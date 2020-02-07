/*
 * Autopsy Forensic Browser
 *
 * Copyright 2014-2020 Basis Technology Corp.
 * Contact: carrier <at> sleuthkit <dot> org
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.sleuthkit.autopsy.keywordsearch;

import com.google.common.util.concurrent.ThreadFactoryBuilder;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.concurrent.ScheduledThreadPoolExecutor;
import static java.util.concurrent.TimeUnit.MILLISECONDS;
import java.util.concurrent.atomic.AtomicLong;
import java.util.logging.Level;
import javax.annotation.concurrent.GuardedBy;
import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;
import org.netbeans.api.progress.aggregate.AggregateProgressFactory;
import org.netbeans.api.progress.aggregate.AggregateProgressHandle;
import org.netbeans.api.progress.aggregate.ProgressContributor;
import org.openide.util.Cancellable;
import org.openide.util.NbBundle;
import org.openide.util.NbBundle.Messages;
import org.sleuthkit.autopsy.coreutils.Logger;
import org.sleuthkit.autopsy.coreutils.MessageNotifyUtil;
import org.sleuthkit.autopsy.coreutils.StopWatch;
import org.sleuthkit.autopsy.ingest.IngestJobContext;
import org.sleuthkit.autopsy.ingest.IngestMessage;
import org.sleuthkit.autopsy.ingest.IngestServices;

/**
 * Performs periodic commits of the text index and periodic and final keyword
 * searches for ingest jobs.
 */
final class IngestSearchRunner {

    private static final Logger logger = Logger.getLogger(IngestSearchRunner.class.getName());
    private static IngestSearchRunner instance;
    private IngestServices services = IngestServices.getInstance();
    private Ingester ingester;
    private long currentUpdateIntervalMs;
    private volatile boolean periodicSearchTaskRunning;
    private Future<?> periodicSearchTaskFuture;
    private final ScheduledThreadPoolExecutor periodicSearchTaskExecutor;
    private static final int NUM_SEARCH_SCHEDULING_THREADS = 1;
    private static final String SEARCH_SCHEDULER_THREAD_NAME = "periodic-search-scheduler-%d";
    private Map<Long, SearchJobInfo> searchJobsByIngestJob = new ConcurrentHashMap<>();

    /**
     * Constructs an ingest search runner that performs periodic commits of the
     * text index and periodic and final keyword searches for ingest jobs.
     */
    private IngestSearchRunner() {
        currentUpdateIntervalMs = ((long) KeywordSearchSettings.getUpdateFrequency().getTime()) * 60 * 1000;
        ingester = Ingester.getDefault();
        periodicSearchTaskExecutor = new ScheduledThreadPoolExecutor(NUM_SEARCH_SCHEDULING_THREADS, new ThreadFactoryBuilder().setNameFormat(SEARCH_SCHEDULER_THREAD_NAME).build());
    }

    /**
     * Gets the singleton ingest search runner that performs periodic commits of
     * the text index and periodic and final keyword searches for ingest jobs.
     *
     * @return The ingest search runner.
     */
    static synchronized IngestSearchRunner getInstance() {
        if (instance == null) {
            instance = new IngestSearchRunner();
        }
        return instance;
    }

    /**
     * Queues a search job for an ingest job.
     *
     * @param jobContext       The ingest job context for the ingest job.
     * @param keywordListNames The keyword lists to be searched for the ingest
     *                         job.
     */
    synchronized void queueSearchJob(IngestJobContext jobContext, List<String> keywordListNames) {
        /*
         * Add a data structure for keeping track of the search job for an
         * ingest job, if the search job does not already exist. If the search
         * job already exists it is because another keyword search ingest module
         * doing analysis for the same ingest job got here first.
         */
        long ingestJobID = jobContext.getJobId();
        if (searchJobsByIngestJob.containsKey(ingestJobID) == false) {
            SearchJobInfo jobData = new SearchJobInfo(jobContext, keywordListNames);
            searchJobsByIngestJob.put(ingestJobID, jobData);
        }

        /*
         * Keep track of how many keyword search ingest module instances are
         * doing analysis for the same ingest job so that we can know when they
         * have all finished indexing the and the final search for the ingest
         * job can be performed.
         */
        searchJobsByIngestJob.get(ingestJobID).incrementModuleReferenceCount();

        /*
         * Create a background task to do a text index commit and then a search
         * for EVERY ingest job in progress, if one does not already exist.
         * These searches are periodic searches, not final searches.
         */
        if ((searchJobsByIngestJob.size() > 0) && (periodicSearchTaskRunning == false)) {
            currentUpdateIntervalMs = ((long) KeywordSearchSettings.getUpdateFrequency().getTime()) * 60 * 1000;
            periodicSearchTaskFuture = periodicSearchTaskExecutor.schedule(new PeriodicSearchTask(), currentUpdateIntervalMs, MILLISECONDS);
            periodicSearchTaskRunning = true;
        }
    }

    /**
     * Finishes a search job for an ingest job, including performing one last
     * commit of the text index and the final search. Blocks until the final
     * search is complete.
     *
     * @param ingestJobId The ID of the ingest job for which the search job is
     *                    being done.
     */
    synchronized void finishSearchJob(long ingestJobId) {
        /*
         * Make sure the search job has not already been finished.
         */
        SearchJobInfo job;
        job = searchJobsByIngestJob.get(ingestJobId);
        if (job == null) {
            return;
        }

        /*
         * Only do the fnial search if all of the keyword search ingest module
         * instances doing analysis for the same ingest job have all indexing
         * the files for the ingest job.
         */
        boolean readyForFinalSearch = false;
        if (job.decrementModuleReferenceCount() == 0) {
            searchJobsByIngestJob.remove(ingestJobId);
            readyForFinalSearch = true;
        }

        if (readyForFinalSearch) {
            commit();
            doFinalSearch(job); // Blocks until search is completed.

            // new jobs could have been added while we were doing final search
            if (searchJobsByIngestJob.isEmpty()) {
                // no more jobs left. stop the PeriodicSearchTask. 
                // A new one will be created for future jobs. 
                periodicSearchTaskRunning = false;
                periodicSearchTaskFuture.cancel(true);
            }
        }
    }

    /**
     * Cancels the search job for in ingest job. The search job data structure
     * is removed and the final search SwingWorker for the jobm if it exists, is
     * cancelled.
     *
     * @param ingestJobId
     */
    synchronized void cancelSearchJob(long ingestJobId) {
        logger.log(Level.INFO, "Stopping search job {0}", ingestJobId); //NON-NLS
        commit();

        SearchJobInfo job;
        job = searchJobsByIngestJob.get(ingestJobId);
        if (job == null) {
            return;
        }

        //stop currentSearcher
        IngestSearchRunner.Searcher currentSearcher = job.getCurrentSearcher();
        if ((currentSearcher != null) && (!currentSearcher.isDone())) {
            logger.log(Level.INFO, "Cancelling search job {0}", ingestJobId); //NON-NLS
            currentSearcher.cancel(true);
        }

        searchJobsByIngestJob.remove(ingestJobId);

        if (searchJobsByIngestJob.isEmpty()) {
            // no more jobs left. stop the PeriodicSearchTask. 
            // A new one will be created for future jobs. 
            logger.log(Level.INFO, "No more search jobs. Stopping periodic search task"); //NON-NLS
            periodicSearchTaskRunning = false;
            periodicSearchTaskFuture.cancel(true);
        }
    }

    /**
     * Adds one or more keyword lists to the search jobs for all of the ingest
     * jobs that are in progress.
     *
     * @param keywordListNames The names of the keyword lists to add to the
     *                         search jobs for the ingest jobs.
     */
    synchronized void addKeywordListsToAllJobs(List<String> keywordListNames) {
        for (String listName : keywordListNames) {
            for (SearchJobInfo searchJob : searchJobsByIngestJob.values()) {
                searchJob.addKeywordListName(listName);
            }
        }
    }

    /**
     * Commits the text index and fires an event to notify listeners that the
     * number of indexed files has changed because of the commit.
     */
    private void commit() {
        ingester.commit();
        try {
            final int numIndexedFiles = KeywordSearch.getServer().queryNumIndexedFiles();
            KeywordSearch.fireNumIndexedFilesChange(null, numIndexedFiles);
        } catch (NoOpenCoreException | KeywordSearchModuleException ex) {
            logger.log(Level.SEVERE, "Error executing Solr query for number of indexed files", ex); //NON-NLS
        }
    }

    /**
     * A final search waits for any still-running workers, and then executes a
     * new one and waits until that is done.
     *
     * @param job
     */
    private void doFinalSearch(SearchJobInfo job) {
        // Run one last search as there are probably some new files committed
        logger.log(Level.INFO, "Starting final search for ingest job {0}", job.getIngestJobId()); //NON-NLS
        if (!job.getKeywordListNames().isEmpty()) {
            try {
                // In case this job still has a worker running, wait for it to finish
                job.waitForCurrentWorker();

                IngestSearchRunner.Searcher finalSearcher = new IngestSearchRunner.Searcher(job, true);
                job.setCurrentSearcher(finalSearcher); //save the ref
                finalSearcher.execute(); //start thread

                // block until the search is complete
                finalSearcher.get();

            } catch (InterruptedException | CancellationException ex) {
                logger.log(Level.WARNING, "Final search for ingest job {0} interrupted or cancelled", job.getIngestJobId()); //NON-NLS
            } catch (ExecutionException ex) {
                logger.log(Level.SEVERE, String.format("Final search for ingest job %d failed", job.getIngestJobId()), ex); //NON-NLS
            }
        }
    }

    /**
     * Task that commits the text index and then performs a periodic search for
     * EVERY ingest job in progress. The searches are done in another thread,
     * but only one at a time.
     */
    private final class PeriodicSearchTask implements Runnable {

        private final Logger logger = Logger.getLogger(IngestSearchRunner.PeriodicSearchTask.class.getName());

        @Override
        public void run() {
            /*
             * Search jobs for ingest jobs could have been added or removed
             * while this task was waiting for the current interval between
             * periodic searches to elapse. If there are no more search jobs or
             * this task has been cancelled, exit immediately.
             *
             * RC: Calling ConcurrentHashMap.isEmpty is not a reliable way to
             * determine if the map is indeed empty.
             */
            if (searchJobsByIngestJob.isEmpty() || periodicSearchTaskFuture.isCancelled()) {
                periodicSearchTaskRunning = false;
                return;
            }

            /*
             * Commit all of the indexing that the keyword search ingest modules
             * have done since the last periodic search.
             */
            commit();

            /*
             * Do a search for EVERY ingest job in progress. Although this task
             * starts the search for each job in a separate thread, it kicks off
             * the searches one at a time and waits for one search to finish
             * before starting the next one.
             *
             * RC: An Iterator over the contents of a ConcurrentHashMap only
             * iterates over a snapshot of the state of the data structure at
             * some point at or since the creation of the iterator.
             */
            final StopWatch stopWatch = new StopWatch();
            stopWatch.start();
            for (Iterator<Entry<Long, SearchJobInfo>> iterator = searchJobsByIngestJob.entrySet().iterator(); iterator.hasNext();) {
                SearchJobInfo searchJob = iterator.next().getValue();

                /*
                 * RC: I think that we should be checking for an interrupt of
                 * the current thread here.
                 */
                if (periodicSearchTaskFuture.isCancelled()) {
                    logger.log(Level.INFO, "Search has been cancelled. Exiting periodic search task."); //NON-NLS
                    periodicSearchTaskRunning = false;
                    return;
                }

                /*
                 * If there are no keywords to search for, or a search is
                 * already running for this ingest job, skip kicking off a
                 * search task.
                 */
                if (!searchJob.getKeywordListNames().isEmpty() && !searchJob.isWorkerRunning()) {
                    logger.log(Level.INFO, String.format("Starting periodic search for ingest job %d", searchJob.getIngestJobId())); //NON-NLS
                    Searcher searcher = new Searcher(searchJob);
                    searchJob.setCurrentSearcher(searcher);
                    searcher.execute();
                    searchJob.setWorkerRunning(true);
                    try {
                        searcher.get();
                    } catch (InterruptedException | ExecutionException ex) {
                        logger.log(Level.SEVERE, String.format("Error perfoming periodic search for ingest job %d", searchJob.getIngestJobId()), ex); //NON-NLS
                        /*
                         * This resolves to a no-op if not running with a GUI.
                         */
                        services.postMessage(IngestMessage.createErrorMessage(
                                KeywordSearchModuleFactory.getModuleName(),
                                NbBundle.getMessage(this.getClass(), "SearchRunner.Searcher.done.err.msg"),
                                ex.getMessage()));
                    } catch (java.util.concurrent.CancellationException ex) {
                        logger.log(Level.WARNING, String.format("Periodic search for ingest job %d cancelled", searchJob.getIngestJobId()), ex); //NON-NLS
                    }
                    logger.log(Level.INFO, String.format("Finished periodic search for ingest job %d", searchJob.getIngestJobId())); //NON-NLS
                }
            }
            stopWatch.stop();
            logger.log(Level.INFO, "Periodic searches for current inget jobs cumulatively took {0} secs", stopWatch.getElapsedTimeSecs()); //NON-NLS

            /*
             * Adjust the interval between periodic searches based on the time
             * these searches took.
             */
            recalculateUpdateIntervalTime(stopWatch.getElapsedTimeSecs());

            // schedule next PeriodicSearchTask
            periodicSearchTaskFuture = periodicSearchTaskExecutor.schedule(new PeriodicSearchTask(), currentUpdateIntervalMs, MILLISECONDS);
        }

        private void recalculateUpdateIntervalTime(long lastSerchTimeSec) {
            // If periodic search takes more than 1/4 of the current periodic search interval, then double the search interval
            if (lastSerchTimeSec * 1000 < currentUpdateIntervalMs / 4) {
                return;
            }
            // double the search interval
            currentUpdateIntervalMs = currentUpdateIntervalMs * 2;
            logger.log(Level.WARNING, "Last periodic search took {0} sec. Increasing search interval to {1} sec", new Object[]{lastSerchTimeSec, currentUpdateIntervalMs / 1000});
            return;
        }
    }

    /**
     * A data structure to keep track of the keyword lists, interim and final
     * results, and search running status for an ingest job.
     */
    private class SearchJobInfo {

        private final IngestJobContext jobContext;
        private volatile boolean workerRunning;
        @GuardedBy("this")
        private List<String> keywordListNames;
        @GuardedBy("this")
        private Map<Keyword, Set<Long>> currentResults; // Maps keywords to object ids of files with hits.
        @GuardedBy("this")
        private IngestSearchRunner.Searcher currentSearcher;
        private AtomicLong moduleReferenceCount = new AtomicLong(0);
        private final Object finalSearchLock = new Object(); //used for a condition wait

        private SearchJobInfo(IngestJobContext jobContext, List<String> keywordListNames) {
            this.jobContext = jobContext;
            this.keywordListNames = new ArrayList<>(keywordListNames);
            currentResults = new HashMap<>();
            workerRunning = false;
            currentSearcher = null;
        }

        private IngestJobContext getJobContext() {
            return jobContext;
        }

        private long getIngestJobId() {
            return jobContext.getJobId();
        }

        private long getDataSourceId() {
            return jobContext.getDataSource().getId();
        }

        private synchronized List<String> getKeywordListNames() {
            return new ArrayList<>(keywordListNames);
        }

        private synchronized void addKeywordListName(String keywordListName) {
            if (!keywordListNames.contains(keywordListName)) {
                keywordListNames.add(keywordListName);
            }
        }

        private synchronized Set<Long> currentKeywordResults(Keyword k) {
            return currentResults.get(k);
        }

        private synchronized void addKeywordResults(Keyword k, Set<Long> resultsIDs) {
            currentResults.put(k, resultsIDs);
        }

        private boolean isWorkerRunning() {
            return workerRunning;
        }

        private void setWorkerRunning(boolean flag) {
            workerRunning = flag;
        }

        private synchronized IngestSearchRunner.Searcher getCurrentSearcher() {
            return currentSearcher;
        }

        private synchronized void setCurrentSearcher(IngestSearchRunner.Searcher searchRunner) {
            currentSearcher = searchRunner;
        }

        private void incrementModuleReferenceCount() {
            moduleReferenceCount.incrementAndGet();
        }

        private long decrementModuleReferenceCount() {
            return moduleReferenceCount.decrementAndGet();
        }

        /**
         * In case this job still has a worker running, wait for it to finish
         *
         * @throws InterruptedException
         */
        private void waitForCurrentWorker() throws InterruptedException {
            synchronized (finalSearchLock) {
                while (workerRunning) {
                    logger.log(Level.INFO, "Waiting for previous worker to finish"); //NON-NLS
                    finalSearchLock.wait(); //wait() releases the lock
                    logger.log(Level.INFO, "Notified previous worker finished"); //NON-NLS
                }
            }
        }

        /**
         * Unset workerRunning and wake up thread(s) waiting on finalSearchLock
         */
        private void searchNotify() {
            synchronized (finalSearchLock) {
                workerRunning = false;
                finalSearchLock.notify();
            }
        }

    }

    /**
     * A SwingWorker that searches the text index for a given collection of
     * keywords, writes new hits to the blackboard, fires ingest events for the
     * artifacts it creates, and adds messages to the ingest inbox for the user.
     */
    private final class Searcher extends SwingWorker<Object, Void> {

        /**
         * Searcher has private copies/snapshots of the lists and keywords
         */
        private SearchJobInfo job;
        private List<Keyword> keywords; //keywords to search
        private List<String> keywordListNames; // lists currently being searched
        private List<KeywordList> keywordLists;
        private Map<Keyword, KeywordList> keywordToList; //keyword to list name mapping
        private AggregateProgressHandle progressGroup;
        private final Logger logger = Logger.getLogger(IngestSearchRunner.Searcher.class.getName());
        private boolean finalRun = false;

        Searcher(SearchJobInfo job) {
            this.job = job;
            keywordListNames = job.getKeywordListNames();
            keywords = new ArrayList<>();
            keywordToList = new HashMap<>();
            keywordLists = new ArrayList<>();
        }

        Searcher(SearchJobInfo job, boolean finalRun) {
            this(job);
            this.finalRun = finalRun;
        }

        @Override
        @Messages("SearchRunner.query.exception.msg=Error performing query:")
        protected Object doInBackground() throws Exception {
            final String displayName = NbBundle.getMessage(this.getClass(), "KeywordSearchIngestModule.doInBackGround.displayName")
                    + (finalRun ? (" - " + NbBundle.getMessage(this.getClass(), "KeywordSearchIngestModule.doInBackGround.finalizeMsg")) : "");
            final String pgDisplayName = displayName + (" (" + NbBundle.getMessage(this.getClass(), "KeywordSearchIngestModule.doInBackGround.pendingMsg") + ")");
            progressGroup = AggregateProgressFactory.createSystemHandle(pgDisplayName, null, new Cancellable() {
                @Override
                public boolean cancel() {
                    logger.log(Level.INFO, "Cancelling the searcher by user."); //NON-NLS
                    if (progressGroup != null) {
                        progressGroup.setDisplayName(displayName + " " + NbBundle.getMessage(this.getClass(), "SearchRunner.doInBackGround.cancelMsg"));
                    }
                    progressGroup.finish();
                    return IngestSearchRunner.Searcher.this.cancel(true);
                }
            }, null);

            updateKeywords();

            ProgressContributor[] subProgresses = new ProgressContributor[keywords.size()];
            int i = 0;
            for (Keyword keywordQuery : keywords) {
                subProgresses[i] = AggregateProgressFactory.createProgressContributor(keywordQuery.getSearchTerm());
                progressGroup.addContributor(subProgresses[i]);
                i++;
            }

            progressGroup.start();

            final StopWatch stopWatch = new StopWatch();
            stopWatch.start();
            try {
                progressGroup.setDisplayName(displayName);

                int keywordsSearched = 0;

                for (Keyword keyword : keywords) {
                    if (this.isCancelled() || this.job.getJobContext().fileIngestIsCancelled()) {
                        logger.log(Level.INFO, "Cancel detected, bailing before new keyword processed: {0}", keyword.getSearchTerm()); //NON-NLS
                        return null;
                    }

                    final KeywordList keywordList = keywordToList.get(keyword);

                    //new subProgress will be active after the initial query
                    //when we know number of hits to start() with
                    if (keywordsSearched > 0) {
                        subProgresses[keywordsSearched - 1].finish();
                    }

                    KeywordSearchQuery keywordSearchQuery = KeywordSearchUtil.getQueryForKeyword(keyword, keywordList);

                    // Filtering
                    //limit search to currently ingested data sources
                    //set up a filter with 1 or more image ids OR'ed
                    final KeywordQueryFilter dataSourceFilter = new KeywordQueryFilter(KeywordQueryFilter.FilterType.DATA_SOURCE, job.getDataSourceId());
                    keywordSearchQuery.addFilter(dataSourceFilter);

                    QueryResults queryResults;

                    // Do the actual search
                    try {
                        queryResults = keywordSearchQuery.performQuery();
                    } catch (KeywordSearchModuleException | NoOpenCoreException ex) {
                        logger.log(Level.SEVERE, "Error performing query: " + keyword.getSearchTerm(), ex); //NON-NLS
                        MessageNotifyUtil.Notify.error(Bundle.SearchRunner_query_exception_msg() + keyword.getSearchTerm(), ex.getCause().getMessage());
                        //no reason to continue with next query if recovery failed
                        //or wait for recovery to kick in and run again later
                        //likely case has closed and threads are being interrupted
                        return null;
                    } catch (CancellationException e) {
                        logger.log(Level.INFO, "Cancel detected, bailing during keyword query: {0}", keyword.getSearchTerm()); //NON-NLS
                        return null;
                    }

                    // Reduce the results of the query to only those hits we
                    // have not already seen. 
                    QueryResults newResults = filterResults(queryResults);

                    if (!newResults.getKeywords().isEmpty()) {

                        // Write results to BB
                        //scale progress bar more more granular, per result sub-progress, within per keyword
                        int totalUnits = newResults.getKeywords().size();
                        subProgresses[keywordsSearched].start(totalUnits);
                        int unitProgress = 0;
                        String queryDisplayStr = keyword.getSearchTerm();
                        if (queryDisplayStr.length() > 50) {
                            queryDisplayStr = queryDisplayStr.substring(0, 49) + "...";
                        }
                        subProgresses[keywordsSearched].progress(keywordList.getName() + ": " + queryDisplayStr, unitProgress);

                        // Create blackboard artifacts                
                        newResults.process(null, subProgresses[keywordsSearched], this, keywordList.getIngestMessages(), true);

                    } //if has results

                    //reset the status text before it goes away
                    subProgresses[keywordsSearched].progress("");

                    ++keywordsSearched;

                } //for each keyword

            } //end try block
            catch (Exception ex) {
                logger.log(Level.WARNING, "searcher exception occurred", ex); //NON-NLS
            } finally {
                try {
                    finalizeSearcher();
                    stopWatch.stop();
                    logger.log(Level.INFO, "Searcher took {0} secs to run (final = {1})", new Object[]{stopWatch.getElapsedTimeSecs(), this.finalRun}); //NON-NLS
                } finally {
                    // In case a thread is waiting on this worker to be done
                    job.searchNotify();
                }
            }

            return null;
        }

        /**
         * Sync-up the updated keywords from the currently used lists in the XML
         */
        private void updateKeywords() {
            XmlKeywordSearchList loader = XmlKeywordSearchList.getCurrent();

            keywords.clear();
            keywordToList.clear();
            keywordLists.clear();

            for (String name : keywordListNames) {
                KeywordList list = loader.getList(name);
                keywordLists.add(list);
                for (Keyword k : list.getKeywords()) {
                    keywords.add(k);
                    keywordToList.put(k, list);
                }
            }
        }

        /**
         * Performs the cleanup that needs to be done right AFTER
         * doInBackground() returns without relying on done() method that is not
         * guaranteed to run.
         */
        private void finalizeSearcher() {
            SwingUtilities.invokeLater(new Runnable() {
                @Override
                public void run() {
                    progressGroup.finish();
                }
            });
        }

        /**
         * This method filters out all of the hits found in earlier periodic
         * searches and returns only the results found by the most recent
         * search.
         *
         * This method will only return hits for objects for which we haven't
         * previously seen a hit for the keyword.
         *
         * @param queryResult The results returned by a keyword search.
         *
         * @return A unique set of hits found by the most recent search for
         *         objects that have not previously had a hit. The hits will be
         *         for the lowest numbered chunk associated with the object.
         *
         */
        private QueryResults filterResults(QueryResults queryResult) {

            // Create a new (empty) QueryResults object to hold the most recently
            // found hits.
            QueryResults newResults = new QueryResults(queryResult.getQuery());

            // For each keyword represented in the results.
            for (Keyword keyword : queryResult.getKeywords()) {
                // These are all of the hits across all objects for the most recent search.
                // This may well include duplicates of hits we've seen in earlier periodic searches.
                List<KeywordHit> queryTermResults = queryResult.getResults(keyword);

                // Sort the hits for this keyword so that we are always 
                // guaranteed to return the hit for the lowest chunk.
                Collections.sort(queryTermResults);

                // This will be used to build up the hits we haven't seen before
                // for this keyword.
                List<KeywordHit> newUniqueHits = new ArrayList<>();

                // Get the set of object ids seen in the past by this searcher
                // for the given keyword.
                Set<Long> curTermResults = job.currentKeywordResults(keyword);
                if (curTermResults == null) {
                    // We create a new empty set if we haven't seen results for
                    // this keyword before.
                    curTermResults = new HashSet<>();
                }

                // For each hit for this keyword.
                for (KeywordHit hit : queryTermResults) {
                    if (curTermResults.contains(hit.getSolrObjectId())) {
                        // Skip the hit if we've already seen a hit for
                        // this keyword in the object.
                        continue;
                    }

                    // We haven't seen the hit before so add it to list of new
                    // unique hits.
                    newUniqueHits.add(hit);

                    // Add the object id to the results we've seen for this
                    // keyword.
                    curTermResults.add(hit.getSolrObjectId());
                }

                // Update the job with the list of objects for which we have
                // seen hits for the current keyword.
                job.addKeywordResults(keyword, curTermResults);

                // Add the new hits for the current keyword into the results
                // to be returned.
                newResults.addResult(keyword, newUniqueHits);
            }

            return newResults;
        }

    }

}
