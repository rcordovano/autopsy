/*
 * Autopsy Forensic Browser
 *
 * Copyright 2020 Basis Technology Corp.
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
package org.sleuthkit.autopsy.datasourcesummary.datamodel;

import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TimeZone;
import org.joda.time.Interval;
import org.sleuthkit.autopsy.datasourcesummary.datamodel.SleuthkitCaseProvider.SleuthkitCaseProviderException;
import org.sleuthkit.autopsy.datasourcesummary.uiutils.DefaultUpdateGovernor;
import org.sleuthkit.autopsy.ingest.IngestManager;
import org.sleuthkit.autopsy.ingest.ModuleContentEvent;
import org.sleuthkit.datamodel.AbstractFile;
import org.sleuthkit.datamodel.DataSource;
import org.sleuthkit.datamodel.TimelineEvent;
import org.sleuthkit.datamodel.TimelineEventType;
import org.sleuthkit.datamodel.TimelineFilter;
import org.sleuthkit.datamodel.TimelineFilter.DataSourcesFilter;
import org.sleuthkit.datamodel.TimelineFilter.RootFilter;
import org.sleuthkit.datamodel.TimelineManager;
import org.sleuthkit.datamodel.TskCoreException;
import java.util.function.Supplier;
import org.sleuthkit.autopsy.core.UserPreferences;

/**
 * Provides data source summary information pertaining to Timeline data.
 */
public class TimelineSummary implements DefaultUpdateGovernor {

    private static final long DAY_SECS = 24 * 60 * 60;
    private static final Set<IngestManager.IngestJobEvent> INGEST_JOB_EVENTS = new HashSet<>(
            Arrays.asList(IngestManager.IngestJobEvent.COMPLETED, IngestManager.IngestJobEvent.CANCELLED));

    private static final Set<TimelineEventType> FILE_SYSTEM_EVENTS
            = new HashSet<>(Arrays.asList(
                    TimelineEventType.FILE_MODIFIED,
                    TimelineEventType.FILE_ACCESSED,
                    TimelineEventType.FILE_CREATED,
                    TimelineEventType.FILE_CHANGED));

    private final SleuthkitCaseProvider caseProvider;
    private final Supplier<TimeZone> timeZoneProvider;

    /**
     * Default constructor.
     */
    public TimelineSummary() {
        this(SleuthkitCaseProvider.DEFAULT, () -> TimeZone.getTimeZone(UserPreferences.getTimeZoneForDisplays()));
    }

    /**
     * Construct object with given SleuthkitCaseProvider
     *
     * @param caseProvider SleuthkitCaseProvider provider, cannot be null.
     * @param timeZoneProvider The timezone provider, cannot be null.
     */
    public TimelineSummary(SleuthkitCaseProvider caseProvider, Supplier<TimeZone> timeZoneProvider) {
        this.caseProvider = caseProvider;
        this.timeZoneProvider = timeZoneProvider;
    }

    @Override
    public boolean isRefreshRequired(ModuleContentEvent evt) {
        return true;
    }

    @Override
    public boolean isRefreshRequired(AbstractFile file) {
        return true;
    }

    @Override
    public boolean isRefreshRequired(IngestManager.IngestJobEvent evt) {
        return (evt != null && INGEST_JOB_EVENTS.contains(evt));
    }

    @Override
    public Set<IngestManager.IngestJobEvent> getIngestJobEventUpdates() {
        return INGEST_JOB_EVENTS;
    }

    /**
     * Retrieves timeline summary data.
     *
     * @param dataSource The data source for which timeline data will be
     * retrieved.
     * @param recentDaysNum The maximum number of most recent days' activity to
     * include.
     * @return The retrieved data.
     * @throws SleuthkitCaseProviderException
     * @throws TskCoreException
     */
    public TimelineSummaryData getData(DataSource dataSource, int recentDaysNum) throws SleuthkitCaseProviderException, TskCoreException {
        TimeZone timeZone = this.timeZoneProvider.get();
        TimelineManager timelineManager = this.caseProvider.get().getTimelineManager();

        // get a mapping of days from epoch to the activity for that day
        Map<Long, DailyActivityAmount> dateCounts = getTimelineEventsByDay(dataSource, timelineManager, timeZone);

        // get minimum and maximum usage date by iterating through 
        Long minDay = null;
        Long maxDay = null;
        for (long daysFromEpoch : dateCounts.keySet()) {
            minDay = (minDay == null) ? daysFromEpoch : Math.min(minDay, daysFromEpoch);
            maxDay = (maxDay == null) ? daysFromEpoch : Math.max(maxDay, daysFromEpoch);
        }

        // if no min date or max date, no usage; return null.
        if (minDay == null || maxDay == null) {
            return null;
        }

        Date minDate = new Date(minDay * 1000 * DAY_SECS);
        Date maxDate = new Date(maxDay * 1000 * DAY_SECS);

        // The minimum recent day will be within recentDaysNum from the maximum day 
        // (+1 since maxDay included) or the minimum day of activity
        long minRecentDay = Math.max(maxDay - recentDaysNum + 1, minDay);

        // get most recent days activity
        List<DailyActivityAmount> mostRecentActivityAmt = getMostRecentActivityAmounts(dateCounts, minRecentDay, maxDay);

        return new TimelineSummaryData(minDate, maxDate, mostRecentActivityAmt);
    }

    /**
     * Given activity by day, converts to most recent days' activity handling
     * empty values.
     *
     * @param dateCounts The day from epoch mapped to activity amounts for that
     * day.
     * @param minRecentDay The minimum recent day in days from epoch.
     * @param maxDay The maximum recent day in days from epoch;
     * @return The most recent daily activity amounts.
     */
    private List<DailyActivityAmount> getMostRecentActivityAmounts(Map<Long, DailyActivityAmount> dateCounts, long minRecentDay, long maxDay) {
        List<DailyActivityAmount> mostRecentActivityAmt = new ArrayList<>();

        for (long curRecentDay = minRecentDay; curRecentDay <= maxDay; curRecentDay++) {
            DailyActivityAmount prevCounts = dateCounts.get(curRecentDay);
            DailyActivityAmount countsHandleNotFound = prevCounts != null
                    ? prevCounts
                    : new DailyActivityAmount(new Date(curRecentDay * DAY_SECS * 1000), 0, 0);

            mostRecentActivityAmt.add(countsHandleNotFound);
        }
        return mostRecentActivityAmt;
    }

    /**
     * Fetches timeline events per day for a particular data source.
     *
     * @param dataSource The data source.
     * @param timelineManager The timeline manager to use while fetching the
     * data.
     * @param timeZone The time zone to use to determine which day activity
     * belongs.
     * @return A Map mapping days from epoch to the activity for that day.
     * @throws TskCoreException
     */
    private Map<Long, DailyActivityAmount> getTimelineEventsByDay(DataSource dataSource, TimelineManager timelineManager, TimeZone timeZone) throws TskCoreException {

        DataSourcesFilter dataSourceFilter = new DataSourcesFilter();
        dataSourceFilter.addSubFilter(new TimelineFilter.DataSourceFilter(dataSource.getName(), dataSource.getId()));

        RootFilter dataSourceRootFilter = new RootFilter(
                null,
                null,
                null,
                null,
                null,
                dataSourceFilter,
                null,
                Collections.emptySet());

        // get events for data source
        long curRunTime = System.currentTimeMillis();
        List<TimelineEvent> events = timelineManager.getEvents(new Interval(1, curRunTime), dataSourceRootFilter);

        // get counts of events per day (left is file system events, right is everything else)
        Map<Long, DailyActivityAmount> dateCounts = new HashMap<>();
        for (TimelineEvent evt : events) {
            long curSecondsFromEpoch = evt.getTime();
            long curDaysFromEpoch = Instant.ofEpochMilli(curSecondsFromEpoch * 1000)
                    .atZone(timeZone.toZoneId())
                    .toLocalDate()
                    .toEpochDay();

            DailyActivityAmount prevAmt = dateCounts.get(curDaysFromEpoch);
            long prevFileEvtCount = prevAmt == null ? 0 : prevAmt.getFileActivityCount();
            long prevArtifactEvtCount = prevAmt == null ? 0 : prevAmt.getArtifactActivityCount();
            Date thisDay = prevAmt == null ? new Date(curDaysFromEpoch * 1000 * DAY_SECS) : prevAmt.getDay();

            boolean isFileEvt = FILE_SYSTEM_EVENTS.contains(evt.getEventType());
            long curFileEvtCount = prevFileEvtCount + (isFileEvt ? 1 : 0);
            long curArtifactEvtCount = prevArtifactEvtCount + (isFileEvt ? 0 : 1);

            dateCounts.put(curDaysFromEpoch, new DailyActivityAmount(thisDay, curFileEvtCount, curArtifactEvtCount));
        }

        return dateCounts;
    }

    /**
     * All the data to be represented in the timeline summary tab.
     */
    public static class TimelineSummaryData {

        private final Date minDate;
        private final Date maxDate;
        private final List<DailyActivityAmount> histogramActivity;

        /**
         * Main constructor.
         *
         * @param minDate Earliest usage date recorded for the data source.
         * @param maxDate Latest usage date recorded for the data source.
         * @param recentDaysActivity A list of activity prior to and including
         * the latest usage date by day.
         */
        TimelineSummaryData(Date minDate, Date maxDate, List<DailyActivityAmount> recentDaysActivity) {
            this.minDate = minDate;
            this.maxDate = maxDate;
            this.histogramActivity = (recentDaysActivity == null) ? Collections.emptyList() : Collections.unmodifiableList(recentDaysActivity);
        }

        /**
         * @return Earliest usage date recorded for the data source.
         */
        public Date getMinDate() {
            return minDate;
        }

        /**
         * @return Latest usage date recorded for the data source.
         */
        public Date getMaxDate() {
            return maxDate;
        }

        /**
         * @return A list of activity prior to and including the latest usage
         * date by day.
         */
        public List<DailyActivityAmount> getMostRecentDaysActivity() {
            return histogramActivity;
        }
    }

    /**
     * Represents the amount of usage based on timeline events for a day.
     */
    public static class DailyActivityAmount {

        private final Date day;
        private final long fileActivityCount;
        private final long artifactActivityCount;

        /**
         * Main constructor.
         *
         * @param day The day for which activity is being measured.
         * @param fileActivityCount The amount of file activity timeline events.
         * @param artifactActivityCount The amount of artifact timeline events.
         */
        DailyActivityAmount(Date day, long fileActivityCount, long artifactActivityCount) {
            this.day = day;
            this.fileActivityCount = fileActivityCount;
            this.artifactActivityCount = artifactActivityCount;
        }

        /**
         * @return The day for which activity is being measured.
         */
        public Date getDay() {
            return day;
        }

        /**
         * @return The amount of file activity timeline events.
         */
        public long getFileActivityCount() {
            return fileActivityCount;
        }

        /**
         * @return The amount of artifact timeline events.
         */
        public long getArtifactActivityCount() {
            return artifactActivityCount;
        }

    }
}
