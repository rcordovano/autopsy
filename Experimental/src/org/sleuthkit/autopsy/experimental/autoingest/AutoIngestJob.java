/*
 * Autopsy Forensic Browser
 *
 * Copyright 2011-2017 Basis Technology Corp.
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
package org.sleuthkit.autopsy.experimental.autoingest;

import java.io.Serializable;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.Instant;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.Objects;
import javax.annotation.concurrent.GuardedBy;
import javax.annotation.concurrent.Immutable;
import javax.annotation.concurrent.ThreadSafe;
import org.sleuthkit.autopsy.corecomponentinterfaces.DataSourceProcessor;
import org.sleuthkit.autopsy.coreutils.NetworkUtils;
import org.sleuthkit.autopsy.ingest.IngestJob;

/**
 * An automated ingest job for a manifest. The manifest specifies a co-located
 * data source and a case to which the data source is to be added.
 */
@ThreadSafe
public final class AutoIngestJob implements Comparable<AutoIngestJob>, Serializable {

    private static final long serialVersionUID = 1L;
    private static final int CURRENT_VERSION = 1;
    private static final int DEFAULT_PRIORITY = 0;
    private static final String LOCAL_HOST_NAME = NetworkUtils.getLocalHostName();
    private final int version;
    private final Manifest manifest;
    private final String nodeName;
    @GuardedBy("this")
    private String caseDirectoryPath;
    @GuardedBy("this")
    private Integer priority;
    @GuardedBy("this")
    private Stage stage;
    @GuardedBy("this")
    private Date stageStartDate;
    @GuardedBy("this")
    private StageDetails stageDetails;
    @GuardedBy("this")
    transient private DataSourceProcessor dataSourceProcessor;
    @GuardedBy("this")
    transient private IngestJob ingestJob;
    @GuardedBy("this")
    transient private boolean cancelled;
    @GuardedBy("this")
    transient private boolean completed;
    @GuardedBy("this")
    private Date completedDate;
    @GuardedBy("this")
    private boolean errorsOccurred;
    @GuardedBy("this")
    private ProcessingStatus processingStatus;
    @GuardedBy("this")
    private int numberOfCrashes;

    /**
     * Constructs a new automated ingest job for a manifest. All job state not
     * specified in the manifest is set to the default state for a new job.
     *
     * @param manifest          The manifest.
     */
    AutoIngestJob(Manifest manifest) {
        this.version = CURRENT_VERSION;
        this.manifest = manifest;
        this.nodeName = AutoIngestJob.LOCAL_HOST_NAME;
        this.caseDirectoryPath = "";
        this.priority = DEFAULT_PRIORITY;
        this.stage = Stage.PENDING;
        this.stageStartDate = manifest.getDateFileCreated();
        this.stageDetails = this.getStageDetails();
        this.dataSourceProcessor = null;
        this.ingestJob = null;
        this.cancelled = false;
        this.completed = false;
        this.completedDate = new Date(0);
        this.errorsOccurred = false;
        this.processingStatus = ProcessingStatus.PENDING;
        this.numberOfCrashes = 0;
    }

    /**
     * Constructs an automated ingest job for a manifest. The manifest specifies
     * a co-located data source and a case to which the data source is to be
     * added.
     *
     * Note: Manifest objects will be phased out and no longer be part of the
     * AutoIngestJob class.
     *
     * @param nodeData The node data.
     */
    AutoIngestJob(AutoIngestJobNodeData nodeData) {
        this.version = nodeData.getVersion();        
        this.manifest = new Manifest(nodeData.getManifestFilePath(), nodeData.getManifestFileDate(), nodeData.getCaseName(), nodeData.getDeviceId(), nodeData.getDataSourcePath(), Collections.emptyMap());
        this.nodeName = nodeData.getProcessingHostName();
        this.caseDirectoryPath = nodeData.getCaseDirectoryPath().toString();
        this.priority = nodeData.getPriority();
        this.stage = nodeData.getProcessingStage();
        this.stageStartDate = nodeData.getProcessingStageStartDate();
        this.stageDetails = this.getStageDetails();
        this.dataSourceProcessor = null;
        this.ingestJob = null;
        this.cancelled = false;
        this.completed = false;
        this.completedDate = nodeData.getCompletedDate();
        this.errorsOccurred = nodeData.getErrorsOccurred();
        this.processingStatus = nodeData.getProcessingStatus();
        this.numberOfCrashes = nodeData.getNumberOfCrashes();
    }

    /**
     * Gets the auto ingest job manifest.
     *
     * @return The manifest.
     */
    Manifest getManifest() {
        return this.manifest;
    }

    /**
     * Sets the path to the case directory of the case associated with this job.
     *
     * @param caseDirectoryPath The path to the case directory.
     */
    synchronized void setCaseDirectoryPath(Path caseDirectoryPath) {
        this.caseDirectoryPath = caseDirectoryPath.toString();
    }

    /**
     * Gets the path to the case directory of the case associated with this job,
     * may be null.
     *
     * @return The case directory path or null if the case directory has not
     *         been created yet.
     */
    synchronized Path getCaseDirectoryPath() {
        if (!caseDirectoryPath.isEmpty()) {
            return Paths.get(caseDirectoryPath);
        } else {
            return null;
        }
    }

    /**
     * Sets the priority of the job. A higher number indicates a higher
     * priority.
     *
     * @param priority The priority.
     */
    synchronized void setPriority(Integer priority) {
        this.priority = priority;
    }

    /**
     * Gets the priority of the job. A higher number indicates a higher
     * priority.
     *
     * @return The priority.
     */
    synchronized Integer getPriority() {
        return this.priority;
    }

    synchronized void setStage(Stage newStage) {
        if (Stage.CANCELLING == this.stage && Stage.COMPLETED != newStage) {
            return;
        }
        this.stage = newStage;
        this.stageStartDate = Date.from(Instant.now());
    }

    synchronized Stage getProcessingStage() {
        return this.stage;
    }

    synchronized Date getProcessingStageStartDate() {
        return new Date(this.stageStartDate.getTime());
    }

    synchronized StageDetails getStageDetails() {
        String description;
        Date startDate;
        if (Stage.CANCELLING != this.stage && null != this.ingestJob) {
            IngestJob.ProgressSnapshot progress = this.ingestJob.getSnapshot();
            IngestJob.DataSourceIngestModuleHandle ingestModuleHandle = progress.runningDataSourceIngestModule();
            if (null != ingestModuleHandle) {
                /**
                 * A first or second stage data source level ingest module is
                 * running. Reporting this takes precedence over reporting
                 * generic file analysis.
                 */
                startDate = ingestModuleHandle.startTime();
                if (!ingestModuleHandle.isCancelled()) {
                    description = ingestModuleHandle.displayName();
                } else {
                    description = String.format(Stage.CANCELLING_MODULE.getDisplayText(), ingestModuleHandle.displayName());
                }
            } else {
                /**
                 * If no data source level ingest module is running, then either
                 * it is still the first stage of analysis and file level ingest
                 * modules are running or another ingest job is still running.
                 * Note that there can be multiple ingest jobs running in
                 * parallel. For example, there is an ingest job created to
                 * ingest each extracted virtual machine.
                 */
                description = Stage.ANALYZING_FILES.getDisplayText();
                startDate = progress.fileIngestStartTime();
            }
        } else {
            description = this.stage.getDisplayText();
            startDate = this.stageStartDate;
        }
        this.stageDetails = new StageDetails(description, startDate);
        return this.stageDetails;
    }

    synchronized void setStageDetails(StageDetails stageDetails) {
        this.stageDetails = stageDetails;
    }
    
    synchronized void setDataSourceProcessor(DataSourceProcessor dataSourceProcessor) {
        this.dataSourceProcessor = dataSourceProcessor;
    }

    synchronized void setIngestJob(IngestJob ingestJob) {
        this.ingestJob = ingestJob;
    }

    synchronized IngestJob getIngestJob() {
        return this.ingestJob;
    }

    synchronized void cancel() {
        setStage(Stage.CANCELLING);
        cancelled = true;
        errorsOccurred = true;
        if (null != dataSourceProcessor) {
            dataSourceProcessor.cancel();
        }
        if (null != ingestJob) {
            ingestJob.cancel(IngestJob.CancellationReason.USER_CANCELLED);
        }
    }

    synchronized boolean isCanceled() {
        return cancelled;
    }

    synchronized void setCompleted() {
        setStage(Stage.COMPLETED);
        completed = true;
    }

    synchronized boolean isCompleted() {
        return completed;
    }

    /**
     * Sets the date the job was completed, with or without cancellation or
     * errors.
     *
     * @param completedDate The completion date.
     */
    synchronized void setCompletedDate(Date completedDate) {
        this.completedDate = new Date(completedDate.getTime());
    }

    /**
     * Gets the date the job was completed, with or without cancellation or
     * errors.
     *
     * @return True or false.
     */
    synchronized Date getCompletedDate() {
        return new Date(completedDate.getTime());
    }

    /**
     * Sets whether or not errors occurred during the processing of the job.
     *
     * @param errorsOccurred True or false;
     */
    synchronized void setErrorsOccurred(boolean errorsOccurred) {
        this.errorsOccurred = errorsOccurred;
    }

    /**
     * Queries whether or not errors occurred during the processing of the job.
     *
     * @return True or false.
     */
    synchronized boolean getErrorsOccurred() {
        return this.errorsOccurred;
    }

    synchronized String getProcessingHostName() {
        return nodeName;
    }

    int getVersion() {
        return this.version;
    }

    synchronized ProcessingStatus getProcessingStatus() {
        return this.processingStatus;
    }

    synchronized void setProcessingStatus(ProcessingStatus processingStatus) {
        this.processingStatus = processingStatus;
    }

    synchronized int getNumberOfCrashes() {
        return this.numberOfCrashes;
    }

    synchronized void setNumberOfCrashes(int numberOfCrashes) {
        this.numberOfCrashes = numberOfCrashes;
    }

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof AutoIngestJob)) {
            return false;
        }
        if (obj == this) {
            return true;
        }
        return this.getManifest().getFilePath().equals(((AutoIngestJob) obj).getManifest().getFilePath());
    }

    @Override
    public int hashCode() {
        int hash = 71 * (Objects.hashCode(this.getManifest().getFilePath()));
        return hash;
    }

    @Override
    public int compareTo(AutoIngestJob o) {
        return -this.getManifest().getDateFileCreated().compareTo(o.getManifest().getDateFileCreated());
    }

    /**
     * Custom comparator that allows us to sort List<AutoIngestJob> on reverse
     * chronological date modified (descending)
     */
    static class ReverseCompletedDateComparator implements Comparator<AutoIngestJob> {

        @Override
        public int compare(AutoIngestJob o1, AutoIngestJob o2) {
            return -o1.getCompletedDate().compareTo(o2.getCompletedDate());
        }

    }

    /**
     * Comparator that sorts auto ingest jobs by priority in descending order.
     */
    public static class PriorityComparator implements Comparator<AutoIngestJob> {

        @Override
        public int compare(AutoIngestJob job, AutoIngestJob anotherJob) {
            return -(job.getPriority().compareTo(anotherJob.getPriority()));
        }

    }

    /**
     * Custom comparator that allows us to sort List<AutoIngestJob> on case name
     * alphabetically except for jobs for the current host, which are placed at
     * the top of the list.
     */
    static class CaseNameAndProcessingHostComparator implements Comparator<AutoIngestJob> {

        @Override
        public int compare(AutoIngestJob o1, AutoIngestJob o2) {
            if (o1.getProcessingHostName().equalsIgnoreCase(LOCAL_HOST_NAME)) {
                return -1; // o1 is for current case, float to top
            } else if (o2.getProcessingHostName().equalsIgnoreCase(LOCAL_HOST_NAME)) {
                return 1; // o2 is for current case, float to top
            } else {
                return o1.getManifest().getCaseName().compareToIgnoreCase(o2.getManifest().getCaseName());
            }
        }

    }

    /**
     * Processing status for the auto ingest job for the manifest.
     */
    enum ProcessingStatus {
        PENDING,
        PROCESSING,
        COMPLETED,
        DELETED
    }

    enum Stage {

        PENDING("Pending"),
        STARTING("Starting"),
        UPDATING_SHARED_CONFIG("Updating shared configuration"),
        CHECKING_SERVICES("Checking services"),
        OPENING_CASE("Opening case"),
        IDENTIFYING_DATA_SOURCE("Identifying data source type"),
        ADDING_DATA_SOURCE("Adding data source"),
        ANALYZING_DATA_SOURCE("Analyzing data source"),
        ANALYZING_FILES("Analyzing files"),
        EXPORTING_FILES("Exporting files"),
        CANCELLING_MODULE("Cancelling module"),
        CANCELLING("Cancelling"),
        COMPLETED("Completed");

        private final String displayText;

        private Stage(String displayText) {
            this.displayText = displayText;
        }

        String getDisplayText() {
            return displayText;
        }

    }

    @Immutable
    static final class StageDetails implements Serializable {

        private static final long serialVersionUID = 1L;
        private final String description;
        private final Date startDate;

        StageDetails(String description, Date startDate) {
            this.description = description;
            this.startDate = startDate;
        }

        String getDescription() {
            return this.description;
        }

        Date getStartDate() {
            return new Date(this.startDate.getTime());
        }

    }

}
