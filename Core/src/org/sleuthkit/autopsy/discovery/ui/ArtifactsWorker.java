/*
 * Autopsy
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
package org.sleuthkit.autopsy.discovery.ui;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;
import java.util.logging.Level;
import javax.swing.SwingWorker;
import org.apache.commons.lang3.StringUtils;
import org.sleuthkit.autopsy.casemodule.Case;
import org.sleuthkit.autopsy.coreutils.Logger;
import org.sleuthkit.autopsy.discovery.search.DiscoveryEventUtils;
import org.sleuthkit.autopsy.discovery.search.DiscoveryException;
import org.sleuthkit.autopsy.discovery.search.DomainSearch;
import org.sleuthkit.autopsy.discovery.search.DomainSearchArtifactsRequest;
import org.sleuthkit.datamodel.BlackboardArtifact;

/**
 * SwingWorker to retrieve a list of artifacts for a specified type and domain.
 */
class ArtifactsWorker extends SwingWorker<List<BlackboardArtifact>, Void> {

    private final BlackboardArtifact.ARTIFACT_TYPE artifactType;
    private final static Logger logger = Logger.getLogger(ArtifactsWorker.class.getName());
    private final String domain;
    private final boolean grabFocus;

    /**
     * Construct a new ArtifactsWorker.
     *
     * @param artifactType    The type of artifact being retrieved.
     * @param domain          The domain the artifacts should have as an
     *                        attribute.
     * @param shouldGrabFocus True if the list of artifacts should have focus,
     *                        false otherwise.
     */
    ArtifactsWorker(BlackboardArtifact.ARTIFACT_TYPE artifactType, String domain, boolean shouldGrabFocus) {
        this.artifactType = artifactType;
        this.domain = domain;
        this.grabFocus = shouldGrabFocus;
    }

    @Override
    protected List<BlackboardArtifact> doInBackground() throws Exception {
        if (artifactType != null && !StringUtils.isBlank(domain)) {
            DomainSearch domainSearch = new DomainSearch();
            try {
                return domainSearch.getArtifacts(new DomainSearchArtifactsRequest(Case.getCurrentCase().getSleuthkitCase(), domain, artifactType));
            } catch (DiscoveryException ex) {
                if (ex.getCause() instanceof InterruptedException) {
                    this.cancel(true);
                    //ignore the exception as it was cancelled while the cache was performing its get and we support cancellation
                } else {
                    throw ex;
                }
            }
        }
        return new ArrayList<>();
    }

    @Override
    protected void done() {
        List<BlackboardArtifact> listOfArtifacts = new ArrayList<>();
        if (!isCancelled()) {
            try {
                listOfArtifacts.addAll(get());
                DiscoveryEventUtils.getDiscoveryEventBus().post(new DiscoveryEventUtils.ArtifactSearchResultEvent(artifactType, listOfArtifacts, grabFocus));
            } catch (InterruptedException | ExecutionException ex) {
                logger.log(Level.SEVERE, "Exception while trying to get list of artifacts for Domain details for artifact type: "
                        + artifactType.getDisplayName() + " and domain: " + domain, ex);
            } catch (CancellationException ignored) {
                //Worker was cancelled after previously finishing its background work, exception ignored to cut down on non-helpful logging
            }
        }

    }
}
