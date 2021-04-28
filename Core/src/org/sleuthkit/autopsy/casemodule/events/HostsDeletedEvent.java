/*
 * Autopsy Forensic Browser
 *
 * Copyright 2021 Basis Technology Corp.
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
package org.sleuthkit.autopsy.casemodule.events;

import java.util.Collections;
import java.util.List;
import org.sleuthkit.autopsy.casemodule.Case;
import org.sleuthkit.datamodel.Host;
import org.sleuthkit.datamodel.SleuthkitCase;
import org.sleuthkit.datamodel.TskCoreException;

/**
 * Event fired when hosts are deleted.
 */
public class HostsDeletedEvent extends TskDataModelChangedEvent<Host> {

    private static final long serialVersionUID = 1L;

    /**
     * Main constructor.
     *
     * @param dataModelObjectIds The unique numeric IDs (TSK object IDs, case
     *                           database row IDs, etc.) of the Hosts that have
     *                           been deleted.
     */
    public HostsDeletedEvent(List<Long> dataModelObjectIds) {
        super(Case.Events.HOSTS_DELETED.name(), dataModelObjectIds);
    }

    @Override
    protected List<Host> getDataModelObjects(SleuthkitCase caseDb, List<Long> ids) throws TskCoreException {
        return Collections.emptyList();
    }

}
