/*
 * Autopsy Forensic Browser
 *
 * Copyright 2018 Basis Technology Corp.
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
package org.sleuthkit.autopsy.commonfilesearch;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.ExecutionException;
import java.util.logging.Level;
import javax.swing.AbstractListModel;
import javax.swing.ComboBoxModel;
import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;
import javax.swing.event.ListDataListener;
import org.openide.util.NbBundle;
import org.sleuthkit.autopsy.casemodule.Case;
import org.sleuthkit.autopsy.casemodule.NoCurrentCaseException;
import org.sleuthkit.autopsy.corecomponents.DataResultTopComponent;
import org.sleuthkit.autopsy.corecomponents.TableFilterNode;
import org.sleuthkit.autopsy.coreutils.Logger;
import org.sleuthkit.autopsy.coreutils.MessageNotifyUtil;
import org.sleuthkit.autopsy.directorytree.DataResultFilterNode;
import org.sleuthkit.autopsy.directorytree.DirectoryTreeTopComponent;
import org.sleuthkit.datamodel.SleuthkitCase;
import org.sleuthkit.datamodel.SleuthkitCase.CaseDbQuery;
import org.sleuthkit.datamodel.TskCoreException;

/**
 * Panel used for common files search configuration and configuration business
 * logic. Nested within CommonFilesDialog.
 */
public final class CommonFilesPanel extends javax.swing.JPanel {

    private static final long serialVersionUID = 1L;

    private ComboBoxModel<String> dataSourcesList = new DataSourceComboBoxModel();
    private Map<Long, String> dataSourceMap;

    private static final Logger LOGGER = Logger.getLogger(CommonFilesPanel.class.getName());
    private boolean singleDataSource = false;
    private String selectedDataSource = "";

    /**
     * Creates new form CommonFilesPanel
     */
    @NbBundle.Messages({
        "CommonFilesPanel.title=Common Files Panel",
        "CommonFilesPanel.exception=Unexpected Exception loading DataSources."})
    public CommonFilesPanel() {
        initComponents();

        setupDataSources();
    }

    /**
     * Sets up the data sources dropdown and returns the data sources map for
     * future usage.
     *
     * @return a mapping of data source ids to data source names
     */
    @NbBundle.Messages({
        "CommonFilesPanel.buildDataSourceMap.done.tskCoreException=Unable to run query against DB.",
        "CommonFilesPanel.buildDataSourceMap.done.noCurrentCaseException=Unable to open case file.",
        "CommonFilesPanel.buildDataSourceMap.done.exception=Unexpected exception building data sources map.",
        "CommonFilesPanel.buildDataSourceMap.done.interupted=Something went wrong building the Common Files Search dialog box.",
        "CommonFilesPanel.buildDataSourceMap.done.sqlException=Unable to query db for data sources."})
    private void setupDataSources() {

        new SwingWorker<Map<Long, String>, Void>() {

            private static final String SELECT_DATA_SOURCES = "select obj_id, name from tsk_files where obj_id in (SELECT obj_id FROM tsk_objects WHERE obj_id in (select obj_id from data_source_info))";

            private void updateUi() {

                String[] dataSourcesNames = new String[CommonFilesPanel.this.dataSourceMap.size()];
                dataSourcesNames = CommonFilesPanel.this.dataSourceMap.values().toArray(dataSourcesNames);
                CommonFilesPanel.this.dataSourcesList = new DataSourceComboBoxModel(dataSourcesNames);
                CommonFilesPanel.this.selectDataSourceComboBox.setModel(CommonFilesPanel.this.dataSourcesList);

                boolean multipleDataSources = this.caseHasMultipleSources();
                CommonFilesPanel.this.allDataSourcesRadioButton.setEnabled(multipleDataSources);
                CommonFilesPanel.this.allDataSourcesRadioButton.setSelected(multipleDataSources);

                if (!multipleDataSources) {
                    CommonFilesPanel.this.withinDataSourceRadioButton.setSelected(true);
                    withinDataSourceSelected(true);
                }

                CommonFilesPanel.this.searchButton.setEnabled(true);
            }

            private boolean caseHasMultipleSources() {
                return CommonFilesPanel.this.dataSourceMap.size() >= 2;
            }

            @Override
            protected Map<Long, String> doInBackground() throws NoCurrentCaseException, TskCoreException, SQLException {

                Map<Long, String> dataSouceMap = new HashMap<>();

                Case currentCase = Case.getOpenCase();
                SleuthkitCase tskDb = currentCase.getSleuthkitCase();

                //try block releases resources - exceptions are handled in done()
                try (CaseDbQuery query = tskDb.executeQuery(SELECT_DATA_SOURCES)) {
                    ResultSet resultSet = query.getResultSet();
                    while (resultSet.next()) {
                        Long objectId = resultSet.getLong(1);
                        String dataSourceName = resultSet.getString(2);
                        dataSouceMap.put(objectId, dataSourceName);
                    }
                }

                return dataSouceMap;
            }

            @Override
            protected void done() {

                try {
                    CommonFilesPanel.this.dataSourceMap = this.get();

                    updateUi();

                } catch (InterruptedException ex) {
                    LOGGER.log(Level.SEVERE, "Interrupted while building Common Files Search dialog.", ex);
                    MessageNotifyUtil.Message.error(Bundle.CommonFilesPanel_buildDataSourceMap_done_interupted());
                } catch (ExecutionException ex) {
                    String errorMessage;
                    Throwable inner = ex.getCause();
                    if (inner instanceof TskCoreException) {
                        LOGGER.log(Level.SEVERE, "Failed to load data sources from database.", ex);
                        errorMessage = Bundle.CommonFilesPanel_buildDataSourceMap_done_tskCoreException();
                    } else if (inner instanceof NoCurrentCaseException) {
                        LOGGER.log(Level.SEVERE, "Current case has been closed.", ex);
                        errorMessage = Bundle.CommonFilesPanel_buildDataSourceMap_done_noCurrentCaseException();
                    } else if (inner instanceof SQLException) {
                        LOGGER.log(Level.SEVERE, "Unable to query db for data sources.", ex);
                        errorMessage = Bundle.CommonFilesPanel_buildDataSourceMap_done_sqlException();
                    } else {
                        LOGGER.log(Level.SEVERE, "Unexpected exception while building Common Files Search dialog panel.", ex);
                        errorMessage = Bundle.CommonFilesPanel_buildDataSourceMap_done_exception();
                    }
                    MessageNotifyUtil.Message.error(errorMessage);
                }
            }
        }.execute();
    }

    @NbBundle.Messages({
        "CommonFilesPanel.search.results.title=Common Files",
        "CommonFilesPanel.search.results.pathText=Common Files Search Results",
        "CommonFilesPanel.search.done.tskCoreException=Unable to run query against DB.",
        "CommonFilesPanel.search.done.noCurrentCaseException=Unable to open case file.",
        "CommonFilesPanel.search.done.exception=Unexpected exception running Common Files Search.",
        "CommonFilesPanel.search.done.interupted=Something went wrong finding common files.",
        "CommonFilesPanel.search.done.sqlException=Unable to query db for files or data sources."})
    private void search() {

        String title = Bundle.CommonFilesPanel_search_results_title();
        String pathText = Bundle.CommonFilesPanel_search_results_pathText();

        new SwingWorker<List<CommonFilesMetaData>, Void>() {

            private Long determineDataSourceId() {
                Long selectedObjId = 0L;
                if (CommonFilesPanel.this.singleDataSource) {
                    for (Entry<Long, String> dataSource : CommonFilesPanel.this.dataSourceMap.entrySet()) {
                        if (dataSource.getValue().equals(CommonFilesPanel.this.selectedDataSource)) {
                            selectedObjId = dataSource.getKey();
                            break;
                        }
                    }
                }
                return selectedObjId;
            }

            @Override
            protected List<CommonFilesMetaData> doInBackground() throws TskCoreException, NoCurrentCaseException, SQLException {
                Long selectedObjId = determineDataSourceId();
                return new CommonFilesMetaDataBuilder(selectedObjId, CommonFilesPanel.this.dataSourceMap).collateFiles();
            }

            @Override
            protected void done() {
                try {
                    super.done();

                    List<CommonFilesMetaData> metadata = get();

                    DataResultTopComponent component = DataResultTopComponent.createInstance(title);

                    CommonFilesSearchNode commonFilesNode = new CommonFilesSearchNode(metadata);

                    //TODO consider getting em from ExplorerManager.find(this) rather the this wonky stuff seen here...
                    DataResultFilterNode dataResultFilterNode = new DataResultFilterNode(commonFilesNode, DirectoryTreeTopComponent.getDefault().getExplorerManager());

                    TableFilterNode tableFilterWithDescendantsNode = new TableFilterNode(dataResultFilterNode);

                    int totalNodes = 0;
                    for (CommonFilesMetaData meta : metadata) {
                        totalNodes += meta.getChildren().size();
                    }
                    DataResultTopComponent.initInstance(pathText, tableFilterWithDescendantsNode, totalNodes, component);

                } catch (InterruptedException ex) {
                    LOGGER.log(Level.SEVERE, "Interrupted while loading Common Files", ex);
                    MessageNotifyUtil.Message.error(Bundle.CommonFilesPanel_search_done_interupted());
                } catch (ExecutionException ex) {
                    String errorMessage;
                    Throwable inner = ex.getCause();
                    if (inner instanceof TskCoreException) {
                        LOGGER.log(Level.SEVERE, "Failed to load files from database.", ex);
                        errorMessage = Bundle.CommonFilesPanel_search_done_tskCoreException();
                    } else if (inner instanceof NoCurrentCaseException) {
                        LOGGER.log(Level.SEVERE, "Current case has been closed.", ex);
                        errorMessage = Bundle.CommonFilesPanel_search_done_noCurrentCaseException();
                    } else if (inner instanceof SQLException) {
                        LOGGER.log(Level.SEVERE, "Unable to query db for files.", ex);
                        errorMessage = Bundle.CommonFilesPanel_search_done_sqlException();
                    } else {
                        LOGGER.log(Level.SEVERE, "Unexpected exception while running Common Files Search.", ex);
                        errorMessage = Bundle.CommonFilesPanel_search_done_exception();
                    }
                    MessageNotifyUtil.Message.error(errorMessage);
                }
            }
        }.execute();
    }

    private class DataSourceComboBoxModel extends AbstractListModel<String> implements ComboBoxModel<String> {

        private static final long serialVersionUID = 1L;
        private final String[] dataSourceList;
        String selection = null;

        /**
         * Use this to initialize the panel
         */
        DataSourceComboBoxModel() {
            this.dataSourceList = new String[0];
        }

        /**
         * Use this when we have data to display.
         *
         * @param theDataSoureList names of data sources for user to pick from
         */
        DataSourceComboBoxModel(String[] theDataSoureList) {
            dataSourceList = theDataSoureList;
        }

        @Override
        public void setSelectedItem(Object anItem) {
            selection = (String) anItem;
        }

        @Override
        public Object getSelectedItem() {
            return selection;
        }

        @Override
        public int getSize() {
            return dataSourceList.length;
        }

        @Override
        public String getElementAt(int index) {
            return dataSourceList[index];
        }

        @Override
        public void addListDataListener(ListDataListener l) {
            this.listenerList.add(ListDataListener.class, l);
        }

        @Override
        public void removeListDataListener(ListDataListener l) {
            this.listenerList.remove(ListDataListener.class, l);
        }
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        dataSourcesButtonGroup = new javax.swing.ButtonGroup();
        searchButton = new javax.swing.JButton();
        allDataSourcesRadioButton = new javax.swing.JRadioButton();
        withinDataSourceRadioButton = new javax.swing.JRadioButton();
        selectDataSourceComboBox = new javax.swing.JComboBox<>();

        setPreferredSize(new java.awt.Dimension(300, 300));

        org.openide.awt.Mnemonics.setLocalizedText(searchButton, org.openide.util.NbBundle.getMessage(CommonFilesPanel.class, "CommonFilesPanel.searchButton.text")); // NOI18N
        searchButton.setEnabled(false);
        searchButton.setHorizontalTextPosition(javax.swing.SwingConstants.LEADING);
        searchButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                searchButtonActionPerformed(evt);
            }
        });

        dataSourcesButtonGroup.add(allDataSourcesRadioButton);
        allDataSourcesRadioButton.setSelected(true);
        org.openide.awt.Mnemonics.setLocalizedText(allDataSourcesRadioButton, org.openide.util.NbBundle.getMessage(CommonFilesPanel.class, "CommonFilesPanel.allDataSourcesRadioButton.text")); // NOI18N
        allDataSourcesRadioButton.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
        allDataSourcesRadioButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                allDataSourcesRadioButtonActionPerformed(evt);
            }
        });

        dataSourcesButtonGroup.add(withinDataSourceRadioButton);
        org.openide.awt.Mnemonics.setLocalizedText(withinDataSourceRadioButton, org.openide.util.NbBundle.getMessage(CommonFilesPanel.class, "CommonFilesPanel.withinDataSourceRadioButton.text")); // NOI18N
        withinDataSourceRadioButton.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
        withinDataSourceRadioButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                withinDataSourceRadioButtonActionPerformed(evt);
            }
        });

        selectDataSourceComboBox.setModel(dataSourcesList);
        selectDataSourceComboBox.setEnabled(false);
        selectDataSourceComboBox.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                selectDataSourceComboBoxActionPerformed(evt);
            }
        });

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(selectDataSourceComboBox, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(searchButton)
                    .addComponent(withinDataSourceRadioButton)
                    .addComponent(allDataSourcesRadioButton))
                .addContainerGap(javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(javax.swing.GroupLayout.Alignment.TRAILING, layout.createSequentialGroup()
                .addComponent(allDataSourcesRadioButton)
                .addGap(2, 2, 2)
                .addComponent(withinDataSourceRadioButton, javax.swing.GroupLayout.PREFERRED_SIZE, 41, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(18, 18, 18)
                .addComponent(selectDataSourceComboBox, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 90, Short.MAX_VALUE)
                .addComponent(searchButton)
                .addContainerGap())
        );
    }// </editor-fold>//GEN-END:initComponents

    private void searchButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_searchButtonActionPerformed
        search();
        SwingUtilities.windowForComponent(this).dispose();
    }//GEN-LAST:event_searchButtonActionPerformed

    private void allDataSourcesRadioButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_allDataSourcesRadioButtonActionPerformed
        selectDataSourceComboBox.setEnabled(!allDataSourcesRadioButton.isSelected());
        singleDataSource = false;
    }//GEN-LAST:event_allDataSourcesRadioButtonActionPerformed

    private void selectDataSourceComboBoxActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_selectDataSourceComboBoxActionPerformed
        final Object selectedItem = selectDataSourceComboBox.getSelectedItem();
        if (selectedItem != null) {
            selectedDataSource = selectedItem.toString();
        } else {
            selectedDataSource = "";
        }
    }//GEN-LAST:event_selectDataSourceComboBoxActionPerformed

    private void withinDataSourceRadioButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_withinDataSourceRadioButtonActionPerformed
        withinDataSourceSelected(withinDataSourceRadioButton.isSelected());
    }//GEN-LAST:event_withinDataSourceRadioButtonActionPerformed

    private void withinDataSourceSelected(boolean selected) {
        selectDataSourceComboBox.setEnabled(selected);
        if (selectDataSourceComboBox.isEnabled()) {
            selectDataSourceComboBox.setSelectedIndex(0);
            singleDataSource = true;
        }
    }

    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JRadioButton allDataSourcesRadioButton;
    private javax.swing.ButtonGroup dataSourcesButtonGroup;
    private javax.swing.JButton searchButton;
    private javax.swing.JComboBox<String> selectDataSourceComboBox;
    private javax.swing.JRadioButton withinDataSourceRadioButton;
    // End of variables declaration//GEN-END:variables
}
