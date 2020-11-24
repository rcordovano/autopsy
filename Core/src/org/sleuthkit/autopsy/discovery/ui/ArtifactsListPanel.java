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
import java.util.logging.Level;
import javax.swing.JPanel;
import javax.swing.event.ListSelectionListener;
import javax.swing.table.AbstractTableModel;
import org.apache.commons.io.FilenameUtils;
import org.apache.commons.lang.StringUtils;
import org.openide.util.NbBundle;
import org.sleuthkit.autopsy.casemodule.Case;
import org.sleuthkit.autopsy.coreutils.Logger;
import org.sleuthkit.autopsy.coreutils.ThreadConfined;
import org.sleuthkit.datamodel.BlackboardArtifact;
import org.sleuthkit.datamodel.BlackboardAttribute;
import org.sleuthkit.datamodel.TskCoreException;

/**
 * Panel to display list of artifacts for selected domain.
 *
 */
class ArtifactsListPanel extends JPanel {

    private static final long serialVersionUID = 1L;
    private final DomainArtifactTableModel tableModel;
    private static final Logger logger = Logger.getLogger(ArtifactsListPanel.class.getName());

    /**
     * Creates new form ArtifactsListPanel.
     *
     * @param artifactType The type of artifact displayed in this table.
     */
    @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
    ArtifactsListPanel(BlackboardArtifact.ARTIFACT_TYPE artifactType) {
        tableModel = new DomainArtifactTableModel(artifactType);
        initComponents();
        jTable1.getRowSorter().toggleSortOrder(0);
        jTable1.getRowSorter().toggleSortOrder(0);
    }

    /**
     * Add a listener to the table of artifacts to perform actions when an
     * artifact is selected.
     *
     * @param listener The listener to add to the table of artifacts.
     */
    @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
    void addSelectionListener(ListSelectionListener listener) {
        jTable1.getSelectionModel().addListSelectionListener(listener);
    }

    /**
     * Remove a listener from the table of artifacts.
     *
     * @param listener The listener to remove from the table of artifacts.
     */
    @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
    void removeListSelectionListener(ListSelectionListener listener) {
        jTable1.getSelectionModel().removeListSelectionListener(listener);
    }

    /**
     * The artifact which is currently selected, null if no artifact is
     * selected.
     *
     * @return The currently selected BlackboardArtifact or null if none is
     *         selected.
     */
    @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
    BlackboardArtifact getSelectedArtifact() {
        int selectedIndex = jTable1.getSelectionModel().getLeadSelectionIndex();
        if (selectedIndex < jTable1.getSelectionModel().getMinSelectionIndex() || jTable1.getSelectionModel().getMaxSelectionIndex() < 0 || selectedIndex > jTable1.getSelectionModel().getMaxSelectionIndex()) {
            return null;
        }
        return tableModel.getArtifactByRow(jTable1.convertRowIndexToModel(selectedIndex));
    }

    /**
     * Whether the list of artifacts is empty.
     *
     * @return true if the list of artifacts is empty, false if there are
     *         artifacts.
     */
    @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
    boolean isEmpty() {
        return tableModel.getRowCount() <= 0;
    }

    /**
     * Select the first available artifact in the list if it is not empty to
     * populate the panel to the right.
     */
    @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
    void selectFirst() {
        if (!isEmpty()) {
            jTable1.setRowSelectionInterval(0, 0);
        } else {
            jTable1.clearSelection();
        }
    }

    /**
     * Add the specified list of artifacts to the list of artifacts which should
     * be displayed.
     *
     * @param artifactList The list of artifacts to display.
     */
    @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
    void addArtifacts(List<BlackboardArtifact> artifactList) {
        tableModel.setContents(artifactList);
        jTable1.validate();
        jTable1.repaint();
        tableModel.fireTableDataChanged();
    }

    /**
     * Remove all artifacts from the list of artifacts displayed.
     */
    @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
    void clearArtifacts() {
        tableModel.setContents(new ArrayList<>());
        tableModel.fireTableDataChanged();
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        javax.swing.JScrollPane jScrollPane1 = new javax.swing.JScrollPane();
        jTable1 = new javax.swing.JTable();

        setOpaque(false);
        setPreferredSize(new java.awt.Dimension(300, 0));

        jScrollPane1.setBorder(null);
        jScrollPane1.setMinimumSize(new java.awt.Dimension(0, 0));
        jScrollPane1.setPreferredSize(new java.awt.Dimension(0, 0));

        jTable1.setAutoCreateRowSorter(true);
        jTable1.setModel(tableModel);
        jTable1.setSelectionMode(javax.swing.ListSelectionModel.SINGLE_SELECTION);
        jScrollPane1.setViewportView(jTable1);

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(jScrollPane1, javax.swing.GroupLayout.DEFAULT_SIZE, 400, Short.MAX_VALUE)
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addComponent(jScrollPane1, javax.swing.GroupLayout.DEFAULT_SIZE, 607, Short.MAX_VALUE)
        );
    }// </editor-fold>//GEN-END:initComponents

    /**
     * Table model which allows the artifact table in this panel to mimic a list
     * of artifacts.
     */
    private class DomainArtifactTableModel extends AbstractTableModel {

        private static final long serialVersionUID = 1L;
        private final List<BlackboardArtifact> artifactList = new ArrayList<>();
        private final BlackboardArtifact.ARTIFACT_TYPE artifactType;

        /**
         * Construct a new DomainArtifactTableModel.
         *
         * @param artifactType The type of artifact displayed in this table.
         */
        @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
        DomainArtifactTableModel(BlackboardArtifact.ARTIFACT_TYPE artifactType) {
            this.artifactType = artifactType;
        }

        /**
         * Set the list of artifacts which should be represented by this table
         * model.
         *
         * @param artifacts The list of BlackboardArtifacts to represent.
         */
        @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
        void setContents(List<BlackboardArtifact> artifacts) {
            jTable1.clearSelection();
            artifactList.clear();
            artifactList.addAll(artifacts);
        }

        @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
        @Override
        public int getRowCount() {
            return artifactList.size();
        }

        @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
        @Override
        public int getColumnCount() {
            if (artifactType == BlackboardArtifact.ARTIFACT_TYPE.TSK_WEB_CACHE) {
                return 3;
            } else {
                return 2;
            }
        }

        /**
         * Get the BlackboardArtifact at the specified row.
         *
         * @param rowIndex The row the artifact to return is at.
         *
         * @return The BlackboardArtifact at the specified row.
         */
        @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
        BlackboardArtifact getArtifactByRow(int rowIndex) {
            return artifactList.get(rowIndex);
        }

        @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
        @NbBundle.Messages({"ArtifactsListPanel.value.noValue=No value available."})
        @Override
        public Object getValueAt(int rowIndex, int columnIndex) {
            if (columnIndex < 2 || artifactType == BlackboardArtifact.ARTIFACT_TYPE.TSK_WEB_CACHE) {
                try {
                    for (BlackboardAttribute bba : getArtifactByRow(rowIndex).getAttributes()) {
                        if (!StringUtils.isBlank(bba.getDisplayString())) {
                            String stringFromAttribute = getStringForColumn(bba, columnIndex);
                            if (!StringUtils.isBlank(stringFromAttribute)) {
                                return stringFromAttribute;
                            }
                        }
                    }
                    return getFallbackValue(rowIndex, columnIndex);
                } catch (TskCoreException ex) {
                    logger.log(Level.WARNING, "Error getting attributes for artifact " + getArtifactByRow(rowIndex).getArtifactID(), ex);
                }
            }
            return Bundle.ArtifactsListPanel_value_noValue();
        }

        /**
         * Get the appropriate String for the specified column from the
         * BlackboardAttribute.
         *
         * @param bba         The BlackboardAttribute which may contain a value.
         * @param columnIndex The column the value will be displayed in.
         *
         * @return The value from the specified attribute which should be
         *         displayed in the specified column, null if the specified
         *         attribute does not contain a value for that column.
         *
         * @throws TskCoreException When unable to get abstract files based on
         *                          the TSK_PATH_ID.
         */
        @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
        private String getStringForColumn(BlackboardAttribute bba, int columnIndex) throws TskCoreException {
            if (columnIndex == 0 && bba.getAttributeType().getTypeID() == BlackboardAttribute.ATTRIBUTE_TYPE.TSK_DATETIME_ACCESSED.getTypeID()) {
                return bba.getDisplayString();
            } else if (columnIndex == 1) {
                if (artifactType == BlackboardArtifact.ARTIFACT_TYPE.TSK_WEB_DOWNLOAD || artifactType == BlackboardArtifact.ARTIFACT_TYPE.TSK_WEB_CACHE) {
                    if (bba.getAttributeType().getTypeID() == BlackboardAttribute.ATTRIBUTE_TYPE.TSK_PATH_ID.getTypeID()) {
                        return Case.getCurrentCase().getSleuthkitCase().getAbstractFileById(bba.getValueLong()).getName();
                    } else if (bba.getAttributeType().getTypeID() == BlackboardAttribute.ATTRIBUTE_TYPE.TSK_PATH.getTypeID()) {
                        return FilenameUtils.getName(bba.getDisplayString());
                    }
                } else if (bba.getAttributeType().getTypeID() == BlackboardAttribute.ATTRIBUTE_TYPE.TSK_TITLE.getTypeID()) {
                    return bba.getDisplayString();
                }
            } else if (columnIndex == 2 && bba.getAttributeType().getTypeID() == BlackboardAttribute.ATTRIBUTE_TYPE.TSK_PATH_ID.getTypeID()) {
                return Case.getCurrentCase().getSleuthkitCase().getAbstractFileById(bba.getValueLong()).getMIMEType();
            }
            return null;
        }

        /**
         * Private helper method to use when the value we want for either date
         * or title is not available.
         *
         *
         * @param rowIndex    The row the artifact to return is at.
         * @param columnIndex The column index the attribute will be displayed
         *                    at.
         *
         * @return A string that can be used in place of the accessed date time
         *         attribute title when they are not available.
         *
         * @throws TskCoreException
         */
        @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
        private String getFallbackValue(int rowIndex, int columnIndex) throws TskCoreException {
            for (BlackboardAttribute bba : getArtifactByRow(rowIndex).getAttributes()) {
                if (columnIndex == 0 && bba.getAttributeType().getTypeName().startsWith("TSK_DATETIME") && !StringUtils.isBlank(bba.getDisplayString())) {
                    return bba.getDisplayString();
                } else if (columnIndex == 1 && bba.getAttributeType().getTypeID() == BlackboardAttribute.ATTRIBUTE_TYPE.TSK_URL.getTypeID() && !StringUtils.isBlank(bba.getDisplayString())) {
                    return bba.getDisplayString();
                } else if (columnIndex == 1 && bba.getAttributeType().getTypeID() == BlackboardAttribute.ATTRIBUTE_TYPE.TSK_NAME.getTypeID() && !StringUtils.isBlank(bba.getDisplayString())) {
                    return bba.getDisplayString();
                } else if (columnIndex == 1 && bba.getAttributeType().getTypeID() == BlackboardAttribute.ATTRIBUTE_TYPE.TSK_TEXT.getTypeID() && !StringUtils.isBlank(bba.getDisplayString())) {
                    return bba.getDisplayString();
                }
            }
            return Bundle.ArtifactsListPanel_value_noValue();
        }

        @ThreadConfined(type = ThreadConfined.ThreadType.AWT)
        @NbBundle.Messages({"ArtifactsListPanel.titleColumn.name=Title",
            "ArtifactsListPanel.fileNameColumn.name=Name",
            "ArtifactsListPanel.dateColumn.name=Date/Time",
            "ArtifactsListPanel.mimeTypeColumn.name=MIME Type"})
        @Override
        public String getColumnName(int column) {
            switch (column) {
                case 0:
                    return Bundle.ArtifactsListPanel_dateColumn_name();
                case 1:
                    if (artifactType == BlackboardArtifact.ARTIFACT_TYPE.TSK_WEB_CACHE || artifactType == BlackboardArtifact.ARTIFACT_TYPE.TSK_WEB_DOWNLOAD) {
                        return Bundle.ArtifactsListPanel_fileNameColumn_name();
                    } else {
                        return Bundle.ArtifactsListPanel_titleColumn_name();
                    }
                case 2:
                    return Bundle.ArtifactsListPanel_mimeTypeColumn_name();
                default:
                    return "";
            }
        }
    }
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JTable jTable1;
    // End of variables declaration//GEN-END:variables
}
