/*
 * Autopsy Forensic Browser
 *
 * Copyright 2019-2019 Basis Technology Corp.
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
package org.sleuthkit.autopsy.commandlineingest;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import org.sleuthkit.autopsy.coreutils.Logger;
import org.netbeans.api.sendopts.CommandException;
import org.netbeans.spi.sendopts.Env;
import org.netbeans.spi.sendopts.Option;
import org.netbeans.spi.sendopts.OptionProcessor;
import org.openide.util.lookup.ServiceProvider;
import org.sleuthkit.autopsy.featureaccess.FeatureAccessUtils;

/**
 * This class can be used to add command line options to Autopsy
 */
@ServiceProvider(service = OptionProcessor.class)
public class CommandLineOptionProcessor extends OptionProcessor {

    private static final Logger logger = Logger.getLogger(CommandLineOptionProcessor.class.getName());
    private final Option caseNameOption = Option.requiredArgument('n', "caseName");
    private final Option caseTypeOption = Option.requiredArgument('t', "caseType");
    private final Option caseBaseDirOption = Option.requiredArgument('o', "caseBaseDir");
    private final Option createCaseCommandOption = Option.withoutArgument('c', "createCase");
    private final Option dataSourcePathOption = Option.requiredArgument('s', "dataSourcePath");
    private final Option dataSourceObjectIdOption = Option.requiredArgument('i', "dataSourceObjectId");
    private final Option addDataSourceCommandOption = Option.withoutArgument('a', "addDataSource");
    private final Option caseDirOption = Option.requiredArgument('d', "caseDir");
    private final Option runIngestCommandOption = Option.withoutArgument('r', "runIngest");
    private final Option ingestProfileOption = Option.requiredArgument('p', "ingestProfile");
    private final Option listAllDataSourcesCommandOption = Option.withoutArgument('l', "listAllDataSources");
    private final Option generateReportsOption = Option.withoutArgument('g', "generateReports");

    private boolean runFromCommandLine = false;

    private final List<CommandLineCommand> commands = new ArrayList<>();

    final static String CASETYPE_MULTI = "multi";
    final static String CASETYPE_SINGLE = "single";
    
    @Override
    protected Set<Option> getOptions() {
        Set<Option> set = new HashSet<>();
        set.add(createCaseCommandOption);
        set.add(caseNameOption);
        set.add(caseTypeOption);
        set.add(caseBaseDirOption);
        set.add(dataSourcePathOption);
        set.add(addDataSourceCommandOption);
        set.add(dataSourceObjectIdOption);
        set.add(caseDirOption);
        set.add(runIngestCommandOption);
        set.add(ingestProfileOption);
        set.add(listAllDataSourcesCommandOption);
        set.add(generateReportsOption);
        return set;
    }

    @Override
    protected void process(Env env, Map<Option, String[]> values) throws CommandException {
        logger.log(Level.INFO, "Processing Autopsy command line options"); //NON-NLS
        System.out.println("Processing Autopsy command line options");
        runFromCommandLine = false;

        // input arguments must contain at least one command
        if (!(values.containsKey(createCaseCommandOption) || values.containsKey(addDataSourceCommandOption)
                || values.containsKey(runIngestCommandOption) || values.containsKey(listAllDataSourcesCommandOption)
                || values.containsKey(generateReportsOption))) {
            // not running from command line
            logger.log(Level.INFO, "No command line commands passed in as inputs. Not running from command line."); //NON-NLS
            System.err.println("No command line commands passed in as inputs. Not running from command line.");
            return;
        }

        // parse input parameters
        String[] argDirs;
        String inputCaseName = "";
        if (values.containsKey(caseNameOption)) {
            argDirs = values.get(caseNameOption);
            if (argDirs.length < 1) {
                logger.log(Level.SEVERE, "Missing argument 'caseName'");
                System.err.println("Missing argument 'caseName'");
                return;
            }
            inputCaseName = argDirs[0];

            if (inputCaseName == null || inputCaseName.isEmpty()) {
                logger.log(Level.SEVERE, "'caseName' argument is empty");
                System.err.println("'caseName' argument is empty");
                return;
            }
        }

        
        String caseType = "";
        if (values.containsKey(caseTypeOption)) {
            argDirs = values.get(caseTypeOption);

            if (argDirs.length < 1) {
                logger.log(Level.SEVERE, "Missing argument 'caseType'");
                System.err.println("Missing argument 'caseType'");
                return;
            }
            caseType = argDirs[0];

            if (caseType == null || caseType.isEmpty()) {
                logger.log(Level.SEVERE, "'caseType' argument is empty");
                System.err.println("'caseType' argument is empty");
                return;
            }

            if (!caseType.equalsIgnoreCase(CASETYPE_MULTI) && !caseType.equalsIgnoreCase(CASETYPE_SINGLE)) {
                logger.log(Level.SEVERE, "'caseType' argument is invalid");
                System.err.println("'caseType' argument is invalid");
                return;                
            }
            
            if (caseType.equalsIgnoreCase(CASETYPE_MULTI) && !FeatureAccessUtils.canCreateMultiUserCases()) {
                logger.log(Level.SEVERE, "Unable to create multi user case.");
                System.err.println("Unable to create multi user case. Confirm that multi user settings are configured correctly.");
                return;                                
            }
        }
        
        String caseBaseDir = "";
        if (values.containsKey(caseBaseDirOption)) {
            argDirs = values.get(caseBaseDirOption);
            if (argDirs.length < 1) {
                logger.log(Level.SEVERE, "Missing argument 'caseBaseDir'");
                System.err.println("Missing argument 'caseBaseDir'");
                return;
            }
            caseBaseDir = argDirs[0];

            if (caseBaseDir == null || caseBaseDir.isEmpty()) {
                logger.log(Level.SEVERE, "Missing argument 'caseBaseDir'");
                System.err.println("Missing argument 'caseBaseDir'");
                return;
            }

            if (!(new File(caseBaseDir).exists()) || !(new File(caseBaseDir).isDirectory())) {
                logger.log(Level.SEVERE, "''caseBaseDir'' {0} directory doesn''t exist or is not a directory", caseBaseDir);
                System.err.println("'caseBaseDir' directory doesn't exist or is not a directory: " + caseBaseDir);
                return;
            }
        }

        String dataSourcePath = "";
        if (values.containsKey(dataSourcePathOption)) {

            argDirs = values.get(dataSourcePathOption);
            if (argDirs.length < 1) {
                logger.log(Level.SEVERE, "Missing argument 'dataSourcePath'");
                System.err.println("Missing argument 'dataSourcePath'");
                return;
            }
            dataSourcePath = argDirs[0];

            // verify inputs
            if (dataSourcePath == null || dataSourcePath.isEmpty()) {
                logger.log(Level.SEVERE, "Missing argument 'dataSourcePath'");
                System.err.println("Missing argument 'dataSourcePath'");
                return;
            }

            if (!(new File(dataSourcePath).exists())) {
                logger.log(Level.SEVERE, "Input data source file {0} doesn''t exist", dataSourcePath);
                System.err.println("Input data source file " + dataSourcePath + " doesn't exist");
                return;
            }
        }

        String dataSourceId = "";
        if (values.containsKey(dataSourceObjectIdOption)) {

            argDirs = values.get(dataSourceObjectIdOption);
            if (argDirs.length < 1) {
                logger.log(Level.SEVERE, "Missing argument 'dataSourceObjectIdOption'");
                System.err.println("Missing argument 'dataSourceObjectIdOption'");
                return;
            }
            dataSourceId = argDirs[0];

            // verify inputs
            if (dataSourceId == null || dataSourceId.isEmpty()) {
                logger.log(Level.SEVERE, "Input data source id is empty");
                System.err.println("Input data source id is empty");
                return;
            }
        }

        String caseDir = "";
        if (values.containsKey(caseDirOption)) {

            argDirs = values.get(caseDirOption);
            if (argDirs.length < 1) {
                logger.log(Level.SEVERE, "Missing argument 'caseDirOption'");
                System.err.println("Missing argument 'caseDirOption'");
                return;
            }
            caseDir = argDirs[0];

            // verify inputs
            if (caseDir == null || caseDir.isEmpty()) {
                logger.log(Level.SEVERE, "Missing argument 'caseDirOption'");
                System.err.println("Missing argument 'caseDirOption'");
                return;
            }

            if (!(new File(caseDir).exists()) || !(new File(caseDir).isDirectory())) {
                logger.log(Level.SEVERE, "Case directory {0} doesn''t exist or is not a directory", caseDir);
                System.err.println("Case directory " + caseDir + " doesn't exist or is not a directory");
                return;
            }
        }

        String ingestProfile = "";
        if (values.containsKey(ingestProfileOption)) {

            argDirs = values.get(ingestProfileOption);
            if (argDirs.length < 1) {
                logger.log(Level.SEVERE, "Missing argument 'ingestProfile'");
                System.err.println("Missing argument 'ingestProfile'");
                return;
            }
            ingestProfile = argDirs[0];

            // verify inputs
            if (ingestProfile == null || ingestProfile.isEmpty()) {
                logger.log(Level.SEVERE, "Missing argument 'ingestProfile'");
                System.err.println("Missing argument 'ingestProfile'");
                return;
            }
        }

        // Create commands in order in which they should be executed:
        // First create the "CREATE_CASE" command, if present
        if (values.containsKey(createCaseCommandOption)) {

            // 'caseName' must always be specified for "CREATE_CASE" command
            if (inputCaseName.isEmpty()) {
                logger.log(Level.SEVERE, "'caseName' argument is empty");
                System.out.println("'caseName' argument is empty");
                runFromCommandLine = false;
                return;
            }

            // 'caseBaseDir' must always be specified for "CREATE_CASE" command
            if (caseBaseDir.isEmpty()) {
                logger.log(Level.SEVERE, "'caseBaseDir' argument is empty");
                System.err.println("'caseBaseDir' argument is empty");
                runFromCommandLine = false;
                return;
            }

            CommandLineCommand newCommand = new CommandLineCommand(CommandLineCommand.CommandType.CREATE_CASE);
            newCommand.addInputValue(CommandLineCommand.InputType.CASE_NAME.name(), inputCaseName);
            newCommand.addInputValue(CommandLineCommand.InputType.CASES_BASE_DIR_PATH.name(), caseBaseDir);
            newCommand.addInputValue(CommandLineCommand.InputType.CASE_TYPE.name(), caseType);
            commands.add(newCommand);
            runFromCommandLine = true;
        }

        // Add ADD_DATA_SOURCE command, if present
        if (values.containsKey(addDataSourceCommandOption)) {

            // 'caseDir' must only be specified if the case is not being created during the current run
            if (!values.containsKey(createCaseCommandOption) && caseDir.isEmpty()) {
                // new case is not being created during this run, so 'caseDir' should have been specified
                logger.log(Level.SEVERE, "'caseDir' argument is empty");
                System.err.println("'caseDir' argument is empty");
                runFromCommandLine = false;
                return;
            }

            // 'dataSourcePath' must always be specified for "ADD_DATA_SOURCE" command
            if (dataSourcePath.isEmpty()) {
                logger.log(Level.SEVERE, "'dataSourcePath' argument is empty");
                System.err.println("'dataSourcePath' argument is empty");
                runFromCommandLine = false;
                return;
            }

            CommandLineCommand newCommand = new CommandLineCommand(CommandLineCommand.CommandType.ADD_DATA_SOURCE);
            newCommand.addInputValue(CommandLineCommand.InputType.CASE_FOLDER_PATH.name(), caseDir);
            newCommand.addInputValue(CommandLineCommand.InputType.DATA_SOURCE_PATH.name(), dataSourcePath);
            commands.add(newCommand);
            runFromCommandLine = true;
        }

        // Add RUN_INGEST command, if present
        if (values.containsKey(runIngestCommandOption)) {

            // 'caseDir' must only be specified if the case is not being created during the current run
            if (!values.containsKey(createCaseCommandOption) && caseDir.isEmpty()) {
                // new case is not being created during this run, so 'caseDir' should have been specified
                logger.log(Level.SEVERE, "'caseDir' argument is empty");
                System.err.println("'caseDir' argument is empty");
                runFromCommandLine = false;
                return;
            }

            // if new data source is being added during this run, then 'dataSourceId' is not specified
            if (!values.containsKey(addDataSourceCommandOption) && dataSourceId.isEmpty()) {
                // data source is not being added during this run, so 'dataSourceId' should have been specified
                logger.log(Level.SEVERE, "'dataSourceId' argument is empty");
                System.err.println("'dataSourceId' argument is empty");
                runFromCommandLine = false;
                return;
            }

            CommandLineCommand newCommand = new CommandLineCommand(CommandLineCommand.CommandType.RUN_INGEST);
            newCommand.addInputValue(CommandLineCommand.InputType.CASE_FOLDER_PATH.name(), caseDir);
            newCommand.addInputValue(CommandLineCommand.InputType.DATA_SOURCE_ID.name(), dataSourceId);
            newCommand.addInputValue(CommandLineCommand.InputType.INGEST_PROFILE_NAME.name(), ingestProfile);
            commands.add(newCommand);
            runFromCommandLine = true;
        }

        // Add "LIST_ALL_DATA_SOURCES" command, if present
        if (values.containsKey(listAllDataSourcesCommandOption)) {

            // 'caseDir' must only be specified if the case is not being created during the current run
            if (!values.containsKey(createCaseCommandOption) && caseDir.isEmpty()) {
                // new case is not being created during this run, so 'caseDir' should have been specified
                logger.log(Level.SEVERE, "'caseDir' argument is empty");
                System.err.println("'caseDir' argument is empty");
                runFromCommandLine = false;
                return;
            }

            CommandLineCommand newCommand = new CommandLineCommand(CommandLineCommand.CommandType.LIST_ALL_DATA_SOURCES);
            newCommand.addInputValue(CommandLineCommand.InputType.CASE_FOLDER_PATH.name(), caseDir);
            commands.add(newCommand);
            runFromCommandLine = true;
        }
        
        // Add "GENERATE_REPORTS" command, if present
        if (values.containsKey(generateReportsOption)) {

            // 'caseDir' must only be specified if the case is not being created during the current run
            if (!values.containsKey(createCaseCommandOption) && caseDir.isEmpty()) {
                // new case is not being created during this run, so 'caseDir' should have been specified
                logger.log(Level.SEVERE, "'caseDir' argument is empty");
                System.err.println("'caseDir' argument is empty");
                runFromCommandLine = false;
                return;
            }

            CommandLineCommand newCommand = new CommandLineCommand(CommandLineCommand.CommandType.GENERATE_REPORTS);
            newCommand.addInputValue(CommandLineCommand.InputType.CASE_FOLDER_PATH.name(), caseDir);
            commands.add(newCommand);
            runFromCommandLine = true;
        }        
    }

    /**
     * Returns whether Autopsy should be running in command line mode or not.
     *
     * @return true if running in command line mode, false otherwise.
     */
    public boolean isRunFromCommandLine() {
        return runFromCommandLine;
    }

    /**
     * Returns list of all commands passed in via command line.
     *
     * @return list of input commands
     */
    List<CommandLineCommand> getCommands() {
        return commands;
    }
}
