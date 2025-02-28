package org.Topicus.Utility.Logs;

import java.io.File;
import java.io.IOException;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

/**
 * This class is used to manage the loggers for the application.
 */
public class LoggerManager {

    /**
     * The list of loggers.
     */
    private static List<Logger> loggers = new ArrayList<>();

    /**
     * The logger for the application.
     */
    public static Logger CONSOLE_LOGGER = Logger.getLogger("org.Topicus.Console");

    /**
     * The logger for the DAO package.
     */
    public static Logger DAO_LOGGER;

    /**
     * The logger for the Model package.
     */
    public static Logger MODEL_LOGGER;

    /**
     * The logger for the Payload package.
     */
    public static Logger PAYLOAD_LOGGER;

    /**
     * The logger for the Resource package.
     */
    public static Logger RESOURCE_LOGGER;

    /**
     * The logger for the Security package.
     */
    public static Logger SECURITY_LOGGER;

    /**
     * The logger for the Service package.
     */
    public static Logger SERVICE_LOGGER;

    /**
     * The logger for the Utility package.
     */
    public static Logger UTILITY_LOGGER;

    /**
     * Method to configure all loggers on startup.
     */
    public static void configureLoggers() {
        CONSOLE_LOGGER = Logger.getLogger("org.Topicus.Console");
        DAO_LOGGER = configureLogger("DAO");
        MODEL_LOGGER = configureLogger("Model");
        PAYLOAD_LOGGER = configureLogger("Payload");
        RESOURCE_LOGGER = configureLogger("Resource");
        SECURITY_LOGGER = configureLogger("Security");
        SERVICE_LOGGER = configureLogger("Service");
        UTILITY_LOGGER = configureLogger("Utility");
    }
    
    /**
     * Method to configure a logger.
     * 
     * @param logger_package The package name of the logger.
     * @return The configured logger.
     */
    private static Logger configureLogger(String logger_package) {
        String logger_name = "org.Topicus." + logger_package;
        Logger logger = Logger.getLogger(logger_name);

        String lowercase_logger_package = logger_package.toLowerCase();
        String date_string = LocalDateTime.now().format(DateTimeFormatter.ofPattern("dd-MM-yyyy_HH-mm-ss"));
        String log_file_name = lowercase_logger_package + "_" + date_string;
        String log_file_path = "../topicus/logs/" + lowercase_logger_package + "/" + log_file_name + ".log";
        FileHandler fileHandler;

        try {
            File file = new File(log_file_path);
            boolean created_dirs = file.getParentFile().mkdirs();

            if (created_dirs) {
                CONSOLE_LOGGER.info("Created directories for logger: " + logger_name);
            }

            fileHandler = new FileHandler(log_file_path, true);
            fileHandler.setLevel(Level.ALL);
            fileHandler.setFormatter(new SimpleFormatter());
        } catch (IOException e) {
            CONSOLE_LOGGER.severe(e.getMessage());
            return Logger.getLogger("org.Topicus." + logger_package);
        }

        logger.addHandler(fileHandler);

        loggers.add(logger);

        return logger;
    }

    /**
     * Method to remove all handlers from the loggers.
     */
    public static void removeHandlers() {
        for (Logger logger : loggers) {
            Handler[] handlers = logger.getHandlers();
            for (Handler handler : handlers) {
                handler.flush();
                handler.close();
            }

            for (Handler handler : handlers) {
                logger.removeHandler(handler);
            }
        }
    }
}
