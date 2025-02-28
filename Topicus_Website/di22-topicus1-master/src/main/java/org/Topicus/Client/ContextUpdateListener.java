package org.Topicus.Client;

import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.servlet.ServletContextEvent;
import jakarta.servlet.ServletContextListener;

public class ContextUpdateListener implements ServletContextListener {

    /**
     * This method is used to initialize the context of the Servlet. The purpose of implementing this was to overcome the
     * troublesome error with TomCat's recognition of the Database Driver, where this method essentially forces the server and back-end
     * to locate the correct PostGreSQL jar.
     * @param sce is the ServletContextEvent.
     */
    @Override
    public void contextInitialized(ServletContextEvent sce) {
        LoggerManager.configureLoggers();
        try {
            Class.forName("org.postgresql.Driver");
        } catch (ClassNotFoundException e) {
            LoggerManager.CONSOLE_LOGGER.severe("PostgreSQL driver not found");
        }
    }

    /**
     * This method is to remove the handler associated to the Logger once the server is shut down, to prevent any anomalies from occurring.
     * @param sce of type ServletContextEvent.
     */
    @Override
    public void contextDestroyed(ServletContextEvent sce) {
        LoggerManager.removeHandlers();
    }
}