package org.Topicus.Utility.Builders;

import java.sql.Connection;
import java.util.ArrayList;
import java.util.List;

import org.Topicus.Exceptions.ConnectionConstructionException;
import org.Topicus.Exceptions.ConnectionUnavailableException;
import org.Topicus.Utility.Logs.LoggerManager;

/**
 * This class will bear the implementation of a low-scale connection pool for
 * the application.
 */
public class ConnectionPool {
    // FIELD VARIABLE(S) ------------------------
    private final List<ConnectionPackage> connectionList;

    // CONSTRUCTOR(S) -------------------------------
    public ConnectionPool(int quantity) {
        connectionList = new ArrayList<>();
        for (int i = 0; i < quantity; i++) {
            try {
                ConnectionPackage cPackage = ConnectionPackageBuilder.getInstance().createConnectionPackage();
                connectionList.add(cPackage);
            } catch (ConnectionConstructionException e) {
                LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
            }
        }
    }

    // GETTER(S) ----------------------------------------------------
    public List<ConnectionPackage> getConnectionList() {
        return connectionList;
    }

    // METHOD(S) ---------------------------------------------------

    /**
     * Method that returns the first available connection found from iterating the
     * ConnectionPackages.
     * 
     * @return of type Connection.
     */
    public Connection findAvailableConnection() {
        Connection connection = null;
        try {
            connection = getConnectionList().stream().filter(ConnectionPackage::isAvailable).findFirst().get()
                    .takeConnection();
        } catch (ConnectionUnavailableException e) {
            LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
        }

        if (connection == null) {
            try {
                ConnectionPackage cPackage = ConnectionPackageBuilder.getInstance().createConnectionPackage();
                connection = cPackage.takeConnection();
                // connection = cPackage.getConnection();
            } catch (ConnectionConstructionException | ConnectionUnavailableException e) {
                LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
            }
        }
        
        return connection;
    }
}
