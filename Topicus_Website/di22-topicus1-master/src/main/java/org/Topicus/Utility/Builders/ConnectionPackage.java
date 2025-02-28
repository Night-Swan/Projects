package org.Topicus.Utility.Builders;

import org.Topicus.Exceptions.ConnectionUnavailableException;

import java.sql.Connection;

/**
 * This class represents a usable connection, which has an added layer of access regulation.
 */
public class ConnectionPackage {
    // FIELD VARIABLE(S) ------------------------------------------------
    private final Connection connection;
    private boolean isAvailable;

    // CONSTRUCTOR(S) -----------------------------------------------------
    /**
     * Constructor to be used when created by the ConnectionBuilder.
     * @param connection of type Connection, representing a usable connection to the database.
     */
    public ConnectionPackage(Connection connection) {
        this.connection = connection;
        this.isAvailable = true;
    }

    // GETTER(S) ------------------------------------------------------------
    /**
     * Synchronized getter as iteration will be done over contents of ConnectionPool, and to ensure that multiple requests
     * are not provided the same connection, access will be regulated.
     * @return of type Connection, representing the connection.
     */
    private synchronized Connection getConnection() {
        return this.connection;
    }

    /**
     * Synchronized to ensure that only one request is able to essentially act upon the dedicated task when a free connection
     * is found.
     * @return of type boolean, representing connection status.
     */
    public synchronized boolean isAvailable() {
        return this.isAvailable;
    }

    // METHOD(S) -----------------------------------------------------------------

    /**
     * Method checks the availability of the current connection; if available, takes the connection, otherwise, returns NULL.
     * @return of type Connection, representing a valid, usable connection.
     */
    public synchronized Connection takeConnection() throws ConnectionUnavailableException {
        if (!isAvailable()) {
            throw new ConnectionUnavailableException("Unavailable");
        }
        this.isAvailable = false;
        return getConnection();
    }

    /**
     * Method to reset the status of the connection.
     */
    public synchronized void resetConnection() {
        this.isAvailable = true;
    }
}
