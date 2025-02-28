package org.Topicus.Utility.Builders;

import java.io.FileReader;
import java.io.IOException;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.Properties;

import org.Topicus.Exceptions.ConnectionConstructionException;
import org.Topicus.Utility.Logs.LoggerManager;

/**
 * Singleton ConnectionBuilder Tool: Will Later Have a ConnectionPool object
 * which it manages a fixed set of connections between User Requests for the
 * Database.
 * Ask if the implementation of a ConnectionPool is required for Topicus, and if
 * it is taught in the course or not.
 */
public class ConnectionPackageBuilder {
    // FIELD VARIABLE(S) ----------------------------
    private static ConnectionPackageBuilder instance = null;

    // DATABASE ACCESS CONSTANTS -------------------------------

    private static final String URL = "jdbc:postgresql://";
    private static final String HOST = "bronto.ewi.utwente.nl";
    public static final String DB_NAME = getDBName();
    private static final int PORT = 5432;
    public static final String DB_SCHEMA = "?currentSchema=" + getDBSchema();
    public static final String CONNECTION_STRING = URL + HOST + ":" + PORT + "/" + DB_NAME + DB_SCHEMA;
    private static final String PROPERTIES_PATH = "../topicus/application.properties";

    public static final String USERNAME = getDBUsername();

    public static final String PASSWORD = getDBPassword();

    // CONSTRUCTOR(S) ----------------------------------------
    private ConnectionPackageBuilder() {

    }

    /**
     * Returning the instance that can be used.
     * 
     * @return of type ConnectionBuilder.
     */
    public static ConnectionPackageBuilder getInstance() {
        if (instance == null) {
            instance = new ConnectionPackageBuilder();
        }
        return instance;
    }

    public static Properties getProperties() {
        Properties properties = new Properties();
        try (FileReader reader = new FileReader(PROPERTIES_PATH)) {
            properties.load(reader);

            return properties;
        } catch (IOException e) {
            LoggerManager.UTILITY_LOGGER.severe("no properties file found");
            return null;
        }
    }

    /**
     * Method for getting the database username.
     * 
     * @return of type String.
     */
    public static String getDBUsername() {
        Properties properties = getProperties();

        if (properties == null) {
            LoggerManager.UTILITY_LOGGER.severe("cannot get db username");
            return null;
        }

        String db_username = properties.getProperty("db.username");

        if (db_username == null) {
            LoggerManager.UTILITY_LOGGER.severe("property db.username not found");
            return null;
        }

        return db_username;
    }

    /**
     * Method for getting the database password.
     * 
     * @return of type String.
     */
    public static String getDBPassword() {
        Properties properties = getProperties();

        if (properties == null) {
            LoggerManager.UTILITY_LOGGER.severe("cannot get db password");
            return null;
        }

        String db_password = properties.getProperty("db.password");

        if (db_password == null) {
            LoggerManager.UTILITY_LOGGER.severe("property db.password not found");
            return null;
        }

        return db_password;
    }

    /**
     * Method for getting the database name.
     * 
     * @return of type String.
     */
    public static String getDBName() {
        Properties properties = getProperties();

        if (properties == null) {
            LoggerManager.UTILITY_LOGGER.severe("cannot get db name");
            return null;
        }

        String db_name = properties.getProperty("db.name");

        if (db_name == null) {
            LoggerManager.UTILITY_LOGGER.severe("property db.name not found");
            return null;
        }

        return db_name;
    }

    /**
     * Method for getting the database schema.
     * 
     * @return of type String.
     */
    public static String getDBSchema() {
        Properties properties = getProperties();

        if (properties == null) {
            LoggerManager.UTILITY_LOGGER.severe("cannot get db schema");
            return null;
        }

        String db_schema = properties.getProperty("db.schema");

        if (db_schema == null) {
            LoggerManager.UTILITY_LOGGER.severe("property db.schema not found");
            return null;
        }

        return db_schema;
    }

    public static Connection getConnection() throws SQLException {
        try {
            Class.forName("org.postgresql.Driver");
            return DriverManager.getConnection(CONNECTION_STRING, USERNAME, PASSWORD);
        } catch (ClassNotFoundException e) {
            LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for collecting the connection.
     * 
     * @return of type Connection.
     * @throws ConnectionConstructionException representing the failure to create
     *                                         the connection.
     */
    public ConnectionPackage createConnectionPackage() throws ConnectionConstructionException {
        try {
            Connection connection = DriverManager.getConnection(CONNECTION_STRING, USERNAME, PASSWORD);
            return new ConnectionPackage(connection);
        } catch (SQLException e) {
            LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    public Connection createConnection() {
        try {
            return DriverManager.getConnection(CONNECTION_STRING, USERNAME, PASSWORD);
        } catch (SQLException e) {
            LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
            return null;
        }
    }
}
