package org.Topicus.DAO.SystemUserDAO;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.Contract.DAO;
import org.Topicus.Model.SchoolAdmin.SchoolAdmin;
import org.Topicus.Model.SystemUser.SystemUser;
import org.Topicus.Payload.Internal.HashedPasswordContainer;
import org.Topicus.Payload.Response.SchoolAdmin.SchoolAdminDetails;
import org.Topicus.Service.PasswordService;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.DateParser;
import org.Topicus.Utility.Parsers.ListParser;
import org.Topicus.Utility.Parsers.SchoolParser;
import org.Topicus.Utility.Parsers.SystemUserParser;

public enum SystemUserDAO implements DAO<SystemUser>, SchoolParser, ListParser, DateParser {
    instance;

    // CONSTANTS (SQL QUERIES)
    // ---------------------------------------------------------------------------------------
    private static final String GET_SYSTEM_USER_BY_ID = "SELECT account_id, type, username, email, password FROM t_system_user WHERE account_id = ?";
    private static final String GET_SYSTEM_USER_BY_EMAIL = "SELECT account_id, type, username, email, password FROM t_system_user WHERE email = ?";
    private static final String GET_PASSWORD_SALT_BY_ID = "SELECT password_salt FROM t_system_user WHERE account_id = ?";
    private static final String GET_ALL_SYSTEM_USERS = "SELECT * FROM t_system_user";
    private static final String DELETE_SYSTEM_USER = "DELETE FROM t_system_user AS s WHERE s.account_id = ?";
    private static final String CREATE_SYSTEM_USER = "INSERT INTO t_system_user(account_id, type, username, email, password, password_salt) VALUES(?, ?, ?, ?, ?, ?) RETURNING *";
    private static final String UPDATE_SYSTEM_USER = "UPDATE t_system_user SET account_id = ?, type = ?, username = ?, email = ?, password = ?, password_salt = ? WHERE account_id = ? RETURNING *";

    private static final String GET_SCHOOL_ADMIN_BY_ID = "SELECT sa_id, surname, phone_number, date_of_birth, given_names, school_id, employee_id FROM t_school_administrator WHERE sa_id = ?";
    private static final String GET_SCHOOL_ADMIN_DETAILS_BY_ID = "SELECT su.account_id, su.type, su.username, su.email, sa.surname, sa.phone_number, sa.date_of_birth, sa.given_names,sa.school_id, sa.employee_id FROM t_system_user su, t_school_administrator sa WHERE su.account_id = sa.sa_id AND su.type = 'SCHOOL_ADMIN' AND su.account_id = ?";
    private static final String GET_ALL_SCHOOL_ADMINS = "SELECT * FROM t_school_administrator";
    private static final String GET_ALL_SCHOOL_ADMINS_DETAILS = "SELECT su.account_id, su.type, su.username, su.email, sa.surname, sa.phone_number, sa.date_of_birth, sa.given_names,sa.school_id, sa.employee_id FROM t_system_user su, t_school_administrator sa WHERE su.account_id = sa.sa_id AND su.type = 'SCHOOL_ADMIN'";
    private static final String CREATE_SCHOOL_ADMIN = "INSERT INTO t_school_administrator(sa_id, surname, phone_number, date_of_birth, given_names, school_id, employee_id) VALUES (?, ?, ? ,? ,?, ?, ?) RETURNING *";
    private static final String UPDATE_SCHOOL_ADMIN = "UPDATE t_school_administrator SET sa_id = ?, surname = ?, phone_number = ?, date_of_birth = ?, given_names = ?, school_id = ?, employee_id = ? WHERE sa_id = ? RETURNING *";
    private static final String DELETE_SCHOOL_ADMIN = "DELETE FROM t_school_administrator WHERE sa_id = ?";

    // CONSTRUCTOR(S) --------------------------------------
    SystemUserDAO() {

    }

    // ACCESS METHOD(S) ------------------------------------

    /**
     * Method to return enum instance of DAO class.
     * 
     * @return of type SystemUserDAO.
     */
    public static SystemUserDAO getInstance() {
        return instance;
    }

    // METHOD(S) ----------------------------------------------

    /**
     * Returns one specific system user from the database
     * 
     * @param id of type UUID, the id of the system user
     * @return the system user with the given id
     */
    @Override
    public SystemUser get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_SYSTEM_USER_BY_ID)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();
            if (!resultSet.next()) {
                return null;
            }

            SystemUser systemUser = SystemUserParser.parseSystemUser(resultSet);

            if (resultSet.next()) {
                return null;
            }

            return systemUser;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Get a User by email. This is used when a user is trying to log in.
     * 
     * @param email the email of the user
     * @return a SystemUser
     */
    public SystemUser get(String email) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_SYSTEM_USER_BY_EMAIL)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setString(1, email);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            if (!resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("no user with email " + email);
                return null;
            }

            SystemUser systemUser = SystemUserParser.parseSystemUser(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("more than one user with email " + email);
                return null;
            }

            return systemUser;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Returns the salt for the password of a particular user, so that it can be used for log-in purposes (in comparison).
     * @param user_id of type UUID, representing the user's ID.
     * @return of type byte[], representing the salt of the password.
     */
    public byte[] getPasswordSaltforUser(UUID user_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_PASSWORD_SALT_BY_ID)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, user_id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();
            if (!resultSet.next()) {
                return null;
            }

            byte[] salt = resultSet.getBytes(1);

            return salt;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Returns all school admin details
     * 
     * @return a list with all school admins and their details
     */
    public List<SchoolAdminDetails> getSchoolAdminDetails() {
        List<SchoolAdminDetails> schoolAdminDetails = new ArrayList<>();
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_ALL_SCHOOL_ADMINS_DETAILS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            while (resultSet.next()) {
                schoolAdminDetails.add(SystemUserParser.parseSchoolAdminDetails(resultSet));
            }

            return schoolAdminDetails;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Returns all system users from the database
     * 
     * @return a list of all system users
     */
    @Override
    public List<SystemUser> getAll() {
        List<SystemUser> systemUsers = new ArrayList<>();
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_ALL_SYSTEM_USERS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            while (resultSet.next()) {
                systemUsers.add(SystemUserParser.parseSystemUser(resultSet));
            }

            return systemUsers;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for updating a SystemUser record in the database(either insert or
     * update)
     * 
     * @param systemUser  of type SystemUser, the system user that is going to be
     *                    updated
     * @param modifyQuery of type String, the query that is going to be executed
     * @return the updated system user
     */
    public SystemUser updateRecord(SystemUser systemUser, String modifyQuery, boolean is_update) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(modifyQuery)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, systemUser.getAccount_id());
            preparedStatement.setString(2, systemUser.getType().toString());
            preparedStatement.setString(3, systemUser.getUsername());
            preparedStatement.setString(4, systemUser.getEmail());
            HashedPasswordContainer hpc = PasswordService
                    .generateHashedPasswordContainer(systemUser.getPassword_value()); // this meas that every time the
                                                                                      // user gets updated, their hash
                                                                                      // would get updated as well
            preparedStatement.setString(5, hpc.getHashedPassword());
            preparedStatement.setBytes(6, hpc.getSalt());

            if (is_update) {
                preparedStatement.setObject(7, systemUser.getAccount_id());
            }

            preparedStatement.execute();
            ResultSet result = preparedStatement.getResultSet();

            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("no user record was updated for user id: " + systemUser.getAccount_id());
                return null;
            }

            return SystemUserParser.parseSystemUser(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Creates a new system user in the database
     * 
     * @param systemUser of type SystemUser, the system user that is going to be
     *                   created
     * @return the created system user
     */
    @Override
    public SystemUser save(SystemUser systemUser) {
        systemUser.setAccount_id(UUID.randomUUID());

        if (get(systemUser.getAccount_id()) != null) {
            LoggerManager.DAO_LOGGER.warning("user with id " + systemUser.getAccount_id() + " already exists");
            return null;
        }

        return updateRecord(systemUser, CREATE_SYSTEM_USER, false);
    }

    /**
     * Updates a system user in the database
     * 
     * @param systemUser of type SystemUser, the system user that is going to be
     *                   updated
     * @return the updated system user
     */
    @Override
    public SystemUser update(SystemUser systemUser) {
        return updateRecord(systemUser, UPDATE_SYSTEM_USER, true);
    }

    /**
     * Deletes a system user from the database
     *
     * @return the deleted system user
     */
    @Override
    public void delete(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_SYSTEM_USER)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, id);
            int updateRowCount = preparedStatement.executeUpdate();

            if (updateRowCount != 1) {
                LoggerManager.DAO_LOGGER.warning(
                        updateRowCount + " records were updated(out of 1) when trying to delete for id: " + id);
                return;
            }

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    // SCHOOL-ADMIN
    // ---------------------------------------------------------------------------------------------------------------

    /**
     * Method for getting a SchoolAdmin record from the database
     * 
     * @param id of type UUID, the id of the school admin that is going to be
     * @return the school admin
     */
    public SchoolAdmin getSchoolAdmin(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_SCHOOL_ADMIN_BY_ID)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();
            if (!resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("no school admin with id " + id);
                return null;
            }

            SchoolAdmin schoolAdmin = SystemUserParser.parseSchoolAdmin(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("more than one school admin with id " + id);
                return null;
            }

            return schoolAdmin;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for getting school admin details for a specific school admin
     * 
     * @param id of type UUID, the id of the school admin that is going to be
     * @return the school admin details
     */
    public SchoolAdminDetails getSchoolAdminDetails(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_SCHOOL_ADMIN_DETAILS_BY_ID)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            if (!resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("no school admin details for school admin id: " + id);
                return null;
            }

            SchoolAdminDetails schoolAdminDetails = SystemUserParser.parseSchoolAdminDetails(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("more than one school admin details record for school admin id: " + id);
                return null;
            }

            return schoolAdminDetails;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for getting all SchoolAdmin records from the database
     * 
     * @return a list of all school admins
     */
    public List<SchoolAdmin> getAllSchoolAdmins() {
        List<SchoolAdmin> schoolAdmins = new ArrayList<>();
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_ALL_SCHOOL_ADMINS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            while (resultSet.next()) {
                schoolAdmins.add(SystemUserParser.parseSchoolAdmin(resultSet));
            }

            return schoolAdmins;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for updating a SchoolAdmin record in the database(either insert or
     * update)
     *
     * @param schoolAdmin of type SchoolAdmin, the system user that is going to be
     *                    updated
     * @param modifyQuery of type String, the query that is going to be executed
     * @return the updated school admin
     */
    public SchoolAdmin updateRecordSchoolAdmin(SchoolAdmin schoolAdmin, String modifyQuery, boolean is_update) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(modifyQuery)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, schoolAdmin.getAdminID());
            preparedStatement.setString(2, schoolAdmin.getSurname());
            preparedStatement.setString(3, schoolAdmin.getPhoneNumber());
            preparedStatement.setDate(4, getDate(schoolAdmin.getBirthDate()));
            preparedStatement.setString(5, getStringFromList(schoolAdmin.getGivenNames()));
            preparedStatement.setObject(6, schoolAdmin.getSchoolID());
            preparedStatement.setObject(7, schoolAdmin.getEmployeeID());

            if (is_update) {
                preparedStatement.setObject(8, schoolAdmin.getAdminID());
            }

            preparedStatement.execute();
            ResultSet result = preparedStatement.getResultSet();

            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("no school admin record was updated for school admin id: " + schoolAdmin.getAdminID());
                return null;
            }

            return SystemUserParser.parseSchoolAdmin(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Creates a new school admin in the database
     *
     * @param schoolAdmin of type SchoolAdmin, the school admin that is going to be
     *                    created
     * @return the created system user
     */
    public SchoolAdmin saveSchoolAdmin(SchoolAdmin schoolAdmin) {

        if (getSchoolAdmin(schoolAdmin.getAdminID()) != null) {
            LoggerManager.DAO_LOGGER.warning("user with id " + schoolAdmin.getAdminID() + " already exists");
            return null;
        }

        return updateRecordSchoolAdmin(schoolAdmin, CREATE_SCHOOL_ADMIN, false);
    }

    /**
     * Updates a school admin in the database
     *
     * @param schoolAdmin of type SchoolAdmin, the school admin that is going to be
     *                    updated
     * @return the updated school admin
     */
    public SchoolAdmin updateSchoolAdmin(SchoolAdmin schoolAdmin) {
        if (getSchoolAdmin(schoolAdmin.getAdminID()) == null) {
            LoggerManager.DAO_LOGGER.warning("school admin with id " + schoolAdmin.getAdminID() + " does not exist");
        }

        return updateRecordSchoolAdmin(schoolAdmin, UPDATE_SCHOOL_ADMIN, true);
    }

    /**
     * Deletes a school admin from the database
     * 
     * @param id of type UUID, the id of the school admin that is going to be
     */
    public void deleteSchoolAdmin(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_SCHOOL_ADMIN)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, id);
            int updateRowCount = preparedStatement.executeUpdate();

            if (updateRowCount != 1) {
                LoggerManager.DAO_LOGGER.warning(
                        updateRowCount + " records were updated(out of 1) when trying to delete for id: " + id);
                return;
            }

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    @Override
    public Connection requestConnection() {
        return null;
    }
}
