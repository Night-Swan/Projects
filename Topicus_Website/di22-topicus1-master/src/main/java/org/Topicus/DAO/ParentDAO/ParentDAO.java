package org.Topicus.DAO.ParentDAO;

import java.sql.Connection;
import java.sql.Date;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.Contract.DAO;
import org.Topicus.Model.Guardian.Guardian;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.ChildParser;
import org.Topicus.Utility.Parsers.DateParser;
import org.Topicus.Utility.Parsers.ListParser;
import org.Topicus.Utility.Parsers.ParentParser;

public enum ParentDAO implements DAO<Guardian>, ParentParser, ChildParser, ListParser, DateParser {
    // FIELD VARIABLE(S) -----------------------------------
    instance;

    private static final String GET_ALL_GUARDIANS = "SELECT * FROM t_guardian";
    private static final String LOAD_GUARDIAN_BY_ID = "SELECT * FROM t_guardian WHERE guardian_id = ?";
    private static final String LOAD_GUARDIAN_BY_USER = "SELECT * FROM t_guardian WHERE account_id = ?";
    private static final String CREATE_GUARDIAN = "INSERT INTO t_guardian(guardian_id, account_id, address_id, nationality, surname, phone_number, date_of_birth, given_names, occupation, company_name) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?) RETURNING *";
    private static final String UPDATE_GUARDIAN = "UPDATE t_guardian SET guardian_id = ?, account_id = ?, address_id = ?, nationality = ?, surname = ?, phone_number = ?, date_of_birth = ?, given_names = ?, occupation = ?, company_name = ? WHERE guardian_id = ? RETURNING *";
    public static final String DELETE_GUARDIAN = "DELETE FROM t_guardian WHERE guardian_id = ?";
    public static final String LOAD_GUARDIAN_BY_SCHOOL = "SELECT g.* FROM t_guardian g, t_registration r WHERE r.school_id = ? AND r.guardian_id = g.guardian_id";

    /**
     * Method to return enum instance of DAO class.
     * 
     * @return of type AccountDAO.
     */
    public static ParentDAO getInstance() {
        return instance;
    }

    // BASIC METHOD(S) ----------------------------------------------

    /**
     * Method to retrieve a particular Guardian.
     *
     * @param id of type UUID, representing the id of the element.
     * @return of type Guardian (can be null).
     */
    @Override
    public Guardian get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(LOAD_GUARDIAN_BY_ID)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, id);
            ps.execute();
            ResultSet resultSet = ps.getResultSet();

            if (!resultSet.next()) {
                return null;
            }

            Guardian guardian = parseParent(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("multiple guardians with id " + id + " exist");
            }

            return guardian;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to retrieve a particular Guardian, by account id
     *
     * @param id of type UUID, representing the id of account
     * @return of type Guardian (can be null).
     */
    public Guardian getByAccount(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(LOAD_GUARDIAN_BY_USER)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, id);
            ps.execute();
            ResultSet resultSet = ps.getResultSet();
            if (!resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("guardian with account id " + id + " does not exist");
                return null;
            }

            return parseParent(resultSet);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for getting all Guardians from the database.
     * 
     * @return of type List<Guardian>, representing the list of Guardians.
     */
    @Override
    public List<Guardian> getAll() {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(GET_ALL_GUARDIANS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.execute();
            ResultSet resultSet = ps.getResultSet();

            return parseParents(resultSet);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for updating a Guardian record in the database(either insert or
     * update).
     * 
     * @param guardian of type Guardian, representing the object to be updated.
     * @param query    of type String, representing the query to be executed.
     * @return of type Guardian, representing the updated object.
     */
    public Guardian updateRecord(Guardian guardian, String query, boolean is_update) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(query)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.setObject(1, guardian.getGuardian_id());
            ps.setObject(2, guardian.getAccount_id());
            ps.setObject(3, guardian.getAddress_id());
            ps.setString(4, guardian.getNationality());
            ps.setString(5, guardian.getSurname());
            ps.setString(6, guardian.getPhone_number());
            ps.setDate(7, new Date(guardian.getDate_of_birth().getTime()));
            ps.setString(8, getStringFromList(guardian.getGiven_names()));
            ps.setString(9, guardian.getOccupation());
            ps.setString(10, guardian.getCompany_name());
            if (is_update) {
                ps.setObject(11, guardian.getGuardian_id());
            }
            ps.execute();
            ResultSet resultSet = ps.getResultSet();
            if (!resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("guardian with id " + guardian.getGuardian_id() + " does not exist");
                return null;
            }

            return parseParent(resultSet);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for saving a Guardian record in the database.
     * 
     * @param guardian of type Guardian, representing the object to be saved.
     * @return of type Guardian, representing the saved object.
     */
    public Guardian save(Guardian guardian) {
        guardian.setGuardian_id(UUID.randomUUID());
        if (get(guardian.getGuardian_id()) != null) {
            LoggerManager.DAO_LOGGER.warning("guardian with id " + guardian.getGuardian_id() + " already exists");
            return null;
        }

        return updateRecord(guardian, CREATE_GUARDIAN, false);
    }

    /**
     * Method for updating a Guardian record in the database.
     * 
     * @param guardian of type Guardian, representing the object to be updated.
     * @return of type Guardian, representing the updated object.
     */
    @Override
    public Guardian update(Guardian guardian) {
        if (get(guardian.getGuardian_id()) == null) {
            LoggerManager.DAO_LOGGER.warning("guardian with id " + guardian.getGuardian_id() + " does not exist");
            return null;
        }

        return updateRecord(guardian, UPDATE_GUARDIAN, true);
    }

    /**
     * Method for deleting a Guardian record from the database.
     * 
     * @param id of type UUID, representing the id of the object to be deleted.
     */
    @Override
    public void delete(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(DELETE_GUARDIAN)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.setObject(1, id);
            ps.execute();
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
