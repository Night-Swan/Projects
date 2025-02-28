package org.Topicus.DAO.SchoolDAO;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.Contract.DAO;
import org.Topicus.Model.School.School;
import org.Topicus.Payload.Response.School.SchoolDetails;
import org.Topicus.Payload.Response.School.SchoolName;
import org.Topicus.Payload.Response.SchoolAdmin.SchoolAdminDetails;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.SchoolParser;
import org.Topicus.Utility.Parsers.SystemUserParser;

public enum SchoolDAO implements DAO<School>, SchoolParser, SystemUserParser {
    instance;

    // CONSTANTS (SQL QUERIES)
    // ---------------------------------------------------------------------------------------
    public static final String GET_SCHOOL_BY_ID = "SELECT * FROM t_school WHERE school_id = ?";
    private static final String GET_ALL_SCHOOLS = "SELECT * FROM t_school";
    private static final String GET_ALL_NAMES = "SELECT school_name, school_type FROM t_school";
    private static final String GET_ALL_SCHOOLS_DETAILS = "SELECT s.school_id, s.address_id, s.school_name, s.school_type, s.phone_number, s.email, a.postal_code, a.street_name, a.street_number, a.city, a.country, a.phone_number FROM t_school s, t_address a WHERE s.address_id = a.address_id";
    private static final String GET_ALL_ADMINS_OF_SCHOOL = "SELECT su.account_id, su.type, su.username, su.email, sa.surname, sa.phone_number, sa.date_of_birth, sa.given_names,sa.school_id, sa.employee_id FROM t_system_user su, t_school_administrator sa WHERE su.account_id = sa.sa_id AND su.type = 'SCHOOL_ADMIN' AND sa.school_id = ?";
    public static final String DELETE_SCHOOL = "DELETE FROM t_school WHERE school_id = ?";
    public static final String CREATE_SCHOOL = "INSERT INTO t_school(school_id, address_id, school_name, school_type, phone_number, email) VALUES(?, ?, ?, ?, ?, ?) RETURNING *";
    private final static String UPDATE_SCHOOL = "UPDATE t_school SET school_id = ?, address_id = ?, school_name = ?, school_type = ?, phone_number = ?, email = ?  WHERE school_id = ? RETURNING *";

    // CONSTRUCTOR(S) --------------------------------------
    SchoolDAO() {

    }

    // ACCESS METHOD(S) ------------------------------------

    /**
     * Method to return enum instance of DAO class.
     * 
     * @return of type AccountDAO.
     */
    public static SchoolDAO getInstance() {
        return instance;
    }

    // METHOD(S) ----------------------------------------------

    /**
     * Returns one specific school
     * 
     * @param id of type long, representing the id of the element.
     * @return the school with the id passed as a parameter
     */
    @Override
    public School get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_SCHOOL_BY_ID)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            if (!resultSet.next()) {
                return null;
            }

            School school = SchoolParser.parseSchool(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("more than one school found with id: " + id);
                return null;
            }

            return school;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Returns all the schools from the database
     * 
     * @return list with all the schools
     */
    @Override
    public List<School> getAll() {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_ALL_SCHOOLS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<School> schoolList = new ArrayList<>();
            while (resultSet.next()) {
                schoolList.add(SchoolParser.parseSchool(resultSet));
            }

            return schoolList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method is used to return the details of all the schools in the system.
     * @return of type List<SchoolDetails>
     */
    public List<SchoolDetails> getAllSchoolDetails() {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_ALL_SCHOOLS_DETAILS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<SchoolDetails> schoolList = new ArrayList<>();
            while (resultSet.next()) {
                schoolList.add(SchoolParser.parseSchoolDetails(resultSet));
            }

            return schoolList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method is used to get the details of all the admins for a particular school.
     * @param id of type UUID, representing the SchoolID.
     * @return of type List<SchoolAdminDetails>
     */
    public List<SchoolAdminDetails> getAdminDetailsBySchool(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_ALL_ADMINS_OF_SCHOOL)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<SchoolAdminDetails> adminList = new ArrayList<>();
            while (resultSet.next()) {
                adminList.add(SystemUserParser.parseSchoolAdminDetails(resultSet));
            }

            return adminList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for updating a School record in the database(either insert or update).
     * 
     * @param school      of type School, representing the school to be updated.
     * @param modifyQuery of type String, representing the query to be executed.
     * @param is_update   of type boolean, representing if the query is an update or
     *                    insert.
     * @return of type School, representing the school that was updated.
     */
    public School updateRecord(School school, String modifyQuery, boolean is_update) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(modifyQuery)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.setObject(1, school.getSchool_id());
            ps.setObject(2, school.getAddress_id());
            ps.setString(3, school.getName());
            ps.setString(4, school.getType());
            ps.setString(5, school.getPhone_number());
            ps.setString(6, school.getEmail());
            if (is_update) {
                ps.setObject(7, school.getSchool_id());
            }
            ps.execute();
            ResultSet resultSet = ps.getResultSet();

            if (!resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("no school for id: " + school.getSchool_id());
                return null;
            }

            return SchoolParser.parseSchool(resultSet);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Creates a new School record in the database.
     * 
     * @param school of type School, representing the school to be created.
     * @return of type School, representing the school that was created.
     */
    public School save(School school) {
        school.setSchool_id(UUID.randomUUID());

        if (get(school.getSchool_id()) != null) {
            LoggerManager.DAO_LOGGER.warning("school with id " + school.getSchool_id() + " already exists");
            return null;
        }

        return updateRecord(school, CREATE_SCHOOL, false);
    }

    /**
     * Updates a School record in the database.
     * 
     * @param school of type School, representing the school to be updated.
     * @return of type School, representing the school that was updated.
     */
    public School update(School school) {
        if (get(school.getSchool_id()) == null) {
            LoggerManager.DAO_LOGGER.warning("school with id " + school.getSchool_id() + " does not exist");
            return null;
        }

        return updateRecord(school, UPDATE_SCHOOL, true);
    }

    /**
     * deletes one school from the database with a specific id
     * 
     * @param id the id of the object that is going to be deleted
     */
    @Override
    public void delete(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(DELETE_SCHOOL)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.setObject(1, id);
            int updateRowCount = ps.executeUpdate();

            if (updateRowCount != 1) {
                LoggerManager.DAO_LOGGER.warning(
                        updateRowCount + " rows were updated(out of 1) when trying to delete for school id: " + id);
                return;
            }

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    /**
     * method to be used in SchoolResources for getting all the school's name
     * 
     * @return of type List<SchoolName>
     */
    public List<SchoolName> getAllNames() {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(GET_ALL_NAMES)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.execute();
            ResultSet resultSet = ps.getResultSet();

            return parseSchoolNames(resultSet);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }

    }

    @Override
    public Connection requestConnection() {
        return null;
    }
}
