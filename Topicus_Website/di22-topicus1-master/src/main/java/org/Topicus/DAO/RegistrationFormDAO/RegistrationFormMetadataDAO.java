package org.Topicus.DAO.RegistrationFormDAO;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.Contract.DAO;
import org.Topicus.Model.RegistrationForm.RegistrationFormMetadata;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.RegistrationFormMetadataParser;

public enum RegistrationFormMetadataDAO implements DAO<RegistrationFormMetadata> {
    instance;

    // QUERY(IES) ------------------------------------------

    private final static String LOAD_REGISTRATION_FORM_METADATA = "SELECT * FROM t_registration_form WHERE registration_form_id = ?";

    private final static String LOAD_ALL_REGISTRATION_FORMS_METADATA = "SELECT * FROM t_registration_form";

    private final static String LOAD_REGISTRATION_FORM_METADATA_FOR_SCHOOL = "SELECT * FROM t_registration_form WHERE school_id = ?";

    private final static String INSERT_REGISTRATION_FORM_METADATA = "INSERT INTO t_registration_form(registration_form_id, school_id, title, description, year, education_type, isdeleted, isactive, startDate) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?) RETURNING *";

    private final static String UPDATE_REGISTRATION_FORM_METADATA = "UPDATE t_registration_form SET registration_form_id = ?, school_id = ?, title = ?, description = ?, year = ?, education_type = ?, isdeleted = ?, isactive = ?, startDate = ? WHERE registration_form_id = ? RETURNING *";

    private final static String DELETE_REGISTRATION_FORM_METADATA = "DELETE FROM t_registration_form WHERE registration_form_id = ?";

    // CONSTRUCTOR(S) --------------------------------------
    RegistrationFormMetadataDAO() {

    }

    // ACCESS METHOD(S) ------------------------------------

    /**
     * Method to return singleton instance of DAO class.
     * 
     * @return of type AccountDAO.
     */
    public static RegistrationFormMetadataDAO getInstance() {
        return instance;
    }

    // METHOD(S) ----------------------------------------------

    /**
     * Method to return the metadata of a registration form
     * 
     * @return of type RegistrationFormMetadata.
     */
    @Override
    public RegistrationFormMetadata get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(LOAD_REGISTRATION_FORM_METADATA)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();
            if (!resultSet.next()) {
                return null;
            }

            RegistrationFormMetadata form = RegistrationFormMetadataParser.parseFormMetadata(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("More than one registration form metadata found for id: " + id);
            }

            return form;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to return all registration forms metadata
     * 
     * @return of type List<RegistrationFormMetadata>.
     */
    @Override
    public List<RegistrationFormMetadata> getAll() {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection
                        .prepareStatement(LOAD_ALL_REGISTRATION_FORMS_METADATA)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<RegistrationFormMetadata> registrationFormMetadataList = new ArrayList<>();

            while (resultSet.next()) {
                registrationFormMetadataList.add(RegistrationFormMetadataParser.parseFormMetadata(resultSet));
            }

            return registrationFormMetadataList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to get all registration form metadata for a school
     * 
     * @param school_id of type UUID.
     * @return of type List<RegistrationFormMetadata>.
     */
    public List<RegistrationFormMetadata> getRegistrationFormMetadataForSchool(UUID school_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection
                        .prepareStatement(LOAD_REGISTRATION_FORM_METADATA_FOR_SCHOOL)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, school_id);

            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<RegistrationFormMetadata> registrationFormMetadataList = new ArrayList<>();
            while (resultSet.next()) {
                registrationFormMetadataList.add(RegistrationFormMetadataParser.parseFormMetadata(resultSet));
            }

            return registrationFormMetadataList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for updating a RegistrationFormMetadata record in the database(either
     * insert
     * or update)
     * 
     * @param registrationFormMetadata of type RegistrationFormMetadata.
     * @param modifyQuery              of type String.
     * @return of type RegistrationFormMetadata.
     */
    private RegistrationFormMetadata updateRecord(RegistrationFormMetadata registrationFormMetadata, String modifyQuery,
            boolean is_update) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(modifyQuery)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, registrationFormMetadata.getRegistration_form_id());
            preparedStatement.setObject(2, registrationFormMetadata.getSchool_id());
            preparedStatement.setString(3, registrationFormMetadata.getTitle());
            preparedStatement.setString(4, registrationFormMetadata.getDescription());
            preparedStatement.setInt(5, registrationFormMetadata.getYear());
            preparedStatement.setString(6, registrationFormMetadata.getEducation_type());
            preparedStatement.setBoolean(7, registrationFormMetadata.isIs_deleted());
            preparedStatement.setBoolean(8, registrationFormMetadata.isIs_active());
            preparedStatement.setDate(9, registrationFormMetadata.getStart_date());
            if (is_update) {
                preparedStatement.setObject(10, registrationFormMetadata.getRegistration_form_id());
            }

            preparedStatement.execute();
            ResultSet result = preparedStatement.getResultSet();

            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("no record was updated for id: " + registrationFormMetadata.getRegistration_form_id());
                return null;
            }

            return RegistrationFormMetadataParser.parseFormMetadata(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to save individual registration form metadata to the database
     * 
     * @param registrationFormMetadata of type RegistrationFormMetadata.
     * @return of type RegistrationFormMetadata.
     */
    @Override
    public RegistrationFormMetadata save(RegistrationFormMetadata registrationFormMetadata) {
        if (get(registrationFormMetadata.getRegistration_form_id()) != null) {
            LoggerManager.DAO_LOGGER.warning(
                    "form with id " + registrationFormMetadata.getRegistration_form_id() + " already exists");
            return null;
        }

        return updateRecord(registrationFormMetadata, INSERT_REGISTRATION_FORM_METADATA, false);
    }

    /**
     * Method to update individual registration form metadata in the database
     * 
     * @param registrationFormMetadata of type RegistrationFormMetadata.
     * @return of type RegistrationFormMetadata.
     */
    @Override
    public RegistrationFormMetadata update(RegistrationFormMetadata registrationFormMetadata) {
        if (get(registrationFormMetadata.getRegistration_form_id()) == null) {
            LoggerManager.DAO_LOGGER.warning(
                    "form with id " + registrationFormMetadata.getRegistration_form_id() + " doesn't exist");
            return null;
        }

        return updateRecord(registrationFormMetadata, UPDATE_REGISTRATION_FORM_METADATA, true);
    }

    /**
     * Method to delete individual registration form metadata from the database
     *
     * @param form_id of type UUID.
     */
    @Override
    public void delete(UUID form_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_REGISTRATION_FORM_METADATA)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, form_id);
            int updateRowCount = preparedStatement.executeUpdate();

            if (updateRowCount != 1) {
                LoggerManager.DAO_LOGGER.warning(
                        updateRowCount + " were updated(out of 1) when trying to delete metadata for id: " + form_id);
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

    /**
     * Method to get the metadata for the active registration form for a school
     * 
     * @param school_id of type UUID.
     * @return of type RegistrationFormMetadata.
     */
    public RegistrationFormMetadata getActiveFormMetadata(UUID school_id) {
        List<RegistrationFormMetadata> activeForms = getAll().stream()
                .filter(form -> form.getSchool_id().equals(school_id) && form.isIs_active()).toList();

        if (activeForms.size() != 1) {
            LoggerManager.DAO_LOGGER
                    .warning("school with id " + " has " + activeForms.size() + " active forms(out of 1)");
            return null;
        }

        return activeForms.get(0);
    }
}
