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
import org.Topicus.Model.RegistrationForm.FormComponent;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.FormComponentParser;
import org.Topicus.Utility.Query.QueryUtils;

public enum FormComponentDAO implements DAO<FormComponent> {
    instance;

    // QUERY(IES) ------------------------------------------
    private final static String GET_FORM_COMPONENT_BY_ID = "SELECT * FROM t_registration_form_component WHERE component_id = ?";

    private final static String GET_FORM_COMPONENTS_FOR_FORM = "SELECT * FROM t_registration_form_component WHERE registration_form_id = ?";

    private final static String GET_FORM_COMPONENTS_FOR_SECTION = "SELECT * FROM t_registration_form_component WHERE section_id = ?";

    private final static String INSERT_FORM_COMPONENT = "INSERT INTO t_registration_form_component(component_id, registration_form_id, section_id, position_number, title, mandatory, data_type) VALUES (?, ?, ?, ?, ?, ?, ?) RETURNING *";

    private final static String BULK_INSERT_FORM_COMPONENTS = "INSERT INTO t_registration_form_component(component_id, registration_form_id, section_id, position_number, title, mandatory, data_type) VALUES ";

    private final static String UPDATE_FORM_COMPONENT = "UPDATE t_registration_form_component SET component_id = ?, registration_form_id = ?, section_id = ?, position_number = ?, title = ?, mandatory = ?, data_type = ? WHERE component_id = ? RETURNING *";

    private final static String BULK_UPDATE_FORM_COMPONENTS = "UPDATE t_registration_form_component SET ";

    private final static String DELETE_FORM_COMPONENT = "DELETE FROM t_registration_form_component WHERE component_id = ?";

    private final static String DELETE_FORM_COMPONENTS_FOR_FORM = "DELETE FROM t_registration_form_component WHERE registration_form_id = ?";

    private final static String DELETE_OLD_FORM_COMPONENTS_FOR_FORM = "DELETE FROM t_registration_form_component WHERE registration_form_id = ? AND component_id NOT IN ";

    // CONSTRUCTOR(S) --------------------------------------
    FormComponentDAO() {

    }

    // ACCESS METHOD(S) ------------------------------------

    /**
     * Method to return singleton instance of DAO class.
     * 
     * @return of type AccountDAO.
     */
    public static FormComponentDAO getInstance() {
        return instance;
    }

    // METHOD(S) ----------------------------------------------

    /**
     * Method for getting a FormComponent from the database.'
     * 
     * @param id of type UUID.
     * @return of type FormComponent.
     */
    @Override
    public FormComponent get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_FORM_COMPONENT_BY_ID)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();

            ResultSet resultSet = preparedStatement.getResultSet();

            if (!resultSet.next()) {
                return null;
            }

            FormComponent formComponent = FormComponentParser.parseComponent(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("multiple components with id " + id);
            }

            return formComponent;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for getting all FormComponents from the database.
     * 
     * @return of type List<FormComponent>.
     */
    @Override
    public List<FormComponent> getAll() {
        return null; // WE DON'T NEED THIS
    }

    /**
     * Method for getting all FormComponents for a given form.
     * 
     * @param form_id of type UUID.
     * @return of type List<FormComponent>.
     */
    public List<FormComponent> getAllComponentsForForm(UUID form_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_FORM_COMPONENTS_FOR_FORM)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, form_id);

            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<FormComponent> formComponentList = new ArrayList<>();

            while (resultSet.next()) {
                formComponentList.add(FormComponentParser.parseComponent(resultSet));
            }

            return formComponentList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for getting all FormComponents for a given section.
     * 
     * @param section_id of type UUID.
     * @return of type List<FormComponent>.
     */
    public List<FormComponent> getAllComponentsForSection(UUID section_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_FORM_COMPONENTS_FOR_SECTION)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, section_id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<FormComponent> sectionFormComponentList = new ArrayList<>();
            while (resultSet.next()) {
                sectionFormComponentList.add(FormComponentParser.parseComponent(resultSet));
            }

            return sectionFormComponentList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to update a FormComponent record in the database.(either insert or
     * update)
     * 
     * @param formComponent of type FormComponent.
     * @param modifyQuery   of type String.
     * @return of type FormComponent.
     */
    private FormComponent updateRecord(FormComponent formComponent, String modifyQuery, boolean is_update) {

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(modifyQuery)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, formComponent.getComponent_id());
            preparedStatement.setObject(2, formComponent.getRegistration_form_id());
            preparedStatement.setObject(3, formComponent.getSection_id());
            preparedStatement.setInt(4, formComponent.getPosition());
            preparedStatement.setString(5, formComponent.getTitle());
            preparedStatement.setBoolean(6, formComponent.isMandatory());
            preparedStatement.setString(7, formComponent.getData_type().toString());
            if (is_update) {
                preparedStatement.setObject(8, formComponent.getComponent_id());
            }

            preparedStatement.execute();
            ResultSet result = preparedStatement.getResultSet();

            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("no record was updated for component id: " + formComponent.getComponent_id());
                return null;
            }

            return FormComponentParser.parseComponent(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to save a new FormComponent to the database.
     * 
     * @param formComponent of type FormComponent.
     * @return of type FormComponent.
     */
    @Override
    public FormComponent save(FormComponent formComponent) {
        formComponent.setComponent_id(UUID.randomUUID());
        if (get(formComponent.getComponent_id()) != null) {
            LoggerManager.DAO_LOGGER
                    .warning("component with id " + formComponent.getComponent_id() + " already exists");
            return null;
        }

        return updateRecord(formComponent, INSERT_FORM_COMPONENT, false);
    }

    /**
     * Method for bulk saving FormComponents to the database.
     * 
     * @param formComponentList of type List<FormComponent>.
     * @return of type List<FormComponent>.
     */
    public List<FormComponent> bulkCreateFormComponents(List<FormComponent> formComponentList) {
        String query = BULK_INSERT_FORM_COMPONENTS + QueryUtils.generateInsertPlaceholders(7, formComponentList.size());
        query += " RETURNING *";

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(query)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            int index = 1;
            for (FormComponent formComponent : formComponentList) {
                preparedStatement.setObject(index++, formComponent.getComponent_id());
                preparedStatement.setObject(index++, formComponent.getRegistration_form_id());
                preparedStatement.setObject(index++, formComponent.getSection_id());
                preparedStatement.setInt(index++, formComponent.getPosition());
                preparedStatement.setString(index++, formComponent.getTitle());
                preparedStatement.setBoolean(index++, formComponent.isMandatory());
                preparedStatement.setString(index++, formComponent.getData_type() == null ? null
                        : formComponent.getData_type().toString());
            }

            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<FormComponent> createdFormComponentList = new ArrayList<>();
            while (resultSet.next()) {
                createdFormComponentList.add(FormComponentParser.parseComponent(resultSet));
            }

            return createdFormComponentList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to update an existing FormComponent in the database.
     * 
     * @param formComponent of type FormComponent.
     * @return of type FormComponent.
     */
    @Override
    public FormComponent update(FormComponent formComponent) {
        if (get(formComponent.getComponent_id()) == null) {
            LoggerManager.DAO_LOGGER
                    .warning("component with id " + formComponent.getComponent_id() + " does not exist");
            return null;
        }

        return updateRecord(formComponent, UPDATE_FORM_COMPONENT, true);
    }

    /**
     * Method for bulk updating FormComponents in the database.
     *
     * @param registrationFormID of type UUID
     * @param componentList of type List<FormComponent>.
     * @return of type List<FormComponent>.
     */
    public List<FormComponent> bulkUpdateFormComponentsForForm(UUID registrationFormID,
            List<FormComponent> componentList) {
        List<String> columnNames = new ArrayList<>();
        columnNames.add("registration_form_id");
        columnNames.add("section_id");
        columnNames.add("position_number");
        columnNames.add("title");
        columnNames.add("mandatory");
        columnNames.add("data_type");

        String query = BULK_UPDATE_FORM_COMPONENTS + QueryUtils.generateUpdatePlaceholders("component_id",
                "registration_form_id", columnNames, componentList.size());
        query += " RETURNING *;";

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(query)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            int index = 1;
            for (FormComponent formComponent : componentList) {
                preparedStatement.setObject(index++, formComponent.getComponent_id());
                preparedStatement.setObject(index++, registrationFormID);
            }

            for (FormComponent formComponent : componentList) {
                preparedStatement.setObject(index++, formComponent.getComponent_id());
                preparedStatement.setObject(index++, formComponent.getSection_id());
            }

            for (FormComponent formComponent : componentList) {
                preparedStatement.setObject(index++, formComponent.getComponent_id());
                preparedStatement.setInt(index++, formComponent.getPosition());
            }

            for (FormComponent formComponent : componentList) {
                preparedStatement.setObject(index++, formComponent.getComponent_id());
                preparedStatement.setString(index++, formComponent.getTitle());
            }

            for (FormComponent formComponent : componentList) {
                preparedStatement.setObject(index++, formComponent.getComponent_id());
                preparedStatement.setBoolean(index++, formComponent.isMandatory());
            }

            for (FormComponent formComponent : componentList) {
                preparedStatement.setObject(index++, formComponent.getComponent_id());
                preparedStatement.setString(index++, formComponent.getData_type().toString());
            }

            preparedStatement.setObject(index, registrationFormID);

            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<FormComponent> updatedFormComponentList = new ArrayList<>();
            while (resultSet.next()) {
                updatedFormComponentList.add(FormComponentParser.parseComponent(resultSet));
            }

            return updatedFormComponentList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to delete a FormComponent from the database.
     * 
     * @param component_id of type UUID.
     */
    @Override
    public void delete(UUID component_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_FORM_COMPONENT)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, component_id);
            int updateRowCount = preparedStatement.executeUpdate();

            if (updateRowCount != 1) {
                LoggerManager.DAO_LOGGER.warning(updateRowCount
                        + " rows were updated(out of 1) when trying to delete for component id: " + component_id);
                return;
            }

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    /**
     * Method to delete all FormComponents for a form from the database.
     * 
     * @param registrationFormID of type UUID.
     */
    public void deleteComponentsForForm(UUID registrationFormID) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_FORM_COMPONENTS_FOR_FORM)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, registrationFormID);
            preparedStatement.executeUpdate();

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    /**
     * Method for deleting all old form components for a form
     * 
     * @param registrationFormID
     * @param formComponentIdList list of form component ids
     */
    public void deleteOldFormComponents(UUID registrationFormID, List<UUID> formComponentIdList) {
        String query = DELETE_OLD_FORM_COMPONENTS_FOR_FORM
                + QueryUtils.generateDeletePlaceholders(formComponentIdList.size());

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(query)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);

            int index = 1;
            preparedStatement.setObject(index++, registrationFormID);
            for (UUID formComponentId : formComponentIdList) {
                preparedStatement.setObject(index++, formComponentId);
            }

            preparedStatement.executeUpdate();

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
