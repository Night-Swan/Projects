package org.Topicus.DAO.RegistrationDAO;

import java.sql.Connection;
import java.sql.Date;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;
import java.util.stream.Collectors;

import org.Topicus.DAO.Contract.DAO;
import org.Topicus.DAO.RegistrationFormDAO.SectionDAO;
import org.Topicus.Model.Modification.Modification;
import org.Topicus.Model.Registration.DBDataField;
import org.Topicus.Model.Registration.FEDataField;
import org.Topicus.Model.Registration.Registration;
import org.Topicus.Model.Registration.Status;
import org.Topicus.Model.RegistrationForm.Section;
import org.Topicus.Model.RegistrationForm.Style.Style;
import org.Topicus.Payload.Request.Registration.FieldCreationRequest;
import org.Topicus.Payload.Request.Registration.FieldUpdateRequest;
import org.Topicus.Payload.Request.Registration.RegistrationStatusUpdateRequest;
import org.Topicus.Payload.Response.Registration.ModificationListView;
import org.Topicus.Payload.Response.Registration.RegistrationContainer;
import org.Topicus.Payload.Response.Registration.RegistrationView;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.RegistrationParser;
import org.Topicus.Utility.Parsers.StyleParser;

public enum RegistrationDAO implements DAO<Registration>, RegistrationParser {
    instance;

    // CONSTANTS (SQL QUERIES)
    // ---------------------------------------------------------------------------------------
    public static final String S_LOAD_REGISTRATION = "SELECT r.* FROM T_Registration AS r WHERE r.registration_id = ?";

    public static final String S_LOAD_GUARDIAN_REGISTRATIONS = "SELECT \n" +
            "r.status AS status, \n" +
            "r.registration_id AS rid, \n" +
            "r.school_id AS sid,\n" +
            "CONCAT(g.surname, ', ', g.given_names) AS gname, \n" +
            "CONCAT(c.surname, ', ', c.given_names) AS cname,\n" +
            "g.guardian_id AS gid, \n" +
            "c.child_id AS cid, \n" +
            "s.school_name AS sname,\n" +
            "rf.title AS title, \n" +
            "rf.year AS year\n" +
            "FROM T_Registration AS r, T_Guardian AS g, T_Child AS c, T_School AS s, T_Registration_Form AS rf\n " +
            "WHERE r.guardian_id = ? \n " +
            "AND g.guardian_id = r.guardian_id\n " +
            "AND c.child_id = r.child_id\n" +
            "AND s.school_id = r.school_id\n " +
            "AND rf.registration_form_id = r.registration_form_id\n " +
            "GROUP BY r.registration_id, r.school_id, g.surname, g.given_names, c.surname, c.given_names,\n " +
            "g.guardian_id, c.child_id, r.status, s.school_name, rf.title, rf.year;\n";

    public static final String S_LOAD_SCHOOL_REGISTRATIONS = "SELECT \n" +
            "r.status AS status, \n" +
            "r.registration_id AS rid, \n" +
            "r.school_id AS sid,\n" +
            "CONCAT(g.surname, ', ', g.given_names) AS gname, \n" +
            "CONCAT(c.surname, ', ', c.given_names) AS cname,\n" +
            "g.guardian_id AS gid, \n" +
            "c.child_id AS cid, \n" +
            "s.school_name AS sname,\n" +
            "rf.title AS title, \n" +
            "rf.year AS year\n" +
            "FROM T_Registration AS r, T_Guardian AS g, T_Child AS c, T_School AS s, T_Registration_Form AS rf\n" +
            "WHERE r.school_id = ?\n" +
            "AND g.guardian_id = r.guardian_id\n" +
            "AND c.child_id = r.child_id\n" +
            "AND s.school_id = r.school_id\n" +
            "AND rf.registration_form_id = r.registration_form_id\n" +
            "GROUP BY r.registration_id, r.school_id, g.surname, g.given_names, c.surname, c.given_names,\n" +
            " g.guardian_id, c.child_id, r.status, s.school_name, rf.title, rf.year;";

    public static final String S_GET_REGISTRATIONS_FOR_FORM = "SELECT \n" +
            "r.status AS status, \n" +
            "r.registration_id AS rid, \n" +
            "r.school_id AS sid,\n" +
            "CONCAT(g.surname, ', ', g.given_names) AS gname, \n" +
            "CONCAT(c.surname, ', ', c.given_names) AS cname,\n" +
            "g.guardian_id AS gid, \n" +
            "c.child_id AS cid, \n" +
            "s.school_name AS sname,\n" +
            "rf.title AS title, \n" +
            "rf.year AS year\n" +
            "FROM T_Registration AS r, T_Guardian AS g, T_Child AS c, T_School AS s, T_Registration_Form AS rf\n " +
            "WHERE g.guardian_id = r.guardian_id\n " +
            "AND c.child_id = r.child_id\n" +
            "AND s.school_id = r.school_id\n " +
            "AND rf.registration_form_id = ?\n " +
            "GROUP BY r.registration_id, r.school_id, g.surname, g.given_names, c.surname, c.given_names,\n " +
            "g.guardian_id, c.child_id, r.status, s.school_name, rf.title, rf.year;\n";

    public static final String S_GET_ALL = "SELECT * FROM T_Registration";

    public static final String S_CREATE_REGISTRATION = "INSERT INTO T_Registration(registration_id, guardian_id, child_id, school_id, registration_form_id, status)"
            +
            "VALUES(?, ?, ?, ?, ?, ?) RETURNING *";

    public static final String S_UPDATE_REGISTRATION = "UPDATE T_Registration SET status = ? WHERE registration_id = ? RETURNING *;";

    public static final String S_DELETE_REGISTRATION = "DELETE FROM T_Registration AS r \n" +
            "WHERE r.registration_id = ?;";

    public static final String S_DELETE_FIELDS = "DELETE FROM T_Data_Field AS f \n" +
            "WHERE f.registration_id = ?;";

    public static final String S_LOAD_DATA_FIELDS_FOR_REGISTRATION = "SELECT d.field_id, d.registration_id, d.component_id, rf.section_id, rf.title, d.content, rf.position_number, rf.mandatory, rf.data_type\n"
            +
            "FROM T_Data_Field AS d, T_Registration_Form_Component AS rf, T_Registration AS r\n" +
            "WHERE d.registration_id = ?\n" +
            "AND r.registration_id = d.registration_id\n" +
            "AND rf.registration_form_id = r.registration_form_id\n" +
            "AND rf.component_id = d.component_id;";

    public static final String S_LOAD_SECTIONS_FOR_REGISTRATION = "SELECT s.* \n" +
            "FROM T_Section AS s, T_Registration AS r\n" +
            "WHERE r.registration_id = ?\n" +
            "AND s.registration_form_id = r.registration_form_id;";

    public static final String S_VALIDATE_COUNT_DATAFIELDS = "SELECT COUNT(df.field_id)\n" +
            "FROM T_Data_Field AS df\n" +
            "WHERE df.registration_id = ?;";

    public static final String S_VALIDATE_COUNT_FORMCOMPONENTS = "SELECT COUNT(rfc.component_id) \n" +
            "FROM T_Registration_Form_Component AS rfc, T_Registration AS r \n" +
            "WHERE r.registration_id = ? \n" +
            "AND rfc.registration_form_id = r.registration_form_id;";

    public static final String S_GET_MODIFICATIONS = "SELECT\n" +
            "m.date AS date,\n" +
            "m.sa_id,\n" +
            "s.surname,\n" +
            "m.reg_id,\n" +
            "m.description,\n" +
            "m.visible\n" +
            "FROM T_Modification AS m, T_School_Administrator AS s\n" +
            "WHERE m.reg_id = ? \n" +
            "AND m.sa_id = s.sa_id;";

    public static final String S_GET_STYLE = "SELECT \n" +
            "s.* FROM T_Style AS s\n" +
            "WHERE s.registration_form_id = ?;";

    public static final String GET_REGISTRATION_IDS_FOR_FORM = "SELECT registration_id\n" +
            "FROM t_registration \n" +
            "WHERE registration_form_id = ?";

    public static final String GET_REGISTRATIONS_FOR_IDS = "SELECT * FROM t_registration WHERE registration_id IN ";

    public static final String GET_DATA_FIELDS_FOR_REGISTRATION_IDS = "SELECT d.field_id, d.registration_id, d.component_id, rfc.section_id, rfc.title, d.content, rfc.position_number, rfc.mandatory, rfc.data_type\n"
            + "FROM t_data_field AS d, t_registration_form_component AS rfc, t_registration AS r\n"
            + "WHERE r.registration_id = d.registration_id\n"
            + "AND rfc.registration_form_id = r.registration_form_id\n"
            + "AND rfc.component_id = d.component_id\n"
            + "AND d.registration_id IN ";

    // ACCESS METHOD(S) ------------------------------------

    /**
     * Method to return enum instance of DAO class.
     * 
     * @return of type AccountDAO.
     */
    public static RegistrationDAO getInstance() {
        return instance;
    }

    /**
     * Method to retrieve a particular registration.
     * 
     * @param id of type UUID, representing the id of the element.
     * @return of type Registration (can be null).
     */
    @Override
    public Registration get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_LOAD_REGISTRATION)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, id);
            ps.execute();
            ResultSet result = ps.getResultSet();
            if (!result.next()) {
                return null;
            }

            Registration registration = parseRegistration(result);

            if (result.next()) {
                LoggerManager.DAO_LOGGER.warning("More than one registration found for id: " + id);
            }

            return registration;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method will return a list of RegistrationViews that will be sent to the
     * front-end,
     * to appear as a list on the Guardian's existing registrations page.
     * 
     * @param guardian_id of type UUID, representing the unique guardian_code.
     * @return of type List<RegistrationView>.
     */
    public List<RegistrationView> loadGuardianRegistrations(UUID guardian_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_LOAD_GUARDIAN_REGISTRATIONS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, guardian_id);
            ps.execute();
            ResultSet result = ps.getResultSet();

            return parseRegistrationViews(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method returns a list of RegistrationViews based on a particular school.
     * 
     * @param school_id
     * @return of type List<RegistrationView>.
     */

    public List<RegistrationView> loadSchoolRegistrations(UUID school_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_LOAD_SCHOOL_REGISTRATIONS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, school_id);
            ps.execute();
            ResultSet result = ps.getResultSet();

            return parseRegistrationViews(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method is invoked when a query parameter is provided, which will also
     * sort the list based on those whose Status matches.
     * 
     * @param school_id
     * @param status
     * @return of type List<RegistrationView>.
     */
    public List<RegistrationView> loadSchoolRegistrationsByStatus(UUID school_id, Status status) {
        List<RegistrationView> list = loadSchoolRegistrations(school_id);
        List<RegistrationView> returnList = new ArrayList<>();
        if (!list.isEmpty()) {
            returnList = list.stream().filter(listItem -> {
                return listItem.getStatus() == status;
            }).toList();
        }
        return returnList;
    }

    /**
     * Used for a School Administrator to get registrations for a particular form.
     * 
     * @param form_id of type long.
     * @return of type List<RegistrationView>.
     */
    public List<RegistrationView> loadRegistrationsByForm(UUID form_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_GET_REGISTRATIONS_FOR_FORM)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, form_id);
            ps.execute();
            ResultSet result = ps.getResultSet();

            return parseRegistrationViews(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method is used to return all of the Registrations.
     * 
     * @return of type List<Registration>.
     */
    @Override
    public List<Registration> getAll() {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_GET_ALL)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.execute();
            ResultSet r = ps.getResultSet();

            return parseRegistrations(r);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method is for creating a new registration.
     * 
     * @param registration of type <Registration>.
     * @return of type Registration.
     */
    @Override
    public Registration save(Registration registration) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_CREATE_REGISTRATION)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.setObject(1, UUID.randomUUID());
            ps.setObject(2, registration.getGuardianID());
            ps.setObject(3, registration.getChildID());
            ps.setObject(4, registration.getSchoolID());
            ps.setObject(5, registration.getRegistrationFormID());
            ps.setString(6, registration.getStatus().toString());
            ps.execute();
            ResultSet result = ps.getResultSet();
            if (!result.next()) {
                LoggerManager.DAO_LOGGER.warning("no record was created");
                return null;
            }

            return parseRegistration(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * As a registration only requires updating from the registration_id and the
     * status, this method is used.
     * 
     * @param rsur of type RegistrationStatusUpdateRequest.
     * @return of type Registration
     */
    public Registration updateRegistrationStatus(RegistrationStatusUpdateRequest rsur) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_UPDATE_REGISTRATION)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.setString(1, rsur.getStatus());
            ps.setObject(2, rsur.getConvertedUUID());
            ps.execute();
            ResultSet result = ps.getResultSet();
            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("no record was updated for registration with id: " + rsur.getRegistration_id());
                return null;
            }

            return parseRegistration(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method is for updating the existing registration.
     * 
     * @param registration of type <T>
     * @return of type Registration.
     */
    @Override
    public Registration update(Registration registration) {
        RegistrationStatusUpdateRequest rsur = new RegistrationStatusUpdateRequest(
                registration.getRegistrationID().toString(), registration.getStatus().toString());
        return updateRegistrationStatus(rsur);
    }

    /**
     * This method will delete the existing registration.
     * 
     * @param id The ID of the registration.
     */
    @Override
    public void delete(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_DELETE_REGISTRATION)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.setObject(1, id);
            ps.execute();

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    /**
     * This method is required to delete the fields for the registration.
     * 
     * @param id representing the registrationID.
     */
    public boolean deleteFields(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_DELETE_FIELDS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.setObject(1, id);
            ps.execute();

            return true;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return false;
        }
    }

    /**
     * This method is used to return the RegistrationContainer, which is a body to
     * be sent to the front-end to format and manage the related tasks for the displaying, and editing of registrations.
     * 
     * @param registration_id
     * @return of type RegistrationContainer.
     */
    public RegistrationContainer loadDataFieldsForRegistration(UUID registration_id, Registration reg) {
        List<FEDataField> df_pos = null;

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_LOAD_DATA_FIELDS_FOR_REGISTRATION)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, registration_id);
            ps.execute();

            ResultSet result = ps.getResultSet();

            df_pos = parseDataFields(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }

        List<Section> sections = null;

        try (Connection con = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement prep = con.prepareStatement(S_LOAD_SECTIONS_FOR_REGISTRATION)) {
            con.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            prep.setObject(1, registration_id);
            prep.execute();

            ResultSet resultSet = prep.getResultSet();

            sections = parseSections(resultSet);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }

        return new RegistrationContainer(reg, df_pos, sections);
    }

    /**
     * This method is used to load the registration containers for the form.
     * 
     * @param form_id of type UUID.
     * @return of type List<RegistrationContainer>.
     */
    public List<RegistrationContainer> loadRegistrationContainersForForm(UUID form_id) {
        List<UUID> registration_ids = new ArrayList<>();
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(GET_REGISTRATION_IDS_FOR_FORM)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, form_id);
            ps.execute();
            ResultSet result = ps.getResultSet();

            while (result.next()) {
                UUID registration_id = result.getObject(1, UUID.class);
                registration_ids.add(registration_id);
            }

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }

        String registration_ids_string = registration_ids.stream().map(Object::toString)
                .collect(Collectors.joining("', '", "('", "')"));

        List<Registration> registrations = null;

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                Statement statement = connection.createStatement()) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);

            String query = GET_REGISTRATIONS_FOR_IDS + registration_ids_string;
            ResultSet result = statement.executeQuery(query);

            registrations = parseRegistrations(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }

        List<FEDataField> data_fields_for_registration_ids = null;

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                Statement statement = connection.createStatement()) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            String query = GET_DATA_FIELDS_FOR_REGISTRATION_IDS + registration_ids_string;
            ResultSet result = statement.executeQuery(query);

            data_fields_for_registration_ids = parseDataFields(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            e.printStackTrace();
            return null;
        }

        List<Section> sections_for_registration_ids = SectionDAO.getInstance().getAllSectionsForForm(form_id);

        return resolveRegistrationContainers(registrations, data_fields_for_registration_ids,
                sections_for_registration_ids);
    }

    /**
     * This method is used to resolve the registration containers.
     * 
     * @param registrations                 all the registrations for the form.
     * @param data_fields_for_registrations all the data fields for the
     *                                      registrations.
     * @param sections_for_registrations    all the sections for the
     *                                      registrations.
     * @return of type List<RegistrationContainer>.
     */
    private List<RegistrationContainer> resolveRegistrationContainers(List<Registration> registrations,
            List<FEDataField> data_fields_for_registrations, List<Section> sections_for_registrations) {
        List<RegistrationContainer> registration_containers = new ArrayList<>();

        for (Registration registration : registrations) {
            List<FEDataField> data_fields = data_fields_for_registrations.stream()
                    .filter(df -> df.getRegistrationID().equals(registration.getRegistrationID()))
                    .collect(Collectors.toList());

            List<Section> sections = sections_for_registrations.stream()
                    .filter(s -> s.getRegistration_form_id().equals(registration.getRegistrationFormID()))
                    .collect(Collectors.toList());

            registration_containers.add(new RegistrationContainer(registration, data_fields, sections));
        }

        return registration_containers;
    }

    /**
     * Method used to validate batch update and batch insert.
     * 
     * @param registration_id
     * @return
     */
    public int validateListCountDataField(UUID registration_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_VALIDATE_COUNT_DATAFIELDS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, registration_id);
            ps.execute();
            ResultSet result = ps.getResultSet();
            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("could not validate count of data fields for registration id: " + registration_id);
                return -1;
            }

            return result.getInt(1);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return -1;
        }
    }

    /**
     * This method is used to perform a batch-update for the Data_Fields that were
     * changed from the front-end.
     * 
     * @param df
     * @return of type List<DataField> representing the data fields that were
     *         changed.
     */
    public List<DBDataField> updateDataFieldsForRegistration(List<FieldUpdateRequest> df, UUID registration_id) {
        String query = "UPDATE T_Data_Field\n" +
                "SET content = \n" +
                "CASE field_id \n";
        for (FieldUpdateRequest dataField : df) {
            query += "WHEN '" + dataField.getField_id() + "' THEN '" + dataField.getContent() + "' \n";
        }
        query += "END \nWHERE registration_id = '" + registration_id + "' \nRETURNING *;";
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(query)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.execute();
            ResultSet rs = ps.getResultSet();

            return parseDBDataFieldsToList(rs);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method used to validate batch update and batch insert.
     * 
     * @param registration_id
     * @return
     */
    public int validateListCountFormComponent(UUID registration_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_VALIDATE_COUNT_FORMCOMPONENTS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, registration_id);
            ps.execute();
            ResultSet result = ps.getResultSet();
            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("could not validate count of form components for registration id: " + registration_id);
                return -1;
            }

            return result.getInt(1);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return -1;
        }
    }

    /**
     * This method is used to save the registration data fields when it is created
     * for the first time.
     * 
     * @param df
     * @return
     */
    public List<DBDataField> saveDataFields(List<FieldCreationRequest> df) {
        String query = "INSERT INTO T_Data_Field(field_id, registration_id, component_id, content) \n";
        query += valueBuilder(df) + " RETURNING *;";
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(query)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            ps.execute();
            ResultSet rs = ps.getResultSet();

            return parseDBDataFieldsToList(rs);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method is used to create the query lines for adding values.
     * 
     * @param additions of type DataFieldAddition.
     * @return
     */
    public String valueBuilder(List<FieldCreationRequest> additions) {
        String returnString = "VALUES \n";
        for (int i = 0; i < additions.size(); i++) {
            FieldCreationRequest ad = additions.get(i);
            returnString += "('" + UUID.randomUUID() + "', '" + ad.getRegistration_id() + "', '" + ad.getComponent_id()
                    + "', '" + ad.getContent() + "')";
            if (i != additions.size() - 1) {
                returnString += ",\n";
            }
            returnString += " \n";
        }
        return returnString;
    }

    /**
     * This method is used to create the List of ModificationListView to be sent to
     * the front-end.
     * 
     * @param registration_id of type UUID.
     * @return
     */
    public List<ModificationListView> loadModificationsForRegistration(UUID registration_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_GET_MODIFICATIONS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, registration_id);
            ps.execute();
            ResultSet result = ps.getResultSet();

            return parseModifications(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method is used for returning the modifications that are for a parent,
     * meaning that they are visible.
     * 
     * @param registration_id
     * @return
     */
    public List<ModificationListView> loadModificationsForParent(UUID registration_id) {
        List<ModificationListView> list = loadModificationsForRegistration(registration_id);
        List<ModificationListView> returnList = list.stream().filter(mod -> {
            return mod.isVisible();
        }).collect(Collectors.toList());
        return returnList;
    }

    /**
     * Method used to save the modification when a school administrator makes it.
     * 
     * @param sa_id
     * @param reg_id
     * @param description
     * @param visible
     * @return of type Modification.
     */
    public Modification saveModification(UUID sa_id, UUID reg_id, String description, boolean visible) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD)) {
            String query = "INSERT INTO T_MODIFICATION (mod_id, sa_id, reg_id, description, date, visible) \n" +
                    "VALUES(?, ?, ?, ?, ?, ?) \n " +
                    "RETURNING *;";
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            PreparedStatement ps = connection.prepareStatement(query);
            ps.setObject(1, UUID.randomUUID());
            ps.setObject(2, sa_id);
            ps.setObject(3, reg_id);
            ps.setString(4, description);
            ps.setObject(5, new Date(System.currentTimeMillis()));
            ps.setBoolean(6, visible);
            ps.execute();
            ResultSet result = ps.getResultSet();

            if (!result.next()) {
                LoggerManager.DAO_LOGGER.warning("could not save modification for registration id: " + reg_id);
                return null;
            }

            return parseDBModification(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method used to retrieve the style for a particular Registration.
     * 
     * @param reg_form_id
     * @return
     */
    public Style getStyle(UUID reg_form_id) {
        Style style = null;
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement ps = connection.prepareStatement(S_GET_STYLE)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            ps.setObject(1, reg_form_id);
            ps.execute();
            ResultSet result = ps.getResultSet();
            if (!result.next()) {
                LoggerManager.DAO_LOGGER.warning("could not find style for registration id: " + reg_form_id);
                return null;
            }

            style = StyleParser.parseStyle(result);
            System.out.println("Returning Style: " + style.getSection_font_color() + ", "
                    + style.getBackground_color() + ", " + style.getForm_component_font_color());
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }

        return style;
    }

    @Override
    public Connection requestConnection() {
        return null;
    }
}
