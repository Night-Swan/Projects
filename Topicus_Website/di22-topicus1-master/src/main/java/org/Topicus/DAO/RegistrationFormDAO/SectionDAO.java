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
import org.Topicus.Model.RegistrationForm.Section;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.SectionParser;
import org.Topicus.Utility.Query.QueryUtils;

public enum SectionDAO implements DAO<Section> {
    instance;

    // QUERY(IES) ------------------------------------------
    private final static String GET_SECTION_BY_ID = "SELECT * FROM t_section WHERE section_id = ?";

    private final static String GET_SECTIONS_FOR_FORM = "SELECT * FROM t_section WHERE registration_form_id = ?";

    private final static String INSERT_SECTION = "INSERT INTO t_section(section_id, registration_form_id, position_number, title) VALUES(?, ?, ?, ?) RETURNING *";

    private final static String BULK_INSERT_SECTIONS = "INSERT INTO t_section(section_id, registration_form_id, position_number, title) VALUES ";

    private final static String UPDATE_SECTION = "UPDATE t_section SET section_id = ?, registration_form_id = ?, position_number = ?, title = ? WHERE section_id = ? RETURNING *";

    private final static String BULK_UPDATE_SECTIONS_FOR_FORM = "UPDATE t_section SET ";

    private final static String DELETE_SECTION = "DELETE FROM t_section WHERE section_id = ?";

    private final static String DELETE_ALL_SECTIONS_FOR_FORM = "DELETE FROM t_section WHERE registration_form_id = ?";

    private final static String DELETE_OLD_SECTIONS_FOR_FORM = "DELETE FROM t_section WHERE registration_form_id = ? AND section_id NOT IN ";

    // CONSTRUCTOR(S) --------------------------------------
    SectionDAO() {

    }

    // ACCESS METHOD(S) ------------------------------------

    /**
     * Method to return singleton instance of DAO class.
     * 
     * @return of type AccountDAO.
     */
    public static SectionDAO getInstance() {
        return instance;
    }

    // METHOD(S) ----------------------------------------------

    /**
     * Method to get a section based on an id.
     * 
     * @param id of type UUID.
     * @return of type Section.
     */
    @Override
    public Section get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_SECTION_BY_ID)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            if (!resultSet.next()) {
                return null;
            }

            Section section = SectionParser.parseSection(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("more than one section with id " + id);
            }

            return section;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to get all sections.
     * 
     * @return of type List<Section>.
     */
    @Override
    public List<Section> getAll() {
        return null; // WE DON'T NEED THIS
    }

    /**
     * Method to get all sections for a form.
     * 
     * @param form_id of type UUID.
     * @return of type List<Section>.
     */
    public List<Section> getAllSectionsForForm(UUID form_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_SECTIONS_FOR_FORM)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, form_id);
            ResultSet resultSet = preparedStatement.executeQuery();

            List<Section> sectionList = new ArrayList<>();
            while (resultSet.next()) {
                sectionList.add(SectionParser.parseSection(resultSet));
            }

            return sectionList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to update a Section record in the database(either insert or update).
     * 
     * @param section     of type Section.
     * @param modifyQuery of type String.
     * @return of type Section.
     */
    private Section updateRecord(Section section, String modifyQuery, boolean isUpdate) {

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(modifyQuery)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, section.getSection_id());
            preparedStatement.setObject(2, section.getRegistration_form_id());
            preparedStatement.setInt(3, section.getPosition_number());
            preparedStatement.setString(4, section.getTitle());
            if (isUpdate) {
                preparedStatement.setObject(5, section.getSection_id());
            }

            preparedStatement.execute();
            ResultSet result = preparedStatement.getResultSet();

            if (!result.next()) {
                LoggerManager.DAO_LOGGER.warning("no records were updated for section id: " + section.getSection_id());
                return null;
            }

            return SectionParser.parseSection(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for saving a section to the database.
     * 
     * @param section of type Section.
     * @return of type Section.
     */
    @Override
    public Section save(Section section) {
        section.setSection_id(UUID.randomUUID());

        if (get(section.getSection_id()) != null) {
            LoggerManager.DAO_LOGGER.warning("section with id " + section.getSection_id() + " already exists");
            return null;
        }

        return updateRecord(section, INSERT_SECTION, false);
    }

    /**
     * Method for updating a section in the database.
     * 
     * @param section of type Section.
     * @return of type Section.
     */
    @Override
    public Section update(Section section) {

        if (get(section.getSection_id()) == null) {
            LoggerManager.DAO_LOGGER.warning("section with id " + section.getSection_id() + " does not exist");
            return null;
        }

        return updateRecord(section, UPDATE_SECTION, true);
    }

    /**
     * Method for bulk creating sections for a form in the database.
     * 
     * @param sectionList of type List<Section>.
     * @return of type List<Section>.
     */
    public List<Section> bulkCreateSections(List<Section> sectionList) {
        String placeholders = QueryUtils.generateInsertPlaceholders(4, sectionList.size());
        String query = BULK_INSERT_SECTIONS + placeholders + " RETURNING *;";

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(query)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            int index = 1;
            for (Section section : sectionList) {
                preparedStatement.setObject(index++, section.getSection_id());
                preparedStatement.setObject(index++, section.getRegistration_form_id());
                preparedStatement.setInt(index++, section.getPosition_number());
                preparedStatement.setString(index++, section.getTitle());
            }

            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<Section> createdSectionList = new ArrayList<>();
            while (resultSet.next()) {
                createdSectionList.add(SectionParser.parseSection(resultSet));
            }

            return createdSectionList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for updating specific sections for a form in the database.
     * 
     * @param registrationFormID of type UUID.
     * @param sectionList        of type List<Section>.
     * @return of type List<Section>.
     */
    public List<Section> bulkUpdateSectionsForForm(UUID registrationFormID, List<Section> sectionList) {
        List<String> columnNames = new ArrayList<>();
        columnNames.add("registration_form_id");
        columnNames.add("position_number");
        columnNames.add("title");

        String query = BULK_UPDATE_SECTIONS_FOR_FORM + QueryUtils.generateUpdatePlaceholders("section_id",
                "registration_form_id", columnNames, sectionList.size());
        query += " RETURNING *;";
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(query)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);

            int index = 1;
            for (Section section : sectionList) {
                preparedStatement.setObject(index++, registrationFormID);
                preparedStatement.setInt(index++, section.getPosition_number());
                preparedStatement.setString(index++, section.getTitle());
            }

            preparedStatement.setObject(index, registrationFormID);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<Section> updatedSectionList = new ArrayList<>();
            while (resultSet.next()) {
                updatedSectionList.add(SectionParser.parseSection(resultSet));
            }

            return updatedSectionList;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Deletes the section with the given ID.
     * WARNING: This method also deletes all components associated with the section.
     * 
     * @param section_id
     */
    @Override
    public void delete(UUID section_id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_SECTION)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, section_id);
            int updateRowCount = preparedStatement.executeUpdate();
            if (updateRowCount != 1) {
                LoggerManager.DAO_LOGGER.warning(updateRowCount
                        + " rows were updated(out of 1) when trying to delete for section id: " + section_id);
                return;
            }

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    /**
     * Method for deleting all sections for a form
     * 
     * @param registrationFormID of type UUID.
     */
    public void deleteSectionsForForm(UUID registrationFormID) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_ALL_SECTIONS_FOR_FORM)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, registrationFormID);
            preparedStatement.execute();
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    /**
     * Method for deleting old sections
     * 
     * @param registrationFormID of type UUID.
     * @param sectionIdList      of type List<UUID>.
     */
    public void deleteOldSections(UUID registrationFormID, List<UUID> sectionIdList) {
        String query = DELETE_OLD_SECTIONS_FOR_FORM + QueryUtils.generateDeletePlaceholders(sectionIdList.size());

        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(query)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            int index = 1;
            preparedStatement.setObject(index++, registrationFormID);

            for (UUID sectionId : sectionIdList) {
                preparedStatement.setObject(index++, sectionId);
            }

            preparedStatement.execute();
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
