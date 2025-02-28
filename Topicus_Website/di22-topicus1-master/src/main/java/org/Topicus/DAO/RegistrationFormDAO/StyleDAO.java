package org.Topicus.DAO.RegistrationFormDAO;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.Contract.DAO;
import org.Topicus.Model.RegistrationForm.Style.Style;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.StyleParser;

public enum StyleDAO implements DAO<Style> {
    instance;

    private final static String GET_STYLE_FOR_FORM = "SELECT * FROM t_style WHERE registration_form_id = ?";

    private final static String INSERT_STYLE = "INSERT INTO t_style (registration_form_id, section_font_color, form_component_font_color, background_color, logo) VALUES (?, ?, ?, ?, ?) RETURNING *";

    private final static String UPDATE_STYLE = "UPDATE t_style SET registration_form_id = ?, section_font_color = ?, form_component_font_color = ?, background_color = ?, logo = ? WHERE registration_form_id = ? RETURNING *";

    private final static String DELETE_STYLE = "DELETE FROM t_style WHERE registration_form_id = ?";

    /**
     * Method to return singleton instance of DAO class.
     * 
     * @return of type StyleDAO
     */
    public static StyleDAO getInstance() {
        return instance;
    }

    @Override
    public Style get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(GET_STYLE_FOR_FORM)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();

            ResultSet result = preparedStatement.getResultSet();

            if (!result.next()) {
                return null;
            }

            return StyleParser.parseStyle(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    @Override
    public List<Style> getAll() {
        LoggerManager.DAO_LOGGER.warning("getAll() is not supposed to be called on StyleDAO");
        return null;
    }

    public Style updateRecord(Style style, String modifyQuery, boolean is_update) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(modifyQuery)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, style.getRegistration_form_id());
            preparedStatement.setString(2, style.getSection_font_color());
            preparedStatement.setString(3, style.getForm_component_font_color());
            preparedStatement.setString(4, style.getBackground_color());
            preparedStatement.setBytes(5, style.getLogo());
            if (is_update) {
                preparedStatement.setObject(6, style.getRegistration_form_id());
            }

            preparedStatement.execute();

            ResultSet result = preparedStatement.getResultSet();

            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("no style record was updated for form id: " + style.getRegistration_form_id());
                return null;
            }

            return StyleParser.parseStyle(result);
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to insert a new record into the database.
     * 
     * @param style of type Style
     * @return of type Style
     */
    @Override
    public Style save(Style style) {

        if (get(style.getRegistration_form_id()) != null) {
            LoggerManager.DAO_LOGGER.warning("style with id " + style.getRegistration_form_id() + " already exists");
            return null;
        }

        return updateRecord(style, INSERT_STYLE, false);
    }

    /**
     * Method to update an existing record in the database.
     * 
     * @param style of type Style
     * @return of type Style
     */
    @Override
    public Style update(Style style) {

        if (get(style.getRegistration_form_id()) == null) {
            LoggerManager.DAO_LOGGER.warning("style with id " + style.getRegistration_form_id() + " does not exist");
            return null;
        }

        return updateRecord(style, UPDATE_STYLE, true);
    }

    @Override
    public void delete(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_STYLE)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, id);

            preparedStatement.execute();
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    @Override
    public Connection requestConnection() {
        LoggerManager.DAO_LOGGER.warning("requestConnection() is not supposed to be called on StyleDAO");
        return null;
    }

}
