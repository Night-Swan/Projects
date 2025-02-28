package org.Topicus.Utility.Parsers;

import java.sql.Date;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

import org.Topicus.Model.Modification.Modification;
import org.Topicus.Model.Registration.DBDataField;
import org.Topicus.Model.Registration.FEDataField;
import org.Topicus.Model.Registration.Registration;
import org.Topicus.Model.Registration.Status;
import org.Topicus.Model.RegistrationForm.DataType;
import org.Topicus.Model.RegistrationForm.Section;
import org.Topicus.Payload.Response.Registration.ModificationListView;
import org.Topicus.Payload.Response.Registration.RegistrationView;
import org.Topicus.Utility.Logs.LoggerManager;

public interface RegistrationParser {
    String format = "yyyy-MM-dd";

    /**
     * Method is used to parse Registrations from the database to the back-end, to
     * be used as objects.
     * 
     * @param result of type ResultSet.
     * @return of type Registration.
     * @throws SQLException can be thrown.
     */
    default Registration parseRegistration(ResultSet result) throws SQLException {
        UUID registration_id = result.getObject(1, UUID.class);
        UUID guardian_id = result.getObject(2, UUID.class);
        UUID child_id = result.getObject(3, UUID.class);
        UUID school_id = result.getObject(4, UUID.class);
        UUID registration_form_id = result.getObject(5, UUID.class);
        String status = result.getString(6);
        // The methods to create registrations and update them will have the necessary
        // status validation.
        Status stat;
        try {
            stat = Status.valueOf(status);
        } catch (IllegalArgumentException e) {
            stat = null;
        }
        return new Registration(registration_id, guardian_id, child_id, school_id, registration_form_id, stat);
    }

    /**
     * Method is used to parse Registrations from the database to the back-end, into
     * a list.
     * 
     * @param result of type ResultSet.
     * @return of type List<Registration>.
     * @throws SQLException can be thrown.
     */
    default List<Registration> parseRegistrations(ResultSet result) throws SQLException {
        List<Registration> list = new ArrayList<>();
        while (result.next()) {
            list.add(parseRegistration(result));
        }
        return list;
    }

    /**
     * Method to parse RegistrationView from the back-end.
     * 
     * @param result of type ResultSet.
     * @return of type RegistrationView.
     * @throws SQLException can be thrown.
     */
    default RegistrationView parseRegistrationView(ResultSet result) throws SQLException {
        String status = result.getString(1);
        UUID registration_id = result.getObject(2, UUID.class);
        UUID school_id = result.getObject(3, UUID.class);
        String gname = result.getString(4);
        String cname = result.getString(5);
        UUID gid = result.getObject(6, UUID.class);
        UUID cid = result.getObject(7, UUID.class);
        String sname = result.getString(8);
        String formTitle = result.getString(9);
        int formYear = result.getInt(10);
        return new RegistrationView(status, registration_id, school_id, gname, cname, gid, cid, sname, formTitle,
                formYear);
    }

    /**
     * Method to parse RegistrationView to a list.
     * 
     * @param result of type ResultSet
     * @return List<RegistrationView>
     * @throws SQLException
     */
    default List<RegistrationView> parseRegistrationViews(ResultSet result) throws SQLException {
        List<RegistrationView> list = new ArrayList<>();
        while (result.next()) {
            list.add(parseRegistrationView(result));
        }
        return list;
    }

    /**
     * Method to parse Data Field.
     * 
     * @param result of type ResultSet.
     * @return List<DataField>
     * @throws SQLException
     */
    default FEDataField parseDataField(ResultSet result) throws SQLException {
        UUID field_id = result.getObject(1, UUID.class);
        UUID registration_id = result.getObject(2, UUID.class);
        UUID component_id = result.getObject(3, UUID.class);
        UUID section_id = result.getObject(4, UUID.class);
        String title = result.getString(5);
        String content = result.getString(6);
        int position_number = result.getInt(7);
        String m = result.getString(8);
        Boolean mandatory;

        try {
            mandatory = m != null && !m.isEmpty() && Boolean.parseBoolean(m);
        } catch (IllegalArgumentException e) {
            LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
            mandatory = false;
        }

        String dataType;

        try {
            String dt = result.getString(9);

            if (dt == null) {
                LoggerManager.UTILITY_LOGGER.warning("Data type is null for component id: " + component_id);
                dataType = null;
            } else {
                DataType dtype = DataType.valueOf(dt);
                dataType = dtype.getValue();
            }
        } catch (IllegalArgumentException e) {
            LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
            dataType = null;
        }

        return new FEDataField(field_id, registration_id, component_id, section_id, title, content, position_number,
                mandatory, dataType);
    }

    /**
     * Method to parse DataFields to a map, with position number.
     * 
     * @param result of type ResultSet.
     * @return Map<DataField, Integer>
     * @throws SQLException
     */
    default List<FEDataField> parseDataFields(ResultSet result) throws SQLException {
        List<FEDataField> dfs = new ArrayList<>();
        while (result.next()) {
            dfs.add(parseDataField(result));
        }
        return dfs;
    }

    /**
     * Method to parse DataFields to a list.
     * 
     * @param result of type ResultSet.
     * @return List<DataField>
     * @throws SQLException
     */
    default List<FEDataField> parseDataFieldsToList(ResultSet result) throws SQLException {
        List<FEDataField> returnList = new ArrayList<>();
        while (result.next()) {
            returnList.add(parseDataField(result));
        }
        return returnList;
    }

    /**
     * Method for parsing a DataField from the database.
     * 
     * @param result of type ResultSet
     * @return of type DBDataField
     * @throws SQLException
     */
    default DBDataField parseDBDataField(ResultSet result) throws SQLException {
        UUID field_id = result.getObject(1, UUID.class);
        UUID registration_id = result.getObject(2, UUID.class);
        UUID component_id = result.getObject(3, UUID.class);
        String content = result.getString(4);
        return new DBDataField(field_id, registration_id, component_id, content);
    }

    /**
     * Method for parsing database DataField.
     * 
     * @param result of type ResultSet.
     * @return of type List<DBDataField>
     * @throws SQLException
     */
    default List<DBDataField> parseDBDataFieldsToList(ResultSet result) throws SQLException {
        List<DBDataField> returnList = new ArrayList<>();
        while (result.next()) {
            returnList.add(parseDBDataField(result));
        }
        return returnList;
    }

    /**
     * Method to parse the Sections to a list.
     * 
     * @param result of type ResultSet
     * @return of type List<Section>.
     * @throws SQLException
     */
    default List<Section> parseSections(ResultSet result) throws SQLException {
        List<Section> resultList = new ArrayList<>();
        while (result.next()) {
            resultList.add(SectionParser.parseSection(result));
        }
        return resultList;
    }

    /**
     * Method used to parse the ModificationListView object.
     * 
     * @param result of type ResultSet.
     * @return of type ModificationListVIew
     * @throws SQLException
     */
    default ModificationListView parseModification(ResultSet result) throws SQLException {
        String date = result.getString(1);
        UUID sa_id = result.getObject(2, UUID.class);
        String surname = result.getString(3);
        UUID reg_id = result.getObject(4, UUID.class);
        String description = result.getString(5);
        boolean visibility = result.getBoolean(6);
        return new ModificationListView(date, sa_id, surname, reg_id, description, visibility);
    }

    /**
     * Method used to parse the ModificationListViews.
     * 
     * @param result of type ResultSet.
     * @return of type List<ModificationListView>
     * @throws SQLException
     */
    default List<ModificationListView> parseModifications(ResultSet result) throws SQLException {
        List<ModificationListView> resultList = new ArrayList<>();
        while (result.next()) {
            resultList.add(parseModification(result));
        }
        return resultList;
    }

    /**
     * Method used to parse the Modification from the DB.
     * 
     * @param result of type ResultSet.
     * @return of type Modification.
     * @throws SQLException
     */
    default Modification parseDBModification(ResultSet result) throws SQLException {
        UUID mod_id = result.getObject(1, UUID.class);
        UUID sa_id = result.getObject(2, UUID.class);
        UUID reg_id = result.getObject(3, UUID.class);
        String description = result.getString(4);
        Date date = Date.valueOf(result.getString(5));
        boolean visible = result.getBoolean(6);
        return new Modification(mod_id, sa_id, reg_id, description, date, visible);
    }
}
