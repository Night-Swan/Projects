package org.Topicus.Utility.Parsers;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Date;
import java.util.List;
import java.util.UUID;

import org.Topicus.Model.SchoolAdmin.SchoolAdmin;
import org.Topicus.Model.SystemUser.SystemUser;
import org.Topicus.Model.SystemUser.UserType;
import org.Topicus.Payload.Request.SystemUser.SystemUserCreationRequest;
import org.Topicus.Payload.Response.SchoolAdmin.SchoolAdminDetails;
import org.Topicus.Utility.Logs.LoggerManager;

public interface SystemUserParser {
    static SystemUser parseSystemUser(ResultSet rs) throws SQLException {
        UUID account_id = rs.getObject(1, UUID.class);
        UserType type = UserType.valueOf(rs.getString(2));
        String username = rs.getString(3);
        String email = rs.getString(4);
        String password = rs.getString(5);
        return new SystemUser(account_id, type, username, email, password);
    }

    static SystemUser parseSystemUserCreationRequest(SystemUserCreationRequest systemUserCreationRequest) {
        return new SystemUser(systemUserCreationRequest.getType(), systemUserCreationRequest.getUsername(),
                systemUserCreationRequest.getEmail(), systemUserCreationRequest.getPassword());
    }

    static SchoolAdmin parseSchoolAdmin(ResultSet rs) throws SQLException {
        UUID admin_id = rs.getObject(1, UUID.class);
        String surname = rs.getString(2);
        String phone_number = rs.getString(3);
        Date birthDate = getConvertedDate(rs.getDate(4));
        String given_names = rs.getString(5);
        List<String> names = given_names == null ? null : Arrays.asList(given_names.split(", "));
        UUID school_id = rs.getObject(6, UUID.class);
        String employeeID = rs.getString(7);
        return new SchoolAdmin(admin_id, surname,
                phone_number, birthDate, names, school_id, employeeID);

    }

    static SchoolAdmin parseSchoolAdminCreation(SchoolAdmin schoolAdmin) {
        return new SchoolAdmin(schoolAdmin.getAdminID(), schoolAdmin.getSurname(),
                schoolAdmin.getPhoneNumber(), schoolAdmin.getBirthDate(), schoolAdmin.getGivenNames(),
                schoolAdmin.getSchoolID(), schoolAdmin.getEmployeeID());
    }

    static SchoolAdminDetails parseSchoolAdminDetails(ResultSet rs) throws SQLException {
        UUID admin_id = rs.getObject(1, UUID.class);
        UserType type = UserType.valueOf(rs.getString(2));
        String username = rs.getString(3);
        String email = rs.getString(4);
        String surname = rs.getString(5);
        String phone_number = rs.getString(6);
        Date birthDate = getConvertedDate(rs.getDate(7));
        String given_names = rs.getString(8);
        List<String> names = given_names == null ? null : Arrays.asList(rs.getString(8).split(", "));
        UUID school_id = rs.getObject(9, UUID.class);
        String employeeID = rs.getString(10);
        // UUID employeeID = rs.getObject(9, UUID.class);
        return new SchoolAdminDetails(admin_id, type, username, email, surname,
                phone_number, birthDate, names, school_id, employeeID);

    }

    /**
     * convert a date into the right format and check it
     *
     * @param date_of_birth the date_of _birth from the database
     * @return the correct date
     */
    static Date getConvertedDate(Date date_of_birth) {
        if (date_of_birth == null) {
            return null;
        }
        Date date = null;
        SimpleDateFormat formatter1 = new SimpleDateFormat("yyyy-MM-dd");
        String dateString = formatter1.format(date_of_birth);
        try {
            date = formatter1.parse(dateString);
        } catch (ParseException e) {
            LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
        }

        return date;
    }
}
