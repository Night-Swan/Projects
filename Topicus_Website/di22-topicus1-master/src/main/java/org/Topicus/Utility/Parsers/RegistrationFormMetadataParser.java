package org.Topicus.Utility.Parsers;

import java.sql.Date;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.UUID;

import org.Topicus.Model.RegistrationForm.RegistrationFormMetadata;

public interface RegistrationFormMetadataParser {
    static RegistrationFormMetadata parseFormMetadata(ResultSet resultSet) throws SQLException {
        UUID form_id = resultSet.getObject(1, UUID.class);
        UUID school_id = resultSet.getObject(2, UUID.class);
        String title = resultSet.getString(3);
        String description = resultSet.getString(4);
        int year = resultSet.getInt(5);
        String educationType = resultSet.getString(6);
        boolean isDeleted = resultSet.getBoolean(7);
        boolean isActive = resultSet.getBoolean(8);
        Date startDate = resultSet.getDate(9);

        return new RegistrationFormMetadata(form_id, school_id, title, description, year, educationType, isDeleted,
                isActive, startDate);
    }
}
