package org.Topicus.Utility.Parsers;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.UUID;

import org.Topicus.Model.RegistrationForm.Section;

public interface SectionParser {
    /**
     * Parses a section from a result set.
     * 
     * @param resultSet The result set to parse.
     * @return The parsed section.
     * @throws SQLException Thrown if the result set cannot be parsed.
     */
    static Section parseSection(ResultSet resultSet) throws SQLException {
        UUID section_id = resultSet.getObject(1, UUID.class);
        UUID registration_form_id = resultSet.getObject(2, UUID.class);
        int position = resultSet.getInt(3);
        String title = resultSet.getString(4);
        return new Section(section_id, registration_form_id, position, title);
    }
}
