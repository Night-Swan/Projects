package org.Topicus.Utility.Parsers;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.UUID;

import org.Topicus.Model.RegistrationForm.DataType;
import org.Topicus.Model.RegistrationForm.FormComponent;

public interface FormComponentParser {
    static FormComponent parseComponent(ResultSet resultSet) throws SQLException {
        UUID component_id = resultSet.getObject(1, UUID.class);
        UUID registration_form_id = resultSet.getObject(2, UUID.class);
        UUID section_id = resultSet.getObject(3, UUID.class);
        int position = resultSet.getInt(4);
        String title = resultSet.getString(5);
        boolean mandatory = resultSet.getBoolean(6);
        String type = resultSet.getString(7);
        DataType dataType = type == null ? null : DataType.valueOf(type);

        return new FormComponent(component_id, registration_form_id, section_id, position, title, mandatory, dataType);
    }
}
