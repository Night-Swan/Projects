package org.Topicus.Utility.Parsers;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.UUID;

import org.Topicus.Model.RegistrationForm.Style.Style;

public interface StyleParser {
    static Style parseStyle(ResultSet result) throws SQLException {
        UUID registration_form_id = result.getObject("registration_form_id", UUID.class);
        String section_font_color = result.getString("section_font_color");
        String form_component_font_color = result.getString("form_component_font_color");
        String background_color = result.getString("background_color");
        System.out.println("Before bytes");
        byte[] logo = result.getBytes("logo");
        System.out.println("After bytes");
        return new Style(registration_form_id, section_font_color, form_component_font_color, background_color, logo);
    }

}
