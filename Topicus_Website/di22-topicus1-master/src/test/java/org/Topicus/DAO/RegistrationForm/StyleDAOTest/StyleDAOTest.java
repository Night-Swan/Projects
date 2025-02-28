package org.Topicus.DAO.RegistrationForm.StyleDAOTest;

import org.Topicus.DAO.RegistrationFormDAO.StyleDAO;
import org.Topicus.Model.RegistrationForm.Style.Style;
import org.Topicus.Utility.Logs.LoggerManager;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.util.UUID;

import static org.junit.jupiter.api.Assertions.*;

public class StyleDAOTest {
    private static StyleDAO styleDAO;

    @BeforeAll
    public static void setup() {
        styleDAO = StyleDAO.getInstance();
        LoggerManager.configureLoggers();
    }

    @Test
    public void testSaveAndGet() {
        // Create a new style
        Style style = new Style();
        style.setRegistration_form_id(UUID.randomUUID());
        style.setSection_font_color("#000000");
        style.setForm_component_font_color("#ffffff");
        style.setBackground_color("0000ff");
        style.setLogo(new byte[]{1, 2, 3});

        // Save the style
        styleDAO.save(style);

        // Get the style
        Style retrievedStyle = styleDAO.get(style.getRegistration_form_id());

        // Assert that the retrieved style is not null
        assertNotNull(retrievedStyle);

        // Assert that the retrieved style has the same properties as the original style
        assertEquals(style.getRegistration_form_id(), retrievedStyle.getRegistration_form_id());
        assertEquals(style.getSection_font_color(), retrievedStyle.getSection_font_color());
        assertEquals(style.getForm_component_font_color(), retrievedStyle.getForm_component_font_color());
        assertEquals(style.getBackground_color(), retrievedStyle.getBackground_color());
        assertArrayEquals(style.getLogo(), retrievedStyle.getLogo());
    }

    @Test
    public void testUpdate() {
        // Create a new style
        Style style = new Style();
        style.setRegistration_form_id(UUID.randomUUID());
        style.setSection_font_color("#000000");
        style.setForm_component_font_color("#ffffff");
        style.setBackground_color("#0000ff");
        style.setLogo(new byte[]{1, 2, 3});

        // Save the style
        styleDAO.save(style);

        // Update the style
        style.setForm_component_font_color("yellow");
        style.setBackground_color("green");
        styleDAO.update(style);

        // Get the updated style
        Style retrievedStyle = styleDAO.get(style.getRegistration_form_id());

        // Assert that the retrieved style is not null
        assertNotNull(retrievedStyle);

        // Assert that the retrieved style has the updated properties
        assertEquals(style.getForm_component_font_color(), retrievedStyle.getForm_component_font_color());
        assertEquals(style.getBackground_color(), retrievedStyle.getBackground_color());
    }

    @Test
    public void testDelete() {
        // Create a new style
        Style style = new Style();
        style.setRegistration_form_id(UUID.randomUUID());
        style.setSection_font_color("black");
        style.setForm_component_font_color("white");
        style.setBackground_color("blue");
        style.setLogo(new byte[]{1, 2, 3});

        // Save the style
        styleDAO.save(style);

        // Delete the style
        styleDAO.delete(style.getRegistration_form_id());

        // Try to get the deleted style
        Style deletedStyle = styleDAO.get(style.getRegistration_form_id());

        // Assert that the deleted style is null
        assertNull(deletedStyle);
    }
}
