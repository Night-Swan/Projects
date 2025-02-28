package org.Topicus.Model.RegistrationForm.Style;

import java.util.UUID;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class Style {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID registration_form_id;

    private String section_font_color;

    private String form_component_font_color;

    private String background_color;

    private byte[] logo;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------
    /**
     * Default constructor
     */
    public Style() {

    }

    /**
     * Fully specified style constructor
     * 
     * @param registration_form_id
     * @param section_font_color
     * @param form_component_font_color
     * @param background_color
     * @param logo
     */
    public Style(UUID registration_form_id, String section_font_color, String form_component_font_color,
            String background_color, byte[] logo) {
        this(section_font_color, form_component_font_color, background_color, logo);
        this.registration_form_id = registration_form_id;
    }

    /**
     * Constructor for object received from front-end
     * 
     * @param section_font_color
     * @param form_component_font_color
     * @param background_color
     * @param logo
     */
    public Style(String section_font_color, String form_component_font_color, String background_color, byte[] logo) {
        this.section_font_color = section_font_color;
        this.form_component_font_color = form_component_font_color;
        this.background_color = background_color;
        this.logo = logo;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------
    public UUID getRegistration_form_id() {
        return registration_form_id;
    }

    public void setRegistration_form_id(UUID registration_form_id) {
        this.registration_form_id = registration_form_id;
    }

    public String getSection_font_color() {
        return section_font_color;
    }

    public void setSection_font_color(String section_font_color) {
        this.section_font_color = section_font_color;
    }

    public String getForm_component_font_color() {
        return form_component_font_color;
    }

    public void setForm_component_font_color(String form_component_font_color) {
        this.form_component_font_color = form_component_font_color;
    }

    public String getBackground_color() {
        return background_color;
    }

    public void setBackground_color(String background_color) {
        this.background_color = background_color;
    }

    public byte[] getLogo() {
        return logo;
    }

    public void setLogo(byte[] logo) {
        this.logo = logo;
    }
}
