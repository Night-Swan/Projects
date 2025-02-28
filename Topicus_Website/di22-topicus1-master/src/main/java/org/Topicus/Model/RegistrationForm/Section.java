package org.Topicus.Model.RegistrationForm;

import java.util.UUID;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class Section {
    // FIELD VARIABLE(S) ---------------------------------
    private UUID section_id;
    private UUID registration_form_id;
    private int position_number;
    private String title;

    // CONSTRUCTOR(S) ---------------------------------------------

    /**
     * Default Constructor
     */
    public Section() {

    }

    /**
     * Constructor for a section received from the database.
     * 
     * @param section_id
     * @param registration_form_id
     * @param position_number
     * @param title
     */
    @JsonCreator
    public Section(@JsonProperty("section_id") UUID section_id,
            @JsonProperty("registration_form_id") UUID registration_form_id,
            @JsonProperty("position_number") int position_number,
            @JsonProperty("title") String title) {
        this.section_id = section_id;
        this.registration_form_id = registration_form_id;
        this.position_number = position_number;
        this.title = title;
    }

    /**
     * Constructor for a section received from the front-end.
     * 
     * @param position_number
     * @param title
     */
    public Section(int position_number, String title) {
        this.position_number = position_number;
        this.title = title;
    }

    public UUID getSection_id() {
        return section_id;
    }

    public void setSection_id(UUID section_id) {
        this.section_id = section_id;
    }

    public UUID getRegistration_form_id() {
        return registration_form_id;
    }

    public void setRegistration_form_id(UUID registration_form_id) {
        this.registration_form_id = registration_form_id;
    }

    public int getPosition_number() {
        return position_number;
    }

    public void setPosition_number(int position_number) {
        this.position_number = position_number;
    }

    public String getTitle() {
        return title;
    }

    public void setTitle(String title) {
        this.title = title;
    }
}
