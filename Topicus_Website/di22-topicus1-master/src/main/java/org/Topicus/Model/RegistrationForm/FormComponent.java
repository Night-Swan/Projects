package org.Topicus.Model.RegistrationForm;

import java.util.UUID;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class FormComponent {
    // FIELD VARIABLE(S) ---------------------------------------------
    private UUID component_id;
    private UUID registration_form_id;
    private UUID section_id;
    private int position;
    private String title;
    private boolean mandatory;
    private DataType data_type;

    // CONSTRUCTOR(S) ---------------------------------------------

    /**
     * Default FormComponent constructor.
     */
    public FormComponent() {

    }

    /**
     * Constructor for a form component received from the database, fully specified.
     * 
     * @param component_id         The ID of this component.
     * @param registration_form_id The ID of the registration form this component
     *                             belongs to.
     * @param section_id           The ID of the section this component belongs to.
     * @param position             The position of this component in the section.
     * @param title                The title of this component.
     * @param mandatory            Whether this component is mandatory.
     * @param data_type            The data type of this component.
     */
    @JsonCreator
    public FormComponent(@JsonProperty("component_id") UUID component_id,
            @JsonProperty("registration_form_id") UUID registration_form_id,
            @JsonProperty("section_id") UUID section_id,
            @JsonProperty("position") int position,
            @JsonProperty("title") String title,
            @JsonProperty("mandatory") boolean mandatory,
            @JsonProperty("data_type") DataType data_type) {
        this.component_id = component_id;
        this.registration_form_id = registration_form_id;
        this.section_id = section_id;
        this.position = position;
        this.title = title;
        this.mandatory = mandatory;
        this.data_type = data_type;
    }

    /**
     * Constructor for a form component received from the front-end.
     * 
     * @param position             The position of this component in the section.
     * @param title                The title of this component.
     * @param mandatory            Whether this component is mandatory.
     * @param data_type            The data type of this component.
     */
    public FormComponent(int position, String title, boolean mandatory,
            DataType data_type) {
        this.position = position;
        this.title = title;
        this.mandatory = mandatory;
        this.data_type = data_type;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------
    public UUID getComponent_id() {
        return component_id;
    }

    public void setComponent_id(UUID component_id) {
        this.component_id = component_id;
    }

    public UUID getRegistration_form_id() {
        return registration_form_id;
    }

    public void setRegistration_form_id(UUID registration_form_id) {
        this.registration_form_id = registration_form_id;
    }

    public UUID getSection_id() {
        return section_id;
    }

    public void setSection_id(UUID section_id) {
        this.section_id = section_id;
    }

    public int getPosition() {
        return position;
    }

    public void setPosition(int position) {
        this.position = position;
    }

    public String getTitle() {
        return title;
    }

    public void setTitle(String title) {
        this.title = title;
    }

    public boolean isMandatory() {
        return mandatory;
    }

    public void setMandatory(boolean mandatory) {
        this.mandatory = mandatory;
    }

    public DataType getData_type() {
        return data_type;
    }

    public void setData_type(DataType data_type) {
        this.data_type = data_type;
    }
}
