package org.Topicus.Model.RegistrationForm;

import java.sql.Date;
import java.util.UUID;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class RegistrationFormMetadata {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID registration_form_id;
    private UUID school_id;
    private String title;
    private String description;
    private int year;
    private String education_type;
    private boolean is_deleted;
    private boolean is_active;
    private Date start_date;

    /**
     * Default Constructor
     */
    public RegistrationFormMetadata() {

    }

    /**
     * Creates a new RegistrationFormMetadata object to be retrieved from the database.
     * 
     * @param registration_form_id The id of the registration form.
     * @param school_id            The id of the school the registration form
     *                             belongs to.
     * @param title                The title of the registration form.
     * @param description          The description of the registration form.
     * @param year                 The year of the registration form.
     * @param education_type       The education type of the registration form.
     * @param is_deleted           Whether the registration form is deleted.
     * @param is_active            Whether the registration form is active.
     * @param start_date           The start date of the registration form.
     */
    @JsonCreator
    public RegistrationFormMetadata(@JsonProperty("registration_form_id") UUID registration_form_id,
            @JsonProperty("school_id") UUID school_id,
            @JsonProperty("title") String title,
            @JsonProperty("description") String description,
            @JsonProperty("year") int year,
            @JsonProperty("education_type") String education_type,
            @JsonProperty("is_deleted") boolean is_deleted,
            @JsonProperty("is_active") boolean is_active,
            @JsonProperty("start_date") Date start_date) {
        this.registration_form_id = registration_form_id;
        this.school_id = school_id;
        this.title = title;
        this.description = description;
        this.year = year;
        this.education_type = education_type;
        this.is_deleted = is_deleted;
        this.is_active = is_active;
        this.start_date = start_date;
    }

    /**
     * Creates a new RegistrationFormMetadata object to be retrieved from the front-end.
     * 
     * @param school_id      The id of the school the registration form belongs to.
     * @param title          The title of the registration form.
     * @param description    The description of the registration form.
     * @param year           The year of the registration form.
     * @param education_type The education type of the registration form.
     * @param is_deleted     Whether the registration form is deleted.
     * @param is_active      Whether the registration form is active.
     * @param start_date     The start date of the registration form.
     */
    public RegistrationFormMetadata(UUID school_id, String title, String description, int year,
            String education_type, boolean is_deleted, boolean is_active, Date start_date) {
        this.school_id = school_id;
        this.title = title;
        this.description = description;
        this.year = year;
        this.education_type = education_type;
        this.is_deleted = is_deleted;
        this.is_active = is_active;
        this.start_date = start_date;
    }

    public UUID getRegistration_form_id() {
        return registration_form_id;
    }

    public void setRegistration_form_id(UUID registration_form_id) {
        this.registration_form_id = registration_form_id;
    }

    public UUID getSchool_id() {
        return school_id;
    }

    public void setSchool_id(UUID school_id) {
        this.school_id = school_id;
    }

    public String getTitle() {
        return title;
    }

    public void setTitle(String title) {
        this.title = title;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public int getYear() {
        return year;
    }

    public void setYear(int year) {
        this.year = year;
    }

    public String getEducation_type() {
        return education_type;
    }

    public void setEducation_type(String education_type) {
        this.education_type = education_type;
    }

    public boolean isIs_deleted() {
        return is_deleted;
    }

    public void setIs_deleted(boolean is_deleted) {
        this.is_deleted = is_deleted;
    }

    public boolean isIs_active() {
        return is_active;
    }

    public void setIs_active(boolean is_active) {
        this.is_active = is_active;
    }

    public Date getStart_date() {
        return start_date;
    }

    public void setStart_date(Date start_date) {
        this.start_date = start_date;
    }
}
