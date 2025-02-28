package org.Topicus.Payload.Response.Registration;

import java.util.UUID;

import org.Topicus.Model.Registration.Status;
import org.Topicus.Utility.Logs.LoggerManager;

/**
 * Used for the view of Registrations on the front-end in a list format.
 */
public class RegistrationView {
    // FIELD VARIABLE(S) ----------------------------------------------------
    private Status status;
    private UUID registration_id;
    private UUID school_id;
    private String guardian_name;
    private String child_name;
    private UUID guardian_id;
    private UUID child_id;
    private String school_name;
    private String formTitle;
    private int formYear;

    // CONSTRUCTOR(S) ------------------------------------------------
    /**
     * Used to instantiate object which will serve as the list view for the
     * front-end. Fields are self-explanatory.
     * 
     * @param registration_id
     * @param school_id
     * @param guardian_name
     * @param child_name
     * @param guardian_id
     * @param child_id
     * @param school_name
     */
    public RegistrationView(String status, UUID registration_id, UUID school_id, String guardian_name,
            String child_name, UUID guardian_id, UUID child_id, String school_name, String formTitle, int formYear) {
        try {
            this.status = Status.valueOf(status);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.status + " is not a valid Status");
            this.status = Status.UNAVAILABLE_ERROR;
        }
        this.registration_id = registration_id;
        this.school_id = school_id;
        this.guardian_name = guardian_name;
        this.child_name = child_name;
        this.guardian_id = guardian_id;
        this.child_id = child_id;
        this.school_name = school_name;
        this.formTitle = formTitle;
        this.formYear = formYear;
    }

    // METHOD(S) -----------------------------------------------------------

    public Status getStatus() {
        return status;
    }

    public UUID getRegistration_id() {
        return registration_id;
    }

    public UUID getSchool_id() {
        return school_id;
    }

    public String getGuardian_name() {
        return guardian_name;
    }

    public String getChild_name() {
        return child_name;
    }

    public UUID getGuardian_id() {
        return guardian_id;
    }

    public UUID getChild_id() {
        return child_id;
    }

    public String getSchool_name() {
        return school_name;
    }

    public String getFormTitle() {
        return formTitle;
    }

    public int getFormYear() {
        return formYear;
    }
}
