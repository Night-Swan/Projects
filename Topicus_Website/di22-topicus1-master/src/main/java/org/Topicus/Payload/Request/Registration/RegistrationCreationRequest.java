package org.Topicus.Payload.Request.Registration;

import java.util.UUID;

import org.Topicus.Model.Registration.Status;
import org.Topicus.Utility.Logs.LoggerManager;

public class RegistrationCreationRequest {
    // FIELD VARIABLE(S)
    // -----------------------------------------------------------------------------------------
    private String guardianID;
    private String childID;
    private String schoolID;
    private String registrationFormID;
    private String status;
    boolean validRequest;

    // CONSTRUCTOR(S)
    // --------------------------------------------------------------------------------------------

    /**
     * Used by Front-End to create a Registration (requests the creation, back-end
     * performs creation).
     * 
     * @param guardianID
     * @param childID
     * @param schoolID
     * @param registrationFormID
     * @param status
     */
    public RegistrationCreationRequest(String guardianID, String childID, String schoolID, String registrationFormID,
            String status) {
        this.guardianID = guardianID;
        this.childID = childID;
        this.schoolID = schoolID;
        this.registrationFormID = registrationFormID;
        this.status = status;
    }

    public RegistrationCreationRequest() {

    }

    // GETTER(S) --------------------------------------------------

    public String getGuardianID() {
        return guardianID;
    }

    public UUID getConvertedGID() {
        try {
            return UUID.fromString(guardianID);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.guardianID + " is not a valid UUID");
            return null;
        }
    }

    public String getChildID() {
        return childID;
    }

    public UUID getConvertedCID() {
        try {
            return UUID.fromString(childID);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.childID + " is not a valid UUID");
            return null;
        }
    }

    public String getSchoolID() {
        return schoolID;
    }

    public UUID getConvertedSID() {
        try {
            return UUID.fromString(schoolID);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.schoolID + " is not a valid UUID");
            return null;
        }
    }

    public String getRegistrationFormID() {
        return registrationFormID;
    }

    public UUID getConvertedRegistrationFormID() {
        try {
            return UUID.fromString(registrationFormID);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.registrationFormID + " is not a valid UUID");
            return null;
        }
    }

    public String getStatus() {
        return this.status;
    }

    public Status getConvertedStatus() {
        try {
            return Status.valueOf(status);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.status + " is not a valid Status");
            return null;
        }
    }

    public boolean isValidRequest() {
        return (getConvertedGID() != null && getConvertedCID() != null && getConvertedSID() != null
                && getConvertedRegistrationFormID() != null);
    }

    @Override
    public String toString() {
        return "gid: " + getGuardianID() + " | cid: " + getChildID() + " | sid: " + getSchoolID() + " | rfid: "
                + getRegistrationFormID() + " | " + getStatus();
    }
}
