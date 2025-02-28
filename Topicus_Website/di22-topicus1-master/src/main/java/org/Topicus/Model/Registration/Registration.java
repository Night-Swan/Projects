package org.Topicus.Model.Registration;

import jakarta.xml.bind.annotation.XmlRootElement;

import java.util.UUID;

@XmlRootElement
public class Registration {
    // FIELD VARIABLE(S) --------------------------------------------------------------------------------------
    private UUID registrationID;
    private UUID guardianID;
    private UUID childID;
    private UUID schoolID;
    private UUID registrationFormID;
    private Status status;

    // CONSTRUCTOR(S) ----------------------------------------------------------------------------------------------------------------
    /**
     * Used to create a Registration when parsing from back-end to front-end.
     * @param registrationID
     * @param guardianID
     * @param childID
     * @param schoolID
     * @param registrationFormID
     * @param status
     */
    public Registration(UUID registrationID, UUID guardianID, UUID childID, UUID schoolID, UUID registrationFormID, Status status) {
        this.registrationID = registrationID;
        this.guardianID = guardianID;
        this.childID = childID;
        this.schoolID = schoolID;
        this.registrationFormID = registrationFormID;
        this.status = status;
    }

    /**
     * Used to create an incomplete Registration that is to be saved to the database.
     * @param guardianID
     * @param childID
     * @param schoolID
     * @param registrationFormID
     * @param status
     */
    public Registration(UUID guardianID, UUID childID, UUID schoolID, UUID registrationFormID, Status status) {
        this.guardianID = guardianID;
        this.childID = childID;
        this.schoolID = schoolID;
        this.registrationFormID = registrationFormID;
        this.status = status;
    }

    // GETTER(S) ---------------------------------------------------------------------------------------------------------
    public UUID getRegistrationID() {
        return registrationID;
    }

    public UUID getGuardianID() {
        return guardianID;
    }

    public UUID getChildID() {
        return childID;
    }

    public UUID getSchoolID() {
        return schoolID;
    }

    public UUID getRegistrationFormID() {
        return registrationFormID;
    }

    public Status getStatus() {
        return status;
    }

    @Override
    public String toString() {
        return "rid: " + getRegistrationID() + " | gid: " + getGuardianID() + " | cid: " + getChildID() + " | sid: " + getSchoolID() + " | rfid: " + getRegistrationFormID() + " | " + getStatus();
    }
}
