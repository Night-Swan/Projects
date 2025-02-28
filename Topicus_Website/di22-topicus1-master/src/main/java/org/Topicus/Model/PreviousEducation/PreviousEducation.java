package org.Topicus.Model.PreviousEducation;

import java.util.UUID;

/**
 * Unused class, would have been good to implement a standard, but was aborted as schools can request such details extensively
 * with the Registration Form Builder.
 */
public class PreviousEducation {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID previousEducationID;
    private UUID childID;
    private String address;
    private String institutionName;
    private String type;
    private String phoneNumber;
    private int duration;
    private String description;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------
    public PreviousEducation(UUID previousEducationID, UUID childID, String address, String institutionName, String type, String phoneNumber, int duration, String description) {
        this.previousEducationID = previousEducationID;
        this.childID = childID;
        this.address = address;
        this.institutionName = institutionName;
        this.type = type;
        this.phoneNumber = phoneNumber;
        this.duration = duration;
        this.description = description;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------
    public UUID getPreviousEducationID() {
        return previousEducationID;
    }

    public void setPreviousEducationID(UUID previousEducationID) {
        this.previousEducationID = previousEducationID;
    }

    public UUID getChildID() {
        return childID;
    }

    public void setChildID(UUID childID) {
        this.childID = childID;
    }

    public String getAddress() {
        return address;
    }

    public void setAddress(String address) {
        this.address = address;
    }

    public String getInstitutionName() {
        return institutionName;
    }

    public void setInstitutionName(String institutionName) {
        this.institutionName = institutionName;
    }

    public String getType() {
        return type;
    }

    public void setType(String type) {
        this.type = type;
    }

    public String getPhoneNumber() {
        return phoneNumber;
    }

    public void setPhoneNumber(String phoneNumber) {
        this.phoneNumber = phoneNumber;
    }

    public int getDuration() {
        return duration;
    }

    public void setDuration(int duration) {
        this.duration = duration;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }
}
