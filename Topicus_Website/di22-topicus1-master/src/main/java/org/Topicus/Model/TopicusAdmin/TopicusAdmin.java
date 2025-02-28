package org.Topicus.Model.TopicusAdmin;

import java.util.Date;
import java.util.List;
import java.util.UUID;

public class TopicusAdmin {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID adminID;
    private String surname;
    private String phoneNumber;
    private Date birthDate;
    private List<String> givenNames;
    private UUID employeeID;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------
    public TopicusAdmin(UUID adminID, String surname, String phoneNumber, Date birthDate, List<String> givenNames, UUID employeeID) {
        this.adminID = adminID;
        this.surname = surname;
        this.phoneNumber = phoneNumber;
        this.birthDate = birthDate;
        this.givenNames = givenNames;
        this.employeeID = employeeID;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------
    public UUID getAdminID() {
        return adminID;
    }

    public void setAdminID(UUID adminID) {
        this.adminID = adminID;
    }

    public String getSurname() {
        return surname;
    }

    public void setSurname(String surname) {
        this.surname = surname;
    }

    public String getPhoneNumber() {
        return phoneNumber;
    }

    public void setPhoneNumber(String phoneNumber) {
        this.phoneNumber = phoneNumber;
    }

    public Date getBirthDate() {
        return birthDate;
    }

    public void setBirthDate(Date birthDate) {
        this.birthDate = birthDate;
    }

    public List<String> getGivenNames() {
        return givenNames;
    }

    public void setGivenNames(List<String> givenNames) {
        this.givenNames = givenNames;
    }

    public UUID getEmployeeID() {
        return employeeID;
    }

    public void setEmployeeID(UUID employeeID) {
        this.employeeID = employeeID;
    }
}
