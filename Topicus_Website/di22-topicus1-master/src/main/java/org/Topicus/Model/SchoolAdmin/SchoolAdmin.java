package org.Topicus.Model.SchoolAdmin;

import java.util.Date;
import java.util.List;
import java.util.UUID;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class SchoolAdmin {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID adminID;
    private String surname;
    private String phoneNumber;
    private Date birthDate;
    private List<String> givenNames;
    private UUID schoolID;
    private String employeeID;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------

    /**
     * Default constructor.
     */
    public SchoolAdmin() {

    }

    /**
     * Fully loaded constructor for DB to Front-end.
     * @param adminID
     * @param surname
     * @param phoneNumber
     * @param birthDate
     * @param givenNames
     * @param schoolID
     * @param employeeID
     */
    public SchoolAdmin(UUID adminID, String surname, String phoneNumber, Date birthDate, List<String> givenNames,
            UUID schoolID, String employeeID) {
        this.adminID = adminID;
        this.surname = surname;
        this.phoneNumber = phoneNumber;
        this.birthDate = birthDate;
        this.givenNames = givenNames;
        this.schoolID = schoolID;
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

    public UUID getSchoolID() {
        return schoolID;
    }

    public void setSchoolID(UUID schoolID) {
        this.schoolID = schoolID;
    }

    public String getEmployeeID() {
        return employeeID;
    }

    public void setEmployeeID(String employeeID) {
        this.employeeID = employeeID;
    }
}
