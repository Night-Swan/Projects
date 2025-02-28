package org.Topicus.Payload.Response.SchoolAdmin;

import java.util.Date;
import java.util.List;
import java.util.UUID;

import org.Topicus.Model.SystemUser.UserType;

public class SchoolAdminDetails {
    // FIELDS------------------------------------------------------------------------------------------------------------
    private UUID adminID;
    private UserType type;
    private String username;
    private String email;
    private String surname;
    private String phoneNumber;
    private Date birthDate;
    private List<String> givenNames;
    private UUID schoolID;
    private String employeeID;

    // CONSTRUCTORS------------------------------------------------------------------------------------------------------

    public SchoolAdminDetails(UUID adminID, UserType type, String username, String email, String surname,
            String phoneNumber, Date birthDate, List<String> givenNames, UUID schoolID, String employeeID) {
        this.adminID = adminID;
        this.type = type;
        this.username = username;
        this.email = email;
        this.surname = surname;
        this.phoneNumber = phoneNumber;
        this.birthDate = birthDate;
        this.givenNames = givenNames;
        this.schoolID = schoolID;
        this.employeeID = employeeID;
    }

    // GETTERS-----------------------------------------------------------------------------------------------------------

    public UUID getAdminID() {
        return adminID;
    }

    public UserType getType() {
        return type;
    }

    public String getUsername() {
        return username;
    }

    public String getEmail() {
        return email;
    }

    public String getSurname() {
        return surname;
    }

    public String getPhoneNumber() {
        return phoneNumber;
    }

    public Date getBirthDate() {
        return birthDate;
    }

    public List<String> getGivenNames() {
        return givenNames;
    }

    public String getEmployeeID() {
        return employeeID;
    }

    public UUID getSchoolID() {
        return schoolID;
    }

}
