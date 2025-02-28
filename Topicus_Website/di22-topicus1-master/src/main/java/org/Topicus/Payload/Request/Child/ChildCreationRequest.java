package org.Topicus.Payload.Request.Child;

import java.util.Date;
import java.util.List;
import java.util.UUID;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class ChildCreationRequest {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID guardianId;
    private String surname;
    private List<String> givenNames;
    private String preferredName;
    private Date birthDate;
    private String bsn;
    private String nationality;
    private List<String> languages;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------
    public ChildCreationRequest(UUID guardianId, String surname, List<String> givenNames, String preferredName, Date birthDate, String bsn, String nationality, List<String> languages) {
        this.guardianId = guardianId;
        this.surname = surname;
        this.givenNames = givenNames;
        this.preferredName = preferredName;
        this.birthDate = birthDate;
        this.bsn = bsn;
        this.nationality = nationality;
        this.languages = languages;
    }

    public ChildCreationRequest() {

    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------
    public UUID getGuardianId() {
        return guardianId;
    }

    public String getSurname() {
        return surname;
    }

    public List<String> getGivenNames() {
        return givenNames;
    }

    public String getPreferredName() {
        return preferredName;
    }

    public Date getBirthDate() {
        return birthDate;
    }

    public String getBsn() {
        return bsn;
    }

    public String getNationality() {
        return nationality;
    }

    public List<String> getLanguages() {
        return languages;
    }
}
