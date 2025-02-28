package org.Topicus.Model.Child;

import jakarta.xml.bind.annotation.XmlRootElement;

import java.util.Date;
import java.util.List;
import java.util.UUID;

@XmlRootElement
public class Child {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID childID;
    private String surname;
    private List<String> givenNames;
    private String preferredName;
    private Date birthDate;
    private String bsn;
    private String nationality;
    private List<String> languages;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------

    /**
     * Default Child Constructor
     */
    public Child() {

    }

    /**
     * Constructor for creating a new Child to be received from the database
     * @param childID
     * @param surname  
     * @param givenNames
     * @param preferredName
     * @param birthDate
     * @param bsn
     * @param nationality
     * @param languages
     */
    public Child(UUID childID, String surname, List<String> givenNames, String preferredName, Date birthDate, String bsn, String nationality, List<String> languages) {
        this(surname, givenNames, preferredName, birthDate, bsn, nationality, languages);
        this.childID = childID;
    }

    /**
     * Constructor for creating a new Child received from the front-end
     * @param surname
     * @param givenNames
     * @param preferredName
     * @param birthDate
     * @param bsn
     * @param nationality
     * @param languages
     */
    public Child(String surname, List<String> givenNames, String preferredName, Date birthDate, String bsn, String nationality, List<String> languages) {
        this.surname = surname;
        this.givenNames = givenNames;
        this.preferredName = preferredName;
        this.birthDate = birthDate;
        this.bsn = bsn;
        this.nationality = nationality;
        this.languages = languages;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------

    public UUID getChildID() {
        return childID;
    }

    public void setChildID(UUID childID) {
        this.childID = childID;
    }

    public String getSurname() {
        return surname;
    }

    public void setSurname(String surname) {
        this.surname = surname;
    }

    public List<String> getGivenNames() {
        return givenNames;
    }

    public void setGivenNames(List<String> givenNames) {
        this.givenNames = givenNames;
    }

    public String getPreferredName() {
        return preferredName;
    }

    public void setPreferredName(String preferredName) {
        this.preferredName = preferredName;
    }

    public Date getBirthDate() {
        return birthDate;
    }

    public void setBirthDate(Date birthDate) {
        this.birthDate = birthDate;
    }

    public String getBsn() {
        return bsn;
    }

    public void setBsn(String bsn) {
        this.bsn = bsn;
    }

    public String getNationality() {
        return nationality;
    }

    public void setNationality(String nationality) {
        this.nationality = nationality;
    }

    public List<String> getLanguages() {
        return languages;
    }

    public void setLanguages(List<String> languages) {
        this.languages = languages;
    }
}
