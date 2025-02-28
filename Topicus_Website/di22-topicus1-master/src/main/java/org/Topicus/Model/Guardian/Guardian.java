package org.Topicus.Model.Guardian;

import jakarta.xml.bind.annotation.XmlRootElement;

import java.util.Date;
import java.util.List;
import java.util.UUID;

@XmlRootElement
public class Guardian {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID guardian_id;
    private UUID account_id;
    private UUID address_id;
    private String nationality;
    private String surname;
    private List<String> given_names;
    private String phone_number;
    private Date date_of_birth;
    private String occupation;
    private String company_name;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------

    /**
     * Default Guardian Constructor
     */
    public Guardian() {

    }

    public Guardian(UUID guardian_id, UUID account_id, UUID address_id, String nationality, String surname,
            String phone_number, Date date_of_birth, List<String> given_names, String occupation,
            String company_name) {
        this(account_id, address_id, nationality, surname, phone_number, date_of_birth, given_names, occupation, company_name);
        this.guardian_id = guardian_id;
    }

    public Guardian(UUID account_id, UUID address_id, String nationality, String surname,
            String phone_number, Date date_of_birth, List<String> given_names, String occupation,
            String company_name) {
        this.account_id = account_id;
        this.address_id = address_id;
        this.nationality = nationality;
        this.surname = surname;
        this.given_names = given_names;
        this.phone_number = phone_number;
        this.date_of_birth = date_of_birth;
        this.occupation = occupation;
        this.company_name = company_name;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------

    public UUID getGuardian_id() {
        return guardian_id;
    }

    public void setGuardian_id(UUID guardian_id) {
        this.guardian_id = guardian_id;
    }

    public UUID getAccount_id() {
        return account_id;
    }

    public void setAccount_id(UUID account_id) {
        this.account_id = account_id;
    }

    public UUID getAddress_id() {
        return address_id;
    }

    public void setAddress_id(UUID address_id) {
        this.address_id = address_id;
    }

    public String getNationality() {
        return nationality;
    }

    public void setNationality(String nationality) {
        this.nationality = nationality;
    }

    public String getSurname() {
        return surname;
    }

    public void setSurname(String surname) {
        this.surname = surname;
    }

    public List<String> getGiven_names() {
        return given_names;
    }

    public void setGiven_names(List<String> given_names) {
        this.given_names = given_names;
    }

    public String getPhone_number() {
        return phone_number;
    }

    public void setPhone_number(String phone_number) {
        this.phone_number = phone_number;
    }

    public Date getDate_of_birth() {
        return date_of_birth;
    }

    public void setDate_of_birth(Date date_of_birth) {
        this.date_of_birth = date_of_birth;
    }

    public String getOccupation() {
        return occupation;
    }

    public void setOccupation(String occupation) {
        this.occupation = occupation;
    }

    public String getCompany_name() {
        return company_name;
    }

    public void setCompany_name(String company_name) {
        this.company_name = company_name;
    }
}
