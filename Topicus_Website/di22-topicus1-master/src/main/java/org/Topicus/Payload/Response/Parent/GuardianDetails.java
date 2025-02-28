package org.Topicus.Payload.Response.Parent;

import java.util.Date;
import java.util.UUID;

public class GuardianDetails {
    private String email;
    private UUID guardian_id;
    private UUID account_id;
    private String nationality;
    private String surname;
    private String phone_number;
    private Date date_of_birth;
    private String given_names;
    private String occupation;
    private String company_name;

    public GuardianDetails(UUID account_id, UUID guardian_id, String email, String nationality, String surname,
                           String phone_number, Date date_of_birth,
                           String given_names, String occupation,
                           String company_name) {
        this.account_id = account_id;
        this.guardian_id = guardian_id;
        this.email = email;
        this.nationality = nationality;
        this.surname = surname;
        this.phone_number = phone_number;
        this.date_of_birth = date_of_birth;
        this.given_names = given_names;
        this.occupation = occupation;
        this.company_name = company_name;
    }

    public UUID getAccount_id() {
        return account_id;
    }

    public UUID getGuardian_id() {
        return guardian_id;
    }

    public String getSurname() {
        return surname;
    }

    public String getNationality() {
        return nationality;
    }

    public String getPhone_number() {
        return phone_number;
    }

    public Date getDate_of_birth() {
        return date_of_birth;
    }

    public String getGiven_names() {
        return given_names;
    }

    public String getOccupation() {
        return occupation;
    }

    public String getCompany_name() {
        return company_name;
    }

    public String getEmail() {
        return email;
    }
}
