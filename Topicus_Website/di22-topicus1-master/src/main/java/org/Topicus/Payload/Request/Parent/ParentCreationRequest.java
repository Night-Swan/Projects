package org.Topicus.Payload.Request.Parent;

import jakarta.xml.bind.annotation.XmlRootElement;
import org.Topicus.Utility.Parsers.DateParser;
import org.Topicus.Utility.Parsers.ListParser;
import org.Topicus.Utility.Parsers.UUIDParser;

import java.util.Date;
import java.util.List;
import java.util.UUID;

@XmlRootElement
public class ParentCreationRequest implements ListParser, DateParser, UUIDParser {
    // FIELD VARIABLE(S)
    // -----------------------------------------------------------------------------------------
    private UUID account_id;
    private UUID address_id;
    private String nationality;
    private String surname;
    private List<String> given_names;
    private String phone_number;
    private Date birth_date;
    private String occupation;
    private String company_name;
    // CONSTRUCTOR(S)
    // --------------------------------------------------------------------------------------------

    public ParentCreationRequest(UUID address_id, String nationality, String surname,
                                 List<String> given_names, String phone_number, Date birth_date, String occupation, String company_name) {
        this(null, address_id, nationality, surname, given_names, phone_number, birth_date, occupation, company_name);
    }

    public ParentCreationRequest(UUID account_id, UUID address_id, String nationality, String surname,
                                 List<String> given_names, String phone_number, Date birth_date, String occupation, String company_name) {
        this.account_id = account_id;
        this.address_id = address_id;
        this.nationality = nationality;
        this.surname = surname;
        this.given_names = given_names;
        this.phone_number = phone_number;
        this.birth_date = birth_date;
        this.occupation = occupation;
        this.company_name = company_name;
    }

    public ParentCreationRequest() {

    }

    // GETTER(S) --------------------------------------------------

    public UUID getAccount_id() {
        return account_id;
    }

    public UUID getAddress_id() {
        return address_id;
    }

    public String getNationality() {
        return nationality;
    }

    public String getSurname() {
        return surname;
    }

    public List<String> getGiven_names() {
        return given_names;
    }

    public String getPhone_number() {
        return phone_number;
    }

    public Date getBirth_date() {
        return birth_date;
    }

    public String getOccupation() {
        return occupation;
    }

    public String getCompany_name() {
        return company_name;
    }

    public void setAccount_id(UUID account_id) {
        this.account_id = account_id;
    }
}
