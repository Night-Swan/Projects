package org.Topicus.Payload.Request.School;

import java.util.UUID;

import org.Topicus.Utility.Parsers.UUIDParser;
import org.Topicus.Utility.Parsers.YearParser;

import com.fasterxml.jackson.annotation.JsonProperty;

import jakarta.xml.bind.annotation.XmlRootElement;

/**
 * This class is for saving a school
 */
@XmlRootElement
public class SchoolCreationRequest implements UUIDParser, YearParser {
    // FIELD VARIABLE(S)
    // -----------------------------------------------------------------------------------------------

    private UUID address_id;
    private String name;
    private String type;
    private String phone_number;
    private String email;

    // CONSTRUCTOR
    // -----------------------------------------------------------------------------------------------------

    /**
     * Default Constructor
     */
    public SchoolCreationRequest() {

    }

    /**
     * Creates a new school creation request, to be received from the front-end
     * 
     * @param address_id   the address id
     * @param name         the name
     * @param type         the type
     * @param phone_number the phone number
     * @param email        the email
     */
    public SchoolCreationRequest(@JsonProperty("address_id") UUID address_id,
            @JsonProperty("name") String name,
            @JsonProperty("type") String type,
            @JsonProperty("phone_number") String phone_number,
            @JsonProperty("email") String email) {
        this.address_id = address_id;
        this.name = name;
        this.type = type;
        this.phone_number = phone_number;
        this.email = email;
    }

    public UUID getAddress_id() {
        return address_id;
    }

    public void setAddress_id(UUID address_id) {
        this.address_id = address_id;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getType() {
        return type;
    }

    public void setType(String type) {
        this.type = type;
    }

    public String getPhone_number() {
        return phone_number;
    }

    public void setPhoneNumber(String phone_number) {
        this.phone_number = phone_number;
    }

    public String getEmail() {
        return email;
    }

    public void setEmail(String email) {
        this.email = email;
    }
}
