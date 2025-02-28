package org.Topicus.Model.School;

import java.util.UUID;

import com.fasterxml.jackson.annotation.JsonProperty;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class School {
    // FIELD VARIABLE(S) -----------------------------
    private UUID school_id;
    private UUID address_id;
    private String name;
    private String type;
    private String phone_number;
    private String email;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------

    /**
     * Default School Constructor
     */
    public School() {

    }

    /**
     * Creates a School, to be retrieved from the database, fully specified
     * 
     * @param school_id    the school id
     * @param address_id   the address id
     * @param name        the name
     * @param type        the type
     * @param phone_number the phone number
     * @param email       the email
     */
    public School(@JsonProperty("school_id") UUID school_id,
            @JsonProperty("address_id") UUID address_id,
            @JsonProperty("name") String name,
            @JsonProperty("type") String type,
            @JsonProperty("phone_number") String phone_number,
            @JsonProperty("email") String email) {
        this.school_id = school_id;
        this.address_id = address_id;
        this.name = name;
        this.type = type;
        this.phone_number = phone_number;
        this.email = email;
    }

    /**
     * Creates a School to be received from the front-end
     * 
     * @param address_id   the address id
     * @param name        the name
     * @param type        the type
     * @param phone_number the phone number
     * @param email       the email
     */
    public School(UUID address_id, String name, String type, String phone_number, String email) {
        this.address_id = address_id;
        this.name = name;
        this.type = type;
        this.phone_number = phone_number;
        this.email = email;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------
    public UUID getSchool_id() {
        return school_id;
    }

    public void setSchool_id(UUID school_id) {
        this.school_id = school_id;
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

    public void setPhone_number(String phone_number) {
        this.phone_number = phone_number;
    }

    public String getEmail() {
        return email;
    }

    public void setEmail(String email) {
        this.email = email;
    }
}
