package org.Topicus.Payload.Response.School;

import java.util.UUID;

public class SchoolDetails {
    //FIELDS------------------------------------------------------------------------------------------------------------
    private UUID school_id;
    private UUID address_id;
    private String name;
    private String type;
    private String phone_number;
    private String email;
    private String postalCode;
    private String streetName;
    private int streetNumber;
    private String city;
    private String country;
    private String phoneNumber;
    //CONSTRUCTOR-------------------------------------------------------------------------------------------------------

    public SchoolDetails(UUID school_id, UUID address_id, String name, String type, String phone_number, String email, String postalCode, String streetName, int streetNumber, String city, String country, String phoneNumber) {
        this.school_id = school_id;
        this.address_id = address_id;
        this.name = name;
        this.type = type;
        this.phone_number = phone_number;
        this.email = email;
        this.postalCode = postalCode;
        this.streetName = streetName;
        this.streetNumber = streetNumber;
        this.city = city;
        this.country = country;
        this.phoneNumber = phoneNumber;
    }


    //GETTERS-----------------------------------------------------------------------------------------------------------

    public UUID getSchool_id() {
        return school_id;
    }

    public UUID getAddress_id() {
        return address_id;
    }

    public String getName() {
        return name;
    }

    public String getType() {
        return type;
    }

    public String getPhone_number() {
        return phone_number;
    }

    public String getEmail() {
        return email;
    }

    public String getPostalCode() {
        return postalCode;
    }

    public String getStreetName() {
        return streetName;
    }

    public int getStreetNumber() {
        return streetNumber;
    }

    public String getCity() {
        return city;
    }

    public String getCountry() {
        return country;
    }

    public String getPhoneNumber() {
        return phoneNumber;
    }
}
