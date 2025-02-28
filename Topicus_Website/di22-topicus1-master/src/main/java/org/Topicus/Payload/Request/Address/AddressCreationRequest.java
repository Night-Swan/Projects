package org.Topicus.Payload.Request.Address;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class AddressCreationRequest {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private String postalCode;
    private String streetName;
    private int streetNumber;
    private String city;
    private String country;
    private String phoneNumber;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------

    /**
     * Creates a new AddressCreationRequest object to be retrieved from the frontend
     * @param postalCode the postal code of the address
     * @param streetName the street name of the address
     * @param streetNumber the street number of the address
     * @param city the city of the address
     * @param country the country of the address
     * @param phoneNumber the phone number of the address
     */
    public AddressCreationRequest(String postalCode, String streetName, int streetNumber, String city, String country, String phoneNumber) {
        this.postalCode = postalCode;
        this.streetName = streetName;
        this.streetNumber = streetNumber;
        this.city = city;
        this.country = country;
        this.phoneNumber = phoneNumber;
    }

    /**
     * Creates a new empty AddressCreationRequest object
     */
    public AddressCreationRequest() {

    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------
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
