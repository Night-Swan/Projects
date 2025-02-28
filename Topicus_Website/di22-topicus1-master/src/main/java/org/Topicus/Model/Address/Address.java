package org.Topicus.Model.Address;

import jakarta.xml.bind.annotation.XmlRootElement;

import java.util.UUID;
@XmlRootElement
public class Address {
    // FIELD VARIABLES -------------------------------------------------------------------------------------------------
    private UUID addressID;
    private String postalCode;
    private String streetName;
    private int streetNumber;
    private String city;
    private String country;
    private String phoneNumber;

    // CONSTRUCTOR(S) -------------------------------------------------------------------------------------------------
    /**
     * Default Address Constructor.
     */
    public Address() {

    }

    /**
     * Creates a new Address object, fully specified
     * @param addressID the ID of the address
     * @param postalCode the postal code of the address
     * @param streetName the street name of the address
     * @param streetNumber the street number of the address
     * @param city the city of the address
     * @param country the country of the address
     * @param phoneNumber the phone number of the address
     */
    public Address(UUID addressID, String postalCode, String streetName, int streetNumber, String city, String country, String phoneNumber) {
        this.addressID = addressID;
        this.postalCode = postalCode;
        this.streetName = streetName;
        this.streetNumber = streetNumber;
        this.city = city;
        this.country = country;
        this.phoneNumber = phoneNumber;
    }

    /**
     * Creates a new Address object, to be retrieved from the frontend
     * @param postalCode the postal code of the address
     * @param streetName the street name of the address
     * @param streetNumber the street number of the address
     * @param city the city of the address
     * @param country the country of the address
     * @param phoneNumber the phone number of the address
     */
    public Address(String postalCode, String streetName, int streetNumber, String city, String country, String phoneNumber) {
        this.postalCode = postalCode;
        this.streetName = streetName;
        this.streetNumber = streetNumber;
        this.city = city;
        this.country = country;
        this.phoneNumber = phoneNumber;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------

    public UUID getAddressID() {
        return addressID;
    }

    public void setAddressID(UUID addressID) {
        this.addressID = addressID;
    }

    public String getPostalCode() {
        return postalCode;
    }

    public void setPostalCode(String postalCode) {
        this.postalCode = postalCode;
    }

    public String getStreetName() {
        return streetName;
    }

    public void setStreetName(String streetName) {
        this.streetName = streetName;
    }

    public int getStreetNumber() {
        return streetNumber;
    }

    public void setStreetNumber(int streetNumber) {
        this.streetNumber = streetNumber;
    }

    public String getCity() {
        return city;
    }

    public void setCity(String city) {
        this.city = city;
    }

    public String getCountry() {
        return country;
    }

    public void setCountry(String country) {
        this.country = country;
    }

    public String getPhoneNumber() {
        return phoneNumber;
    }

    public void setPhoneNumber(String phoneNumber) {
        this.phoneNumber = phoneNumber;
    }
}
