package org.Topicus.Model.MedicalInformation;

import jakarta.xml.bind.annotation.XmlRootElement;

import java.util.UUID;

/**
 * Unused class, would have been a good addition to the application structure to have pre-defined fields but as things
 * stand, it is just left to encourage later development on these fronts.
 */
@XmlRootElement
public class MedicalInformation {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID childID;
    private String doctorName;
    private String phoneNumber;
    private String insuranceNumber;
    private String vaccinations;
    private String allergies;
    private String medicineRequired;
    private String chronicIllness;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------

    public MedicalInformation(UUID childID, String doctorName, String phoneNumber, String insuranceNumber, String vaccinations, String allergies, String medicineRequired, String chronicIllness) {
        this.childID = childID;
        this.doctorName = doctorName;
        this.phoneNumber = phoneNumber;
        this.insuranceNumber = insuranceNumber;
        this.vaccinations = vaccinations;
        this.allergies = allergies;
        this.medicineRequired = medicineRequired;
        this.chronicIllness = chronicIllness;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------

    public UUID getChildID() {
        return childID;
    }

    public void setChildID(UUID childID) {
        this.childID = childID;
    }

    public String getDoctorName() {
        return doctorName;
    }

    public void setDoctorName(String doctorName) {
        this.doctorName = doctorName;
    }

    public String getPhoneNumber() {
        return phoneNumber;
    }

    public void setPhoneNumber(String phoneNumber) {
        this.phoneNumber = phoneNumber;
    }

    public String getInsuranceNumber() {
        return insuranceNumber;
    }

    public void setInsuranceNumber(String insuranceNumber) {
        this.insuranceNumber = insuranceNumber;
    }

    public String getVaccinations() {
        return vaccinations;
    }

    public void setVaccinations(String vaccinations) {
        this.vaccinations = vaccinations;
    }

    public String getAllergies() {
        return allergies;
    }

    public void setAllergies(String allergies) {
        this.allergies = allergies;
    }

    public String getMedicineRequired() {
        return medicineRequired;
    }

    public void setMedicineRequired(String medicineRequired) {
        this.medicineRequired = medicineRequired;
    }

    public String getChronicIllness() {
        return chronicIllness;
    }

    public void setChronicIllness(String chronicIllness) {
        this.chronicIllness = chronicIllness;
    }
}
