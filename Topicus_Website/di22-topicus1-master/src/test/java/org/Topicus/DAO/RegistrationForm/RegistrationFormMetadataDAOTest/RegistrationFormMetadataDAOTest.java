package org.Topicus.DAO.RegistrationForm.RegistrationFormMetadataDAOTest;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.sql.Date;
import java.util.UUID;

import org.Topicus.DAO.AddressDAO.AddressDAO;
import org.Topicus.DAO.RegistrationFormDAO.RegistrationFormMetadataDAO;
import org.Topicus.DAO.SchoolDAO.SchoolDAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Model.RegistrationForm.RegistrationFormMetadata;
import org.Topicus.Model.School.School;
import org.Topicus.Utility.Logs.LoggerManager;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

public class RegistrationFormMetadataDAOTest {
    private static RegistrationFormMetadataDAO registrationFormMetadataDAO;
    private static Address address;
    private static School school;

    @BeforeAll
    public static void setup() {
        registrationFormMetadataDAO = RegistrationFormMetadataDAO.getInstance();
        LoggerManager.configureLoggers();

        // create a new address
        address = new Address();
        address.setAddressID(UUID.randomUUID());
        address.setStreetName("Test Street");
        address.setStreetNumber(1);
        address.setPostalCode("1234AB");
        address.setCity("Test City");
        address.setCountry("Test Country");
        address.setPhoneNumber("+3106123456");

        // Save the address
        AddressDAO.getInstance().save(address);

        // Create a new school
        school = new School();
        school.setSchool_id(UUID.randomUUID());
        school.setAddress_id(address.getAddressID());
        school.setName("Test School");
        school.setType("Test Type");
        school.setPhone_number("+3106123456");
        school.setEmail("email@gmail.com");

        // Save the school
        SchoolDAO.getInstance().save(school);
    }

    @Test
    public void testSaveAndGet() {
        // Create a new registration form metadata
        RegistrationFormMetadata metadata = new RegistrationFormMetadata();
        metadata.setRegistration_form_id(UUID.randomUUID());
        metadata.setSchool_id(school.getSchool_id());
        metadata.setTitle("Registration Form");
        metadata.setDescription("Please fill out the form to register.");
        metadata.setYear(2023);
        metadata.setEducation_type("Primary");
        metadata.setIs_deleted(false);
        metadata.setIs_active(true);
        metadata.setStart_date(Date.valueOf("2023-06-27"));

        // Save the registration form metadata
        registrationFormMetadataDAO.save(metadata);

        // Get the registration form metadata
        RegistrationFormMetadata retrievedMetadata = registrationFormMetadataDAO
                .get(metadata.getRegistration_form_id());

        // Assert that the retrieved metadata is not null
        assertNotNull(retrievedMetadata);

        // Assert that the retrieved metadata has the same properties as the original
        // metadata
        assertEquals(metadata.getRegistration_form_id(), retrievedMetadata.getRegistration_form_id());
        assertEquals(metadata.getSchool_id(), retrievedMetadata.getSchool_id());
        assertEquals(metadata.getTitle(), retrievedMetadata.getTitle());
        assertEquals(metadata.getDescription(), retrievedMetadata.getDescription());
        assertEquals(metadata.getYear(), retrievedMetadata.getYear());
        assertEquals(metadata.getEducation_type(), retrievedMetadata.getEducation_type());
        assertEquals(metadata.isIs_deleted(), retrievedMetadata.isIs_deleted());
        assertEquals(metadata.isIs_active(), retrievedMetadata.isIs_active());
        assertEquals(metadata.getStart_date(), retrievedMetadata.getStart_date());
    }

    @Test
    public void testUpdate() {
        // Create a new registration form metadata
        RegistrationFormMetadata metadata = new RegistrationFormMetadata();
        metadata.setRegistration_form_id(UUID.randomUUID());
        metadata.setSchool_id(school.getSchool_id());
        metadata.setTitle("Registration Form");
        metadata.setDescription("Please fill out the form to register.");
        metadata.setYear(2023);
        metadata.setEducation_type("Primary");
        metadata.setIs_deleted(false);
        metadata.setIs_active(true);
        metadata.setStart_date(Date.valueOf("2023-06-27"));

        // Save the registration form metadata
        registrationFormMetadataDAO.save(metadata);

        // Update the registration form metadata
        metadata.setTitle("Updated Registration Form");
        metadata.setDescription("Please update the form.");
        registrationFormMetadataDAO.update(metadata);

        // Get the updated registration form metadata
        RegistrationFormMetadata retrievedMetadata = registrationFormMetadataDAO
                .get(metadata.getRegistration_form_id());

        // Assert that the retrieved metadata is not null
        assertNotNull(retrievedMetadata);

        // Assert that the retrieved metadata has the updated properties
        assertEquals(metadata.getTitle(), retrievedMetadata.getTitle());
        assertEquals(metadata.getDescription(), retrievedMetadata.getDescription());
    }

    @Test
    public void testDelete() {
        // Create a new registration form metadata
        RegistrationFormMetadata metadata = new RegistrationFormMetadata();
        metadata.setRegistration_form_id(UUID.randomUUID());
        metadata.setSchool_id(UUID.randomUUID());
        metadata.setTitle("Registration Form");
        metadata.setDescription("Please fill out the form to register.");
        metadata.setYear(2023);
        metadata.setEducation_type("Primary");
        metadata.setIs_deleted(false);
        metadata.setIs_active(true);
        metadata.setStart_date(Date.valueOf("2023-06-27"));

        // Save the registration form metadata
        registrationFormMetadataDAO.save(metadata);

        // Delete the registration form metadata
        registrationFormMetadataDAO.delete(metadata.getRegistration_form_id());

        // Try to get the deleted registration form metadata
        RegistrationFormMetadata deletedMetadata = registrationFormMetadataDAO.get(metadata.getRegistration_form_id());

        // Assert that the deleted registration form metadata is null
        assertNull(deletedMetadata);
    }
}
