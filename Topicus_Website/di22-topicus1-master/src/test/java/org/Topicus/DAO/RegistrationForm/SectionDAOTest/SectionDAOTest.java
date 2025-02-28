package org.Topicus.DAO.RegistrationForm.SectionDAOTest;

import org.Topicus.DAO.AddressDAO.AddressDAO;
import org.Topicus.DAO.RegistrationFormDAO.RegistrationFormMetadataDAO;
import org.Topicus.DAO.RegistrationFormDAO.SectionDAO;
import org.Topicus.DAO.SchoolDAO.SchoolDAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Model.RegistrationForm.RegistrationFormMetadata;
import org.Topicus.Model.RegistrationForm.Section;
import org.Topicus.Model.School.School;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.sql.Date;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.*;

public class SectionDAOTest {
    private static SectionDAO sectionDAO;
    private static Address address;
    private static School school;
    private static RegistrationFormMetadata metadata;

    @BeforeAll
    public static void setup() {
        sectionDAO = SectionDAO.getInstance();

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

        // create a new form metadata object
        metadata = new RegistrationFormMetadata();
        metadata.setRegistration_form_id(UUID.randomUUID());
        metadata.setSchool_id(school.getSchool_id());
        metadata.setYear(2023);
        metadata.setTitle("Test Title");
        metadata.setDescription("Test Description");
        metadata.setEducation_type("Test Education Type");
        metadata.setStart_date(Date.valueOf("2023-01-01"));
        metadata.setIs_active(true);
        metadata.setIs_deleted(false);

        // save the form metadata
        RegistrationFormMetadataDAO.getInstance().save(metadata);
    }

    @Test
    public void testSaveAndGet() {
        // Create a new section
        Section section = new Section();
        section.setSection_id(UUID.randomUUID());
        section.setRegistration_form_id(metadata.getRegistration_form_id());
        section.setTitle("Personal Information");
        section.setPosition_number(1);

        // Save the section
        sectionDAO.save(section);

        // Get the section
        Section retrievedSection = sectionDAO.get(section.getSection_id());

        // Assert that the retrieved section is not null
        assertNotNull(retrievedSection);

        // Assert that the retrieved section has the same properties as the original section
        assertEquals(section.getSection_id(), retrievedSection.getSection_id());
        assertEquals(section.getRegistration_form_id(), retrievedSection.getRegistration_form_id());
        assertEquals(section.getTitle(), retrievedSection.getTitle());
        assertEquals(section.getPosition_number(), retrievedSection.getPosition_number());
    }

    @Test
    public void testUpdate() {
        // Create a new section
        Section section = new Section();
        section.setSection_id(UUID.randomUUID());
        section.setRegistration_form_id(metadata.getRegistration_form_id());
        section.setTitle("Personal Information");
        section.setPosition_number(1);

        // Save the section
        sectionDAO.save(section);

        // Update the section
        section.setTitle("Updated Section");
        sectionDAO.update(section);

        // Get the updated section
        Section retrievedSection = sectionDAO.get(section.getSection_id());

        // Assert that the retrieved section is not null
        assertNotNull(retrievedSection);

        // Assert that the retrieved section has the updated properties
        assertEquals(section.getTitle(), retrievedSection.getTitle());
    }

    @Test
    public void testDelete() {
        // Create a new section
        Section section = new Section();
        section.setSection_id(UUID.randomUUID());
        section.setRegistration_form_id(metadata.getRegistration_form_id());
        section.setTitle("Personal Information");
        section.setPosition_number(1);

        // Save the section
        sectionDAO.save(section);

        // Delete the section
        sectionDAO.delete(section.getSection_id());

        // Try to get the deleted section
        Section deletedSection = sectionDAO.get(section.getSection_id());

        // Assert that the deleted section is null
        assertNull(deletedSection);
    }
}
