package org.Topicus.DAO.RegistrationForm.FormComponentDAOTest;

import org.Topicus.DAO.AddressDAO.AddressDAO;
import org.Topicus.DAO.RegistrationFormDAO.FormComponentDAO;
import org.Topicus.DAO.RegistrationFormDAO.RegistrationFormMetadataDAO;
import org.Topicus.DAO.RegistrationFormDAO.SectionDAO;
import org.Topicus.DAO.SchoolDAO.SchoolDAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Model.RegistrationForm.DataType;
import org.Topicus.Model.RegistrationForm.FormComponent;
import org.Topicus.Model.RegistrationForm.RegistrationFormMetadata;
import org.Topicus.Model.RegistrationForm.Section;
import org.Topicus.Model.School.School;
import org.Topicus.Utility.Logs.LoggerManager;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.sql.Date;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.*;

public class FormComponentDAOTest {
    private static FormComponentDAO formComponentDAO;
    private static Address address;
    private static School school;
    private static RegistrationFormMetadata metadata;
    private static Section section;

    @BeforeAll
    public static void setup() {
        formComponentDAO = FormComponentDAO.getInstance();
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

        // create a new section
        section = new Section();
        section.setSection_id(UUID.randomUUID());
        section.setRegistration_form_id(metadata.getRegistration_form_id());
        section.setTitle("Test Section Name");
        section.setPosition_number(1);

        // save the section
        SectionDAO.getInstance().save(section);

    }

    @Test
    void testSaveAndGet() {
        // Create a new form component
        FormComponent formComponent = new FormComponent();
        formComponent.setComponent_id(UUID.randomUUID());
        formComponent.setRegistration_form_id(metadata.getRegistration_form_id());
        formComponent.setSection_id(section.getSection_id());
        formComponent.setData_type(DataType.TEXT);
        formComponent.setMandatory(true);
        formComponent.setPosition(1);
        formComponent.setTitle("Test Title");

        // Save the form component
        formComponentDAO.save(formComponent);

        // Get the form component
        FormComponent retrievedFormComponent = formComponentDAO.get(formComponent.getComponent_id());

        // Assert that the retrieved form component is not null
        assertNotNull(retrievedFormComponent);

        // Assert that the retrieved form component has the same properties as the
        // original form component
        assertEquals(formComponent.getComponent_id(), retrievedFormComponent.getComponent_id());
        assertEquals(formComponent.getRegistration_form_id(), retrievedFormComponent.getRegistration_form_id());
        assertEquals(formComponent.getSection_id(), retrievedFormComponent.getSection_id());
        assertEquals(formComponent.getData_type(), retrievedFormComponent.getData_type());
        assertEquals(formComponent.isMandatory(), retrievedFormComponent.isMandatory());
        assertEquals(formComponent.getPosition(), retrievedFormComponent.getPosition());
        assertEquals(formComponent.getTitle(), retrievedFormComponent.getTitle());
    }

    @Test
    void testUpdate() {
        // Create a new form component
        FormComponent formComponent = new FormComponent();
        formComponent.setComponent_id(UUID.randomUUID());
        formComponent.setRegistration_form_id(metadata.getRegistration_form_id());
        formComponent.setSection_id(section.getSection_id());
        formComponent.setData_type(DataType.TEXT);
        formComponent.setMandatory(true);
        formComponent.setPosition(1);
        formComponent.setTitle("Test Title");

        // Save the form component
        formComponentDAO.save(formComponent);

        // Update the form component
        formComponent.setTitle("Updated Title");
        formComponent.setMandatory(false);
        formComponent.setPosition(2);
        formComponentDAO.update(formComponent);

        // Get the updated form component
        FormComponent retrievedFormComponent = formComponentDAO.get(formComponent.getComponent_id());

        // Assert that the retrieved form component is not null
        assertNotNull(retrievedFormComponent);

        // Assert that the retrieved form component has the updated properties
        assertEquals(formComponent.getTitle(), retrievedFormComponent.getTitle());
        assertEquals(formComponent.isMandatory(), retrievedFormComponent.isMandatory());
        assertEquals(formComponent.getPosition(), retrievedFormComponent.getPosition());
    }

    @Test
    void testDelete() {
        // Create a new form component
        FormComponent formComponent = new FormComponent();
        formComponent.setComponent_id(UUID.randomUUID());
        formComponent.setRegistration_form_id(metadata.getRegistration_form_id());
        formComponent.setSection_id(section.getSection_id());
        formComponent.setData_type(DataType.TEXT);
        formComponent.setMandatory(true);
        formComponent.setPosition(1);
        formComponent.setTitle("Test Title");

        // Save the form component
        formComponentDAO.save(formComponent);

        // Delete the form component
        formComponentDAO.delete(formComponent.getComponent_id());

        // Try to get the deleted form component
        FormComponent deletedFormComponent = formComponentDAO.get(formComponent.getComponent_id());

        // Assert that the deleted form component is null
        assertNull(deletedFormComponent);
    }
}
