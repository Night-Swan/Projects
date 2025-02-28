package org.Topicus.DAO.RegistrationForm.RegistrationFormDAOTest;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.sql.Date;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.AddressDAO.AddressDAO;
import org.Topicus.DAO.RegistrationFormDAO.FormComponentDAO;
import org.Topicus.DAO.RegistrationFormDAO.RegistrationFormDAO;
import org.Topicus.DAO.RegistrationFormDAO.RegistrationFormMetadataDAO;
import org.Topicus.DAO.RegistrationFormDAO.SectionDAO;
import org.Topicus.DAO.RegistrationFormDAO.StyleDAO;
import org.Topicus.DAO.SchoolDAO.SchoolDAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Model.RegistrationForm.DataType;
import org.Topicus.Model.RegistrationForm.FormComponent;
import org.Topicus.Model.RegistrationForm.RegistrationFormMetadata;
import org.Topicus.Model.RegistrationForm.Section;
import org.Topicus.Model.RegistrationForm.Style.Style;
import org.Topicus.Model.School.School;
import org.Topicus.Payload.Response.RegistrationForm.RegistrationFormContainer;
import org.Topicus.Payload.Response.RegistrationForm.SectionContainer;
import org.Topicus.Utility.Logs.LoggerManager;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

public class RegistrationFormDAOTest {
    private static Address address;
    private static School school;
    private static RegistrationFormMetadata metadata;
    private static Section section;
    private static Section section2;
    private static Section section3;
    private static FormComponent component;
    private static FormComponent component2;
    private static FormComponent component3;
    private static FormComponent component4;
    private static FormComponent component5;
    private static FormComponent component6;
    private static FormComponent component7;
    private static FormComponent component8;
    private static Style style;

    @BeforeAll
    public static void setup() {
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
        section.setTitle("Test Section");
        section.setPosition_number(1);

        // save the section
        SectionDAO.getInstance().save(section);

        // create a new section
        section2 = new Section();
        section2.setSection_id(UUID.randomUUID());
        section2.setRegistration_form_id(metadata.getRegistration_form_id());
        section2.setTitle("Test Section 2");
        section2.setPosition_number(2);

        // save the section
        SectionDAO.getInstance().save(section2);

        // create a new section
        section3 = new Section();
        section3.setSection_id(UUID.randomUUID());
        section3.setRegistration_form_id(metadata.getRegistration_form_id());
        section3.setTitle("Test Section 3");
        section3.setPosition_number(3);

        // save the section
        SectionDAO.getInstance().save(section3);

        // create a new form component
        component = new FormComponent();
        component.setComponent_id(UUID.randomUUID());
        component.setSection_id(section.getSection_id());
        component.setRegistration_form_id(metadata.getRegistration_form_id());
        component.setTitle("Test Component");
        component.setPosition(1);
        component.setMandatory(true);
        component.setData_type(DataType.TEXT);

        // save the component
        FormComponentDAO.getInstance().save(component);

        // create a new form component
        component2 = new FormComponent();
        component2.setComponent_id(UUID.randomUUID());
        component2.setSection_id(section.getSection_id());
        component2.setRegistration_form_id(metadata.getRegistration_form_id());
        component2.setTitle("Test Component 2");
        component2.setPosition(2);
        component2.setMandatory(true);
        component2.setData_type(DataType.TEXT);

        // save the component

        FormComponentDAO.getInstance().save(component2);

        // create a new form component
        component3 = new FormComponent();
        component3.setComponent_id(UUID.randomUUID());
        component3.setSection_id(section.getSection_id());
        component3.setRegistration_form_id(metadata.getRegistration_form_id());
        component3.setTitle("Test Component 3");
        component3.setPosition(3);
        component3.setMandatory(true);
        component3.setData_type(DataType.TEXT);

        // save the component
        FormComponentDAO.getInstance().save(component3);

        // create a new form component
        component4 = new FormComponent();
        component4.setComponent_id(UUID.randomUUID());
        component4.setSection_id(section2.getSection_id());
        component4.setRegistration_form_id(metadata.getRegistration_form_id());
        component4.setTitle("Test Component 4");
        component4.setPosition(1);
        component4.setMandatory(true);
        component4.setData_type(DataType.TEXT);

        // save the component
        FormComponentDAO.getInstance().save(component4);

        // create a new form component
        component5 = new FormComponent();
        component5.setComponent_id(UUID.randomUUID());
        component5.setSection_id(section2.getSection_id());
        component5.setRegistration_form_id(metadata.getRegistration_form_id());
        component5.setTitle("Test Component 5");
        component5.setPosition(2);
        component5.setMandatory(true);
        component5.setData_type(DataType.TEXT);

        // save the component
        FormComponentDAO.getInstance().save(component5);

        // create a new form component
        component6 = new FormComponent();
        component6.setComponent_id(UUID.randomUUID());
        component6.setSection_id(section3.getSection_id());
        component6.setRegistration_form_id(metadata.getRegistration_form_id());
        component6.setTitle("Test Component 6");
        component6.setPosition(1);
        component6.setMandatory(true);
        component6.setData_type(DataType.TEXT);

        // save the component
        FormComponentDAO.getInstance().save(component6);

        // create a new form component
        component7 = new FormComponent();
        component7.setComponent_id(UUID.randomUUID());
        component7.setSection_id(section3.getSection_id());
        component7.setRegistration_form_id(metadata.getRegistration_form_id());
        component7.setTitle("Test Component 7");
        component7.setPosition(2);
        component7.setMandatory(true);
        component7.setData_type(DataType.TEXT);

        // save the component
        FormComponentDAO.getInstance().save(component7);

        // create a new form component
        component8 = new FormComponent();
        component8.setComponent_id(UUID.randomUUID());
        component8.setSection_id(section3.getSection_id());
        component8.setRegistration_form_id(metadata.getRegistration_form_id());
        component8.setTitle("Test Component 8");
        component8.setPosition(3);
        component8.setMandatory(true);
        component8.setData_type(DataType.TEXT);

        // save the component
        FormComponentDAO.getInstance().save(component8);

        // create a new style
        style = new Style();
        style.setRegistration_form_id(metadata.getRegistration_form_id());
        style.setSection_font_color("#000000");
        style.setForm_component_font_color("#000000");
        style.setBackground_color("#FFFFFF");
        style.setLogo(new byte[] { 0x00, 0x01, 0x02, 0x03 });

        // save the style
        StyleDAO.getInstance().save(style);
    }

    @Test
    public void testSaveAndGet() {
        // make a new registration form container
        RegistrationFormContainer container = new RegistrationFormContainer();

        // set the registration form metadata
        container.setFormMetadata(metadata);

        // set the registration form style
        container.setFormStyle(style);

        List<SectionContainer> sectionContainers = new ArrayList<>();

        // create section containers
        SectionContainer sectionContainer = new SectionContainer();

        // add section and components to section container
        sectionContainer.setSection(section);
        sectionContainer.setFormComponentList(Arrays.asList(component, component2, component3));

        // add section container to registration form container
        sectionContainers.add(sectionContainer);

        // create section containers
        SectionContainer sectionContainer2 = new SectionContainer();

        // add section and components to section container
        sectionContainer2.setSection(section2);
        sectionContainer2.setFormComponentList(Arrays.asList(component4, component5));

        // add section container to registration form container
        sectionContainers.add(sectionContainer2);

        // create section containers
        SectionContainer sectionContainer3 = new SectionContainer();

        // add section and components to section container
        sectionContainer3.setSection(section3);
        sectionContainer3.setFormComponentList(Arrays.asList(component6, component7, component8));

        // add section container to registration form container
        sectionContainers.add(sectionContainer3);

        // set the section containers
        container.setSectionContainerList(sectionContainers);

        // save the registration form container
        RegistrationFormDAO.getInstance().updateRecord(container);

        // get the registration form container
        RegistrationFormContainer retrievedContainer = RegistrationFormDAO.getInstance().get(metadata.getRegistration_form_id());

        // check that the registration form container is not null
        assertNotNull(retrievedContainer);

        // check that the registration form metadata is not null
        assertNotNull(retrievedContainer.getFormMetadata());

        // check that the registration form style is not null
        assertNotNull(retrievedContainer.getFormStyle());

        // check that the section containers is not null
        assertNotNull(retrievedContainer.getSectionContainerList());

        // check that the section containers are not empty
        assertFalse(retrievedContainer.getSectionContainerList().isEmpty());

        // check that the section containers contain the correct number of sections
        assertEquals(3, retrievedContainer.getSectionContainerList().size());

    }

    @Test
    public void testUpdate() {
        // make a new registration form container
        RegistrationFormContainer container = new RegistrationFormContainer();

        // set the registration form metadata
        container.setFormMetadata(metadata);

        // set the registration form style
        container.setFormStyle(style);

        List<SectionContainer> sectionContainers = new ArrayList<>();

        // create section containers
        SectionContainer sectionContainer = new SectionContainer();

        // add section and components to section container
        sectionContainer.setSection(section);
        sectionContainer.setFormComponentList(Arrays.asList(component, component2, component3));

        // add section container to registration form container
        sectionContainers.add(sectionContainer);

        // create section containers
        SectionContainer sectionContainer2 = new SectionContainer();

        // add section and components to section container
        sectionContainer2.setSection(section2);
        sectionContainer2.setFormComponentList(Arrays.asList(component4, component5));

        // add section container to registration form container
        sectionContainers.add(sectionContainer2);

        // create section containers
        SectionContainer sectionContainer3 = new SectionContainer();

        // add section and components to section container
        sectionContainer3.setSection(section3);
        sectionContainer3.setFormComponentList(Arrays.asList(component6, component7, component8));

        // add section container to registration form container
        sectionContainers.add(sectionContainer3);

        // set the section containers
        container.setSectionContainerList(sectionContainers);

        // update some components
        component.setTitle("Updated Title");
        component2.setTitle("Updated Title 2");
        component3.setTitle("Updated Title 3");

        // update the registration form container
        RegistrationFormDAO.getInstance().updateRecord(container);

        // get the registration form container
        RegistrationFormContainer retrievedContainer = RegistrationFormDAO.getInstance().get(metadata.getRegistration_form_id());

        // check that the registration form container is not null
        assertNotNull(retrievedContainer);

        // check that the registration form metadata is not null
        assertNotNull(retrievedContainer.getFormMetadata());

        // check that the registration form style is not null
        assertNotNull(retrievedContainer.getFormStyle());

        // check that the section containers is not null
        assertNotNull(retrievedContainer.getSectionContainerList());

        // check that the section containers are not empty
        assertFalse(retrievedContainer.getSectionContainerList().isEmpty());

        // check that the section containers contain the correct number of sections
        assertEquals(3, retrievedContainer.getSectionContainerList().size());

        // check that the components were updated
        assertEquals("Updated Title", retrievedContainer.getSectionContainerList().get(0).getFormComponentList().get(0).getTitle());
        assertEquals("Updated Title 2", retrievedContainer.getSectionContainerList().get(0).getFormComponentList().get(1).getTitle());
        assertEquals("Updated Title 3", retrievedContainer.getSectionContainerList().get(0).getFormComponentList().get(2).getTitle());
    }

    @Test
    public void testDelete() {
        // make a new registration form container
        RegistrationFormContainer container = new RegistrationFormContainer();

        // set the registration form metadata
        container.setFormMetadata(metadata);

        // set the registration form style
        container.setFormStyle(style);

        List<SectionContainer> sectionContainers = new ArrayList<>();

        // create section containers
        SectionContainer sectionContainer = new SectionContainer();

        // add section and components to section container
        sectionContainer.setSection(section);
        sectionContainer.setFormComponentList(Arrays.asList(component, component2, component3));

        // add section container to registration form container
        sectionContainers.add(sectionContainer);

        // create section containers
        SectionContainer sectionContainer2 = new SectionContainer();

        // add section and components to section container
        sectionContainer2.setSection(section2);
        sectionContainer2.setFormComponentList(Arrays.asList(component4, component5));

        // add section container to registration form container
        sectionContainers.add(sectionContainer2);

        // create section containers
        SectionContainer sectionContainer3 = new SectionContainer();

        // add section and components to section container
        sectionContainer3.setSection(section3);
        sectionContainer3.setFormComponentList(Arrays.asList(component6, component7, component8));

        // add section container to registration form container
        sectionContainers.add(sectionContainer3);

        // set the section containers
        container.setSectionContainerList(sectionContainers);

        // save the registration form container
        RegistrationFormDAO.getInstance().updateRecord(container);

        // delete the registration form container
        RegistrationFormDAO.getInstance().delete(metadata.getRegistration_form_id());

        // get the registration form container
        RegistrationFormMetadata retrievedContainer = RegistrationFormMetadataDAO.getInstance().get(metadata.getRegistration_form_id());

        // check that the registration form container is null
        assertNull(retrievedContainer);
    }
}
