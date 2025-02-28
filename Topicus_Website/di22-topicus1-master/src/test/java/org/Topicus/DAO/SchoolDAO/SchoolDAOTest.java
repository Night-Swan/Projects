package org.Topicus.DAO.SchoolDAO;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.Topicus.DAO.AddressDAO.AddressDAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Model.School.School;
import org.Topicus.Payload.Response.School.SchoolDetails;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

class SchoolDAOTest {
    private static Address address;

    private static School school;

    /**
     * Used to create all contextual data that is needed for sufficiently testing
     * the DAO.
     */
    @BeforeAll
    static void setUp() {
        // Create the Address
        address = new Address();
        address.setStreetName("Test Street");
        address.setStreetNumber(1);
        address.setPostalCode("1234AB");
        address.setCity("Test City");
        address.setCountry("Test Country");
        address.setPhoneNumber("+3106123456");

        address = AddressDAO.getInstance().save(address);
    }

    // METHODS
    // ----------------------------------------------------------------------

    /**
     * Tests retrieval of school.
     */
    @Test
    void testGetSchool() {
        school = new School();
        school.setAddress_id(address.getAddressID());
        school.setName("Test School");
        school.setType("Test Type");
        school.setEmail("school-email-test@gmail.com");
        school.setPhone_number("+3106123456");

        school = SchoolDAO.getInstance().save(school);
        assertNotNull(school);

        School found = SchoolDAO.getInstance().get(school.getSchool_id());
        assertNotNull(found);
    }

    /**
     * Tests retrieval of all schools.
     */
    @Test
    void testGetAllSchools() {
        List<School> schoolList = SchoolDAO.getInstance().getAll();
        assertNotNull(schoolList);
        assertTrue(schoolList.size() >= 1);
    }

    /**
     * Tests retrieval of all schools details.
     */
    @Test
    void testGetAllSchoolDetails() {
        List<SchoolDetails> detailsList = SchoolDAO.getInstance().getAllSchoolDetails();
        assertNotNull(detailsList);
        assertTrue(detailsList.size() >= 1);
    }

    /**
     * Tests saving of a particular school.
     */
    @Test
    void testSaveSchool() {
        school = new School();
        school.setAddress_id(address.getAddressID());
        school.setName("Test School");
        school.setType("Test Type");
        school.setEmail("school-email-test@gmail.com");
        school.setPhone_number("+3106123456");

        school = SchoolDAO.getInstance().save(school);
        assertNotNull(school);
    }

    /**
     * Tests updating of a particular school.
     */
    @Test
    void testUpdateSchool() {
        school = new School();
        school.setAddress_id(address.getAddressID());
        school.setName("Test School");
        school.setType("Test Type");
        school.setEmail("school-email-test@gmail.com");
        school.setPhone_number("+3106123456");

        school = SchoolDAO.getInstance().save(school);
        assertNotNull(school);

        school.setName("Updated Test School");
        school.setType("Updated Test Type");

        school = SchoolDAO.getInstance().update(school);
        assertNotNull(school);

        assertEquals("Updated Test School", school.getName());
        assertEquals("Updated Test Type", school.getType());
    }

    /**
     * Tests deleting of a particular school.
     */
    @Test
    void testDeleteSchool() {
        school = new School();
        school.setAddress_id(address.getAddressID());
        school.setName("Test School");
        school.setType("Test Type");
        school.setEmail("school-email-test@gmail.com");
        school.setPhone_number("+3106123456");

        school = SchoolDAO.getInstance().save(school);
        assertNotNull(school);

        SchoolDAO.getInstance().delete(school.getSchool_id());

        School found = SchoolDAO.getInstance().get(school.getSchool_id());
        assertNull(found);
    }
}