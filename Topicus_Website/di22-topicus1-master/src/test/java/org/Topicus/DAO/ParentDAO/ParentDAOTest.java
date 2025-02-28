package org.Topicus.DAO.ParentDAO;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.List;

import org.Topicus.DAO.AddressDAO.AddressDAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Model.Guardian.Guardian;
import org.Topicus.Utility.Logs.LoggerManager;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

class ParentDAOTest {
    private static Address address;
    private static Guardian guardian;

    /**
     * Creates the contextual elements required. In this case, Guardians without an
     * account are possible to treat as it means the account ID can be null. There
     * will be a test for this included.
     */
    @BeforeAll
    static void setUp() {
        LoggerManager.configureLoggers();

        // create address
        address = new Address();
        address.setStreetName("Test Street");
        address.setStreetNumber(1);
        address.setPostalCode("1234AB");
        address.setCity("Test City");
        address.setCountry("Test Country");
        address.setPhoneNumber("+3106123456");
        address = AddressDAO.getInstance().save(address);
        assertNotNull(address);
    }

    /**
     * This method is used to test the creation of the guardian.
     */
    @Test
    void testCreateGuardian() {
        guardian = new Guardian();
        guardian.setNationality("Dutch");
        guardian.setSurname("Test");
        guardian.setGiven_names(new ArrayList<>(Arrays.asList("Test", "Test")));
        guardian.setPhone_number("+3106123456");
        guardian.setAddress_id(address.getAddressID());
        guardian.setDate_of_birth(new Date());
        guardian.setOccupation("Test");
        guardian.setCompany_name("Test");

        guardian = ParentDAO.getInstance().save(guardian);
        assertNotNull(guardian);

        // check if the guardian details are correct
        assertEquals("Dutch", guardian.getNationality());
        assertEquals("Test", guardian.getSurname());
        assertEquals(new ArrayList<>(Arrays.asList("Test", "Test")), guardian.getGiven_names());
        assertEquals("+3106123456", guardian.getPhone_number());
        assertEquals(address.getAddressID(), guardian.getAddress_id());
        assertEquals("Test", guardian.getOccupation());
        assertEquals("Test", guardian.getCompany_name());
    }

    /**
     * This method is used to test the retrieval of a guardian by the guardian_id.
     */
    @Test
    void testGetGuardian() {
        guardian = new Guardian();
        guardian.setNationality("Dutch");
        guardian.setSurname("Test");
        guardian.setGiven_names(new ArrayList<>(Arrays.asList("Test", "Test")));
        guardian.setPhone_number("+3106123456");
        guardian.setAddress_id(address.getAddressID());
        guardian.setDate_of_birth(new Date());
        guardian.setOccupation("Test");
        guardian.setCompany_name("Test");

        guardian = ParentDAO.getInstance().save(guardian);
        assertNotNull(guardian);

        Guardian found = ParentDAO.getInstance().get(guardian.getGuardian_id());
        assertNotNull(found);
        assertEquals(guardian.getGuardian_id(), found.getGuardian_id());
    }

    /**
     * This method is used to test if all of the guardians are retrieved.
     */
    @Test
    void testGetAllGuardians() {
        List<Guardian> guardians = ParentDAO.getInstance().getAll();
        assertNotNull(guardians);
        assertTrue(guardians.size() >= 1);
    }

    /**
     * This method is used to test if a guardian's details are updated.
     */
    @Test
    void testUpdateGuardian() {
        guardian = new Guardian();
        guardian.setNationality("Dutch");
        guardian.setSurname("Test");
        guardian.setGiven_names(new ArrayList<>(Arrays.asList("Test", "Test")));
        guardian.setPhone_number("+3106123456");
        guardian.setAddress_id(address.getAddressID());
        guardian.setDate_of_birth(new Date());
        guardian.setOccupation("Test");
        guardian.setCompany_name("Test");

        guardian = ParentDAO.getInstance().save(guardian);
        assertNotNull(guardian);

        guardian.setNationality("Updated");
        guardian.setSurname("Updated");
        guardian.setGiven_names(new ArrayList<>(Arrays.asList("Updated", "Updated")));

        guardian = ParentDAO.getInstance().update(guardian);

        // check if the guardian details are correct
        assertEquals("Updated", guardian.getNationality());
        assertEquals("Updated", guardian.getSurname());
        assertEquals(new ArrayList<>(Arrays.asList("Updated", "Updated")), guardian.getGiven_names());
    }

    /**
     * This method is used to delete a guardian.
     */
    @Test
    void testDeleteGuardian() {
        guardian = new Guardian();
        guardian.setNationality("Dutch");
        guardian.setSurname("Test");
        guardian.setGiven_names(new ArrayList<>(Arrays.asList("Test", "Test")));
        guardian.setPhone_number("+3106123456");
        guardian.setAddress_id(address.getAddressID());
        guardian.setDate_of_birth(new Date());
        guardian.setOccupation("Test");
        guardian.setCompany_name("Test");

        guardian = ParentDAO.getInstance().save(guardian);
        assertNotNull(guardian);

        ParentDAO.getInstance().delete(guardian.getGuardian_id());
        Guardian found = ParentDAO.getInstance().get(guardian.getGuardian_id());
        assertNull(found);
    }
}