package org.Topicus.DAO.AddressDAO;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.UUID;

import org.Topicus.Model.Address.Address;
import org.Topicus.Utility.Logs.LoggerManager;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

class AddressDAOTest {
    // Test Variables:
    public static AddressDAO dao = AddressDAO.getInstance();
    public Address addressToSave;
    Address addressToUpdate;
    UUID addressID = UUID.randomUUID();
    String[] addition = { addressID.toString(), "7500NM", "Pineapple Road", "1", "Amsterdam", "The Netherlands",
            "+31689573458" };
    String[] update = { addressID.toString(), "6500AB", "Carrot Town", "2", "Enschede", "The Netherlands",
            "+31612633502" };

    @BeforeAll
    static void setUp() {
        LoggerManager.configureLoggers();
        dao = AddressDAO.getInstance();
    }

    /**
     * To facilitate the successful testing of the DAO, all the CRUD testing is
     * conducted in a singular method. This method will
     * perform the CRUD functionalities to assess whether all components of the
     * address are working.
     * This method will invoke smaller testing methods in the process.
     */
    @Test
    void testAllFunctions() {
        testSaveAddress();
        testGetAddress();
        testGetAllAddresses();
        testUpdateAddressRecord();
        testDeleteAddress();
    }

    /**
     * This method is used to create the address object for the database, and then
     * assert whether the returned address has the
     * same properties.
     * This tests the back-end functionality of the POST request.
     */
    @Test
    void testSaveAddress() {
        addressToSave = new Address(null, addition[1], addition[2], Integer.parseInt(addition[3]), addition[4],
                addition[5], addition[6]);
        Address saved = dao.save(addressToSave);
        assertNotNull(saved);
        assertEquals(addressToSave.getPostalCode(), saved.getPostalCode());
        assertEquals(addressToSave.getStreetName(), saved.getStreetName());
        assertEquals(addressToSave.getStreetNumber(), saved.getStreetNumber());
        assertEquals(addressToSave.getCity(), saved.getCity());
        assertEquals(addressToSave.getCountry(), saved.getCountry());
        assertEquals(addressToSave.getPhoneNumber(), saved.getPhoneNumber());
        addressToSave = saved;
    }

    /**
     * Given that the properties are tested for equality in testSaveAddress(), the
     * purpose of this method is to ensure that
     * an address is returned.
     * This tests the back-end functionality of the GET request.
     */
    @Test
    void testGetAddress() {
        addressToSave = new Address(null, addition[1], addition[2], Integer.parseInt(addition[3]), addition[4],
                addition[5], addition[6]);
        Address saved = dao.save(addressToSave);
        assertNotNull(saved);
        Address address = dao.get(saved.getAddressID());
        assertNotNull(address);
    }

    /**
     * This method will be used to check if all the addresses are loaded by the
     * query. After the addition of the address, the
     * size of the list of addresses should be >= 1. In the process, this method
     * will also test the AddressParser.parseAddress() method.
     * This tests the back-end functionality of the GET request.
     */
    @Test
    void testGetAllAddresses() {
        List<Address> addressList = dao.getAll();
        assertNotNull(addressList);
        assertTrue(addressList.size() >= 1);
    }

    /**
     * This method will be used to check if the details of the address can be
     * successfully updated.
     * The way the DAO was implemented unfortunately means that additional
     * validation is required to ensure that the address
     * object's UUID is the same, and this validation happens elsewhere.
     * This tests the back-end functionality of the PUT request.
     */
    @Test
    void testUpdateAddressRecord() {
        addressToSave = new Address(null, addition[1], addition[2], Integer.parseInt(addition[3]), addition[4],
                addition[5], addition[6]);
        Address saved = dao.save(addressToSave);
        assertNotNull(saved);
        addressToUpdate = new Address(saved.getAddressID(), update[1], update[2], Integer.parseInt(update[3]),
                update[4], update[5], update[6]);
        Address updated = dao.update(addressToUpdate);
        assertNotNull(updated);
        assertEquals(addressToUpdate.getAddressID().toString(), updated.getAddressID().toString());
        assertEquals(addressToUpdate.getPostalCode(), updated.getPostalCode());
        assertEquals(addressToUpdate.getStreetName(), updated.getStreetName());
        assertEquals(addressToUpdate.getStreetNumber(), updated.getStreetNumber());
        assertEquals(addressToUpdate.getCity(), updated.getCity());
        assertEquals(addressToUpdate.getCountry(), updated.getCountry());
        assertEquals(addressToUpdate.getPhoneNumber(), updated.getPhoneNumber());
    }

    /**
     * This method will be used to delete the address. It will be followed with a
     * GET to ensure the record is deleted.
     */
    @Test
    void testDeleteAddress() {
        addressToSave = new Address(null, addition[1], addition[2], Integer.parseInt(addition[3]), addition[4],
                addition[5], addition[6]);
        Address saved = dao.save(addressToSave);
        assertNotNull(saved);
        dao.delete(addressToSave.getAddressID());
        Address deletedAddress = dao.get(addressToSave.getAddressID());
        assertNull(deletedAddress);
    }
}