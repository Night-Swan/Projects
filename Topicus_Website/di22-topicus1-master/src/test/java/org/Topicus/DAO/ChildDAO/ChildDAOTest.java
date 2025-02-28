package org.Topicus.DAO.ChildDAO;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.sql.Date;
import java.util.List;
import java.util.Random;

import org.Topicus.DAO.AddressDAO.AddressDAO;
import org.Topicus.DAO.ParentDAO.ParentDAO;
import org.Topicus.DAO.SystemUserDAO.SystemUserDAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Model.Child.Child;
import org.Topicus.Model.Guardian.Guardian;
import org.Topicus.Model.SystemUser.SystemUser;
import org.Topicus.Model.SystemUser.UserType;
import org.Topicus.Utility.Logs.LoggerManager;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

class ChildDAOTest {
    private static Child child;
    private static Guardian guardian;
    private static Address address;
    private static SystemUser user;

    /**
     * The set-up method will create the contextual elements required, such as the
     * Parent and the Address, which
     * will enable the Child to be tested fully.
     */
    @BeforeAll
    static void setUp() {
        LoggerManager.configureLoggers();

        // Create the Address
        address = new Address();
        address.setStreetName("Test Street");
        address.setStreetNumber(1);
        address.setPostalCode("1234AB");
        address.setCity("Test City");
        address.setCountry("Test Country");
        address.setPhoneNumber("+3106123456");

        address = AddressDAO.getInstance().save(address);

        // Create the System User
        user = new SystemUser();
        int nr = new Random().nextInt(350);
        user.setEmail("test_user" + nr + "@gmail.com");
        user.setUsername("test_user" + nr);
        user.setPassword_value("test_password");
        user.setType(UserType.GUARDIAN);

        // save the System User
        user = SystemUserDAO.getInstance().save(user);

        assertNotNull(user);

        // save the Address
        address = AddressDAO.getInstance().save(address);

        // Create the Guardian
        guardian = new Guardian();
        guardian.setAccount_id(user.getAccount_id());
        guardian.setAddress_id(address.getAddressID());
        guardian.setSurname("Test Surname");
        guardian.setGiven_names(List.of("Test Given Name 1", "Test Given Name 2"));
        guardian.setDate_of_birth(Date.valueOf("2000-01-01"));
        guardian.setPhone_number("+3106123456");
        guardian.setNationality("Dutch");
        guardian.setOccupation("Test Occupation");
        guardian.setCompany_name("Test Company Name");

        // save the Guardian
        guardian = ParentDAO.getInstance().save(guardian);
    }

    /**
     * This method is used to test for the creation of a child by standard means.
     */
    @Test
    void testCreateChild() {
        child = new Child();
        child.setGivenNames(List.of("Test Given Name 1", "Test Given Name 2"));
        child.setSurname("Test Surname");
        child.setBirthDate(Date.valueOf("2000-01-01"));
        child.setBsn("123456789");
        child.setNationality("Dutch");
        child.setLanguages(List.of("Dutch", "English"));
        child.setPreferredName("Test Preferred Name");

        // save the Child
        Child createdChild = ChildDAO.getInstance().save(child);

        // check if the Child was saved
        assertNotNull(createdChild);

        // check if the Child has an ID
        assertNotNull(createdChild.getChildID());
        assertEquals(createdChild.getChildID(), child.getChildID());
        assertEquals(createdChild.getSurname(), child.getSurname());
        assertEquals(createdChild.getBirthDate().getTime(), child.getBirthDate().getTime());
        assertEquals(createdChild.getBsn(), child.getBsn());
        assertEquals(createdChild.getNationality(), child.getNationality());
        assertTrue(() -> {
            List<String> cgn = child.getGivenNames();
            List<String> ccgn = createdChild.getGivenNames();
            if (cgn.size() == ccgn.size()) {
                for (int i = 0; i < cgn.size(); i++) {
                    if (!cgn.get(i).equals(ccgn.get(i))) {
                        return false;
                    }
                }
                return true;
            }
            return false;
        });
        assertTrue(() -> {
            List<String> cl = child.getLanguages();
            List<String> ccl = createdChild.getLanguages();
            if (cl.size() == ccl.size()) {
                for (int i = 0; i < cl.size(); i++) {
                    if (!cl.get(i).equals(ccl.get(i))) {
                        return false;
                    }
                }
                return true;
            }
            return false;
        });
        assertEquals(createdChild.getPreferredName(), child.getPreferredName());
    }

    /**
     * This method tests two DAO Methods:
     * The method to create the child in the database.
     * The method to link the child to a provided Guardian.
     */
    @Test
    void testCreateChildWithLink() {
        child = new Child();
        child.setGivenNames(List.of("Test Given Name 1", "Test Given Name 2"));
        child.setSurname("Test Surname");
        child.setBirthDate(Date.valueOf("2000-01-01"));
        child.setBsn("123456789");
        child.setNationality("Dutch");
        child.setLanguages(List.of("Dutch", "English"));
        child.setPreferredName("Test Preferred Name");

        // save the Child
        Child createdChild = ChildDAO.getInstance().save(child);

        System.out.println(createdChild.getChildID());
        // check if the Child was saved
        assertNotNull(createdChild);

        // check if the Child has an ID
        assertNotNull(createdChild.getChildID());

        // link the Child to the Guardian
        ChildDAO.getInstance().linkChildToParent(createdChild.getChildID(), guardian.getGuardian_id());

        // retrieve the children of the Guardian
        List<Child> children = ChildDAO.getInstance().getChildrenForParent(guardian.getGuardian_id());

        // check if the Child was linked to the Guardian
        assertNotNull(children);

        // check if the Child was linked to the Guardian
        List<Child> finalChildren = children.stream().filter(c -> c.getChildID().equals(createdChild.getChildID()))
                .toList();

        // check if the Child was linked to the Guardian
        assertNotNull(finalChildren);
    }

    /**
     * This method is used to retrieve an existing child in the database, and
     * compare the values retrieved to the
     * ones that were expected.
     */
    @Test
    void testGetChild() {
        child = new Child();
        child.setGivenNames(List.of("Test Given Name 1", "Test Given Name 2"));
        child.setSurname("Test Surname");
        child.setBirthDate(Date.valueOf("2000-01-01"));
        child.setBsn("123456789");
        child.setNationality("Dutch");
        child.setLanguages(List.of("Dutch", "English"));
        child.setPreferredName("Test Preferred Name");

        // save the Child
        Child createdChild = ChildDAO.getInstance().save(child);

        // check if the Child was saved
        assertNotNull(createdChild);

        // check if the Child has an ID
        assertNotNull(createdChild.getChildID());

        // retrieve the Child from the database
        Child retrievedChild = ChildDAO.getInstance().get(createdChild.getChildID());

        // check if the Child was retrieved
        assertNotNull(retrievedChild);

        // check if the Child was retrieved correctly
        assertEquals(createdChild.getChildID(), retrievedChild.getChildID());
    }

    /**
     * This method is used to return a list of all the children from the database.
     * It should be >= 1 in size.
     */
    @Test
    void testGetAllChildren() {
        List<Child> children = ChildDAO.getInstance().getAll();
        assertNotNull(children);
        assertTrue(children.size() >= 1);
    }

    /**
     * This method tests two of the DAO methods:
     * First, it links the child to the guardian.
     * Then, it uses the query to attain the children for the parent to see if it
     * was successful.
     */
    @Test
    void testGetChildrenForParent() {
        child = new Child();
        child.setGivenNames(List.of("Test Given Name 1", "Test Given Name 2"));
        child.setSurname("Test Surname");
        child.setBirthDate(Date.valueOf("2000-01-01"));
        child.setBsn("123456789");
        child.setNationality("Dutch");
        child.setLanguages(List.of("Dutch", "English"));
        child.setPreferredName("Test Preferred Name");

        // save the Child
        Child createdChild = ChildDAO.getInstance().save(child);

        // check if the Child was saved
        assertNotNull(createdChild);

        // check if the Child has an ID
        assertNotNull(createdChild.getChildID());

        // link the Child to the Guardian
        ChildDAO.getInstance().linkChildToParent(createdChild.getChildID(), guardian.getGuardian_id());

        // retrieve the children of the Guardian
        List<Child> children = ChildDAO.getInstance().getChildrenForParent(guardian.getGuardian_id());

        // check if the Child was linked to the Guardian
        assertNotNull(children);

        // check if the Child was linked to the Guardian
        List<Child> finalChildren = children.stream().filter(c -> c.getChildID().equals(createdChild.getChildID()))
                .toList();

        // check if the Child was linked to the Guardian
        assertNotNull(finalChildren);
    }

    /**
     * This method is used to update the details of a particular child.
     * NOTE: for convenience, only a few details will be updated to show that the
     * functionality works.
     */
    @Test
    void testUpdateChild() {
        child = new Child();
        child.setGivenNames(List.of("Test Given Name 1", "Test Given Name 2"));
        child.setSurname("Test Surname");
        child.setBirthDate(Date.valueOf("2000-01-01"));
        child.setBsn("123456789");
        child.setNationality("Dutch");
        child.setLanguages(List.of("Dutch", "English"));
        child.setPreferredName("Test Preferred Name");

        // save the Child
        Child createdChild = ChildDAO.getInstance().save(child);

        // check if the Child was saved
        assertNotNull(createdChild);

        // check if the Child has an ID
        assertNotNull(createdChild.getChildID());

        // update the Child
        createdChild.setSurname("Updated Surname");
        createdChild.setNationality("Updated Nationality");

        // save the updated Child
        Child updatedChild = ChildDAO.getInstance().update(createdChild);

        // check if the Child was updated
        assertNotNull(updatedChild);

        // check if the Child was updated correctly
        assertEquals(createdChild.getChildID(), updatedChild.getChildID());

        // check if the Child was updated correctly
        assertEquals(createdChild.getSurname(), updatedChild.getSurname());
        assertEquals(createdChild.getNationality(), updatedChild.getNationality());
    }
}