package org.Topicus.DAO.SystemUserDAO;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.Random;

import org.Topicus.Model.SystemUser.SystemUser;
import org.Topicus.Model.SystemUser.UserType;
import org.Topicus.Utility.Logs.LoggerManager;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

class SystemUserDAOTest {
    private SystemUser user;

    /**
     * This method is used to create the contextual details required to test the
     * DAO.
     */
    @BeforeAll
    static void setUp() {
        LoggerManager.configureLoggers();
    }

    /**
     * This method is used to test the retrieval of a user by email.
     */
    @Test
    void testGetSystemUserByEmail() {
        user = new SystemUser();
        int random = new Random().nextInt(100000);
        user.setUsername("Test" + random);
        user.setEmail("Test" + random + "@test.com");
        user.setType(UserType.SCHOOL_ADMIN);
        user.setPassword_value("Test");

        user = SystemUserDAO.getInstance().save(user);
        assertNotNull(user);

        SystemUser found = SystemUserDAO.getInstance().get(user.getEmail());
        assertNotNull(found);
    }

    /**
     * Tests retrieval of password salt for user.
     */
    @Test
    void testGetPasswordSaltForUser() {
        user = new SystemUser();
        int random = new Random().nextInt(100000);
        user.setUsername("Test" + random);
        user.setEmail("Test" + random + "@test.com");
        user.setType(UserType.SCHOOL_ADMIN);
        user.setPassword_value("Test");

        user = SystemUserDAO.getInstance().save(user);
        assertNotNull(user);

        byte[] passwordSalt = SystemUserDAO.getInstance().getPasswordSaltforUser(user.getAccount_id());
        assertNotNull(passwordSalt);
    }

    /**
     * Tests retrieval of all users.
     */
    @Test
    void testGetAllUsers() {
        List<SystemUser> users = SystemUserDAO.getInstance().getAll();
        assertNotNull(users);
        assertTrue(users.size() >= 1);
    }

    /**
     * Tests saving of a user.
     */
    @Test
    void testSaveSystemUser() {
        user = new SystemUser();
        int random = new Random().nextInt(100000);
        user.setUsername("Test" + random);
        user.setEmail("Test" + random + "@test.com");
        user.setType(UserType.SCHOOL_ADMIN);
        user.setPassword_value("Test");

        user = SystemUserDAO.getInstance().save(user);
        assertNotNull(user);
    }

    /**
     * Tests updating of a user.
     */
    @Test
    void testUpdateSystemUser() {
        user = new SystemUser();
        int random = new Random().nextInt(100000);
        user.setUsername("Test" + random);
        user.setEmail("Test" + random + "@test.com");
        user.setType(UserType.SCHOOL_ADMIN);
        user.setPassword_value("Test");

        user = SystemUserDAO.getInstance().save(user);
        assertNotNull(user);

        user.setUsername("Test" + random + "Updated");
        user.setEmail("Test" + random + "@updated.com");

        SystemUser updated = SystemUserDAO.getInstance().update(user);

        assertNotNull(updated);
        assertEquals(updated.getUsername(), user.getUsername());
        assertEquals(updated.getEmail(), user.getEmail());
    }

    /**
     * Tests deletion of a user.
     */
    @Test
    void testDeleteSystemUser() {
        user = new SystemUser();
        int random = new Random().nextInt(100000);
        user.setUsername("Test" + random);
        user.setEmail("Test" + random + "@test.com");
        user.setType(UserType.SCHOOL_ADMIN);
        user.setPassword_value("Test");

        user = SystemUserDAO.getInstance().save(user);
        assertNotNull(user);

        SystemUserDAO.getInstance().delete(user.getAccount_id());
        SystemUser found = SystemUserDAO.getInstance().get(user.getAccount_id());
        assertNull(found);
    }
}