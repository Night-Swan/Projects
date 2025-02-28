package org.Topicus.Model.SystemUser;

import jakarta.xml.bind.annotation.XmlRootElement;

import java.util.UUID;

@XmlRootElement
public class SystemUser {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID account_id;

    private UserType type;

    private String username;

    private String email;

    /**
     * Stores either the password itself or the hash value of the password, depending on whether the system user is created when received from the front-end or from the database.
     */
    private String password_value;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------------------

    /**
     * Default SystemUser Constructor
     */
    public SystemUser() {

    }

    /**
     * Fully loaded constructor for DB to Front-end.
     * @param account_id
     * @param type
     * @param username
     * @param email
     * @param password_value
     */
    public SystemUser(UUID account_id, UserType type, String username, String email, String password_value) {
        this.account_id = account_id;
        this.type = type;
        this.username = username;
        this.email = email;
        this.password_value = password_value;
    }

    /**
     * Utility constructor for Jersey Parsing.
     * @param type
     * @param username
     * @param email
     * @param password_value
     */
    public SystemUser(UserType type, String username, String email, String password_value) {
        this.type = type;
        this.username = username;
        this.email = email;
        this.password_value = password_value;
    }

    // GETTERS AND SETTERS ---------------------------------------------------------------------------------------------
    public UUID getAccount_id() {
        return account_id;
    }

    public void setAccount_id(UUID account_id) {
        this.account_id = account_id;
    }

    public UserType getType() {
        return type;
    }

    public void setType(UserType type) {
        this.type = type;
    }

    public String getUsername() {
        return username;
    }

    public void setUsername(String username) {
        this.username = username;
    }

    public String getEmail() {
        return email;
    }

    public void setEmail(String email) {
        this.email = email;
    }

    public String getPassword_value() {
        return password_value;
    }

    public void setPassword_value(String password_value) {
        this.password_value = password_value;
    }
}
