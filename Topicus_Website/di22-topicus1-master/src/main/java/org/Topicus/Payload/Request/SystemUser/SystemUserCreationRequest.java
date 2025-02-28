package org.Topicus.Payload.Request.SystemUser;

import jakarta.xml.bind.annotation.XmlRootElement;
import org.Topicus.Model.SystemUser.UserType;

@XmlRootElement
public class SystemUserCreationRequest {
    private UserType type;
    private String username;
    private String email;
    private String password;

    /*
     * CONSTRUCTORS
     */
    public SystemUserCreationRequest(UserType type, String username, String email, String password) {
        this.type = type;
        this.username = username;
        this.email = email;
        this.password = password;
    }

    public SystemUserCreationRequest() {

    }

    /*
     * GETTERS
     */
    public UserType getType() {
        return type;
    }
    public String getUsername() {
        return username;
    }
    public String getEmail() {
        return email;
    }
    public String getPassword() {
        return password;
    }
    
}
