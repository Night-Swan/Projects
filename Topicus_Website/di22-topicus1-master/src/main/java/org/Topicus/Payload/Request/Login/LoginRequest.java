package org.Topicus.Payload.Request.Login;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class LoginRequest {
    // FIELD VARIABLE(S) ----------------------------------------------------------------------------------------------
    private String username;
    private String email;
    private String password;

    // CONSTRUCTOR ----------------------------------------------------------------------------------------------------

    public LoginRequest() {

    }

    public LoginRequest(String username, String email, String password) {
        this.username = username;
        this.email = email;
        this.password = password;
    }

    // GETTERS --------------------------------------------------------------------------------------------------------
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