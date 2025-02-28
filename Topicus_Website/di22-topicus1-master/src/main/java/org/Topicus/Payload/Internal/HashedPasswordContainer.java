package org.Topicus.Payload.Internal;

/**
 * This class serves as a container for the HashedPassword and the Salt.
 */
public class HashedPasswordContainer {
    // FIELD VARIABLE(S) ----------------------------------------------------------------------------------------------
    private String hashedPassword;
    private byte[] salt;

    // CONSTRUCTOR ----------------------------------------------------------------------------------------------------
    public HashedPasswordContainer(String hashedPassword, byte[] salt) {
        this.hashedPassword = hashedPassword;
        this.salt = salt;
    }

    // GETTER(S) ------------------------------------------------------------------------------------------------------
    public String getHashedPassword() {
        return hashedPassword;
    }

    public byte[] getSalt() {
        return salt;
    }
}
