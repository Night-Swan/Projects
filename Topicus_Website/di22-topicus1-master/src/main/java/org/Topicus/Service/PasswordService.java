package org.Topicus.Service;

import java.nio.charset.StandardCharsets;
import java.security.SecureRandom;
import java.util.Base64;

import org.Topicus.Payload.Internal.HashedPasswordContainer;
import org.bouncycastle.crypto.generators.Argon2BytesGenerator;
import org.bouncycastle.crypto.params.Argon2Parameters;

/**
 * Uses Argon2 for hashing the password.
 */
public class PasswordService {

    // FOR ARGON2:
    private static int SALT_LENGTH = 16; // recommended.
    private static int ITERATIONS = 15;// Number of iterations (time cost)
    private static int MEMORY = 8 * 1024;// Memory size in kilobytes (memory cost)
    private static int PARALLELISM = 1;// Parallelism factor

    /**
     * Method to generate the HashedPasswordContainer object
     * 
     * @param password the password of the user
     * @return the object
     */
    public static HashedPasswordContainer generateHashedPasswordContainer(String password) {
        byte[] salt = generateSalt();
        String hash = hashPassword(password, salt);
        return new HashedPasswordContainer(hash, salt);
    }

    /**
     * method for hashing a plain text password using a salt
     * 
     * @param password the password wrote by the user
     * @param salt     the salt
     * @return the hashed password
     */
    public static String hashPassword(String password, byte[] salt) {
        Argon2Parameters.Builder builder = new Argon2Parameters.Builder(Argon2Parameters.ARGON2_id)
                .withVersion(Argon2Parameters.ARGON2_VERSION_13) // Argon2 algorithm version
                .withIterations(ITERATIONS) // Set the number of iterations
                .withMemoryAsKB(MEMORY) // Set the memory size
                .withParallelism(PARALLELISM) // Set the parallelism factor
                .withSalt(salt); // Set the salt value

        Argon2BytesGenerator gen = new Argon2BytesGenerator();
        gen.init(builder.build()); // Initialize the Argon2 generator with the configured parameters

        byte[] result = new byte[32]; // Create an array to store the resulting hash
        gen.generateBytes(password.getBytes(StandardCharsets.UTF_8), result, 0, result.length); // Generate the hash
        String hash = base64Encoding(result);
        return hash;
    }

    /**
     * method for generating a random salt
     * 
     * @return the salt as byte array
     */
    private static byte[] generateSalt() {
        // Create the salt and use SecureRandom to add additional bytes to the byteArray
        // for security measures.
        byte[] salt = new byte[SALT_LENGTH];
        SecureRandom secureRandom = new SecureRandom();
        secureRandom.nextBytes(salt);
        return salt;
    }

    /**
     * this method encodes the input byte array to a Base64-encoded string
     * representation
     * 
     * @param input a byte[] value
     * @return a string that can be safely transmitted or stored as text
     */
    private static String base64Encoding(byte[] input) {
        return Base64.getEncoder().encodeToString(input);
    }

    /**
     * this method checks if the password that user typed in is the same as the one
     * stored in the database
     * 
     * @param password   password as plain text
     * @param storedHash the password hashed in the db
     * @param salt       the salt used for hashing the password
     * @return true or false if the password matches
     */
    public boolean verifyPassword(String password, String storedHash, byte[] salt) {
        return hashPassword(password, salt).equals(storedHash);
    }
}