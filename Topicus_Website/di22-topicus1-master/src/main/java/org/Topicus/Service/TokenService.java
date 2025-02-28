package org.Topicus.Service;

import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.NoSuchAlgorithmException;
import java.security.interfaces.RSAPrivateKey;
import java.security.interfaces.RSAPublicKey;
import java.time.Instant;
import java.util.Base64;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;
import java.util.UUID;
import java.util.logging.Logger;

import org.Topicus.Exceptions.InvalidTokenException;
import org.Topicus.Model.SystemUser.UserType;
import org.Topicus.Utility.Logs.LoggerManager;

import com.auth0.jwt.JWT;
import com.auth0.jwt.JWTCreator;
import com.auth0.jwt.JWTVerifier;
import com.auth0.jwt.algorithms.Algorithm;
import com.auth0.jwt.exceptions.JWTVerificationException;
import com.auth0.jwt.interfaces.DecodedJWT;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.NullNode;

public class TokenService {
    // FIELD VARIABLE(S):
    private static TokenService instance;
    private RSAPublicKey PUBLIC_KEY;
    private RSAPrivateKey PRIVATE_KEY;
    public static final String ISSUER = "topicus";
    private JWTVerifier jwtVerifier;

    // CONSTRUCTOR(S):
    private TokenService() {

    }

    /**
     * Gets the instance of the Singleton class for the creation of password.
     * 
     * @return of type TokenService.
     */
    public static synchronized TokenService getInstance() {
        if (instance == null) {
            instance = new TokenService();
            instance.initializeSeeds();
            instance.initializeValidator();
        }

        return instance;
    }

    // GETTER(S)
    // ------------------------------------------------------------------------------------------------------

    /**
     * @return of RSAPublicKey.
     */
    private RSAPublicKey getPUBLIC_KEY() {
        return PUBLIC_KEY;
    }

    /**
     * @return of RSAPrivateKey.
     */
    private RSAPrivateKey getPRIVATE_KEY() {
        return PRIVATE_KEY;
    }

    private String getIssuer() {
        return ISSUER;
    }

    private JWTVerifier getJwtVerifier() {
        return jwtVerifier;
    }

    /**
     * @param privateKey is of RSAPrivateKey.
     */
    private void setPRIVATE_KEY(RSAPrivateKey privateKey) {
        this.PRIVATE_KEY = privateKey;
    }

    /**
     * @param publicKey of type RSAPublicKey.
     */
    private void setPUBLIC_KEY(RSAPublicKey publicKey) {
        this.PUBLIC_KEY = publicKey;
    }

    public void setJwtVerifier(JWTVerifier jwtVerifier) {
        this.jwtVerifier = jwtVerifier;
    }

    // METHOD(S)
    // -------------------------------------------------------------------------------------------------

    /**
     * Method used for initializing the seeds by which JWT tokens are
     * created/managed/verified.
     */
    public void initializeSeeds() {
        try {
            KeyPairGenerator kpg = KeyPairGenerator.getInstance("RSA");
            kpg.initialize(2048);
            KeyPair kp = kpg.generateKeyPair();
            getInstance().setPRIVATE_KEY((RSAPrivateKey) kp.getPrivate());
            getInstance().setPUBLIC_KEY((RSAPublicKey) kp.getPublic());
        } catch (NoSuchAlgorithmException e) {
            LoggerManager.SERVICE_LOGGER.severe(e.getMessage());
        }
    }

    /**
     * Method used to initialize the validator used for the log-in checking.
     */
    public void initializeValidator() {
        Algorithm algorithm = Algorithm.RSA256(getInstance().getPUBLIC_KEY(), getInstance().getPRIVATE_KEY());
        this.jwtVerifier = JWT.require(algorithm).withIssuer(getInstance().getIssuer()).build();
    }

    /**
     * Used to create the token for a particular user.
     * 
     * @param userID   to set the ID of the user.
     * @param userType to set the Type of the user.
     * @return of type String, representing the JWT token.
     */
    public static synchronized String jwtTokenCreator(String userID, String userType) {
        // String pri64 =
        // Base64.getEncoder().encodeToString(getInstance().getPRIVATE_KEY().getEncoded());
        // String pub64 =
        // Base64.getEncoder().encodeToString(getInstance().getPUBLIC_KEY().getEncoded());
        // Construct the Payload:
        Map<String, String> payload = new HashMap<>();
        payload.put("user_id", userID);
        payload.put("user_type", userType);
        // Now, construct the tokens:
        JWTCreator.Builder tokenBuilder = JWT.create()
                .withIssuer(TokenService.ISSUER)
                .withSubject("Topicus Log-in")
                .withIssuedAt(Date.from(Instant.now()))
                .withExpiresAt(Date.from(Instant.now().plusSeconds(7200)))
                .withJWTId(UUID.randomUUID().toString());
        // Add the contents of the payload to the token:
        payload.forEach(tokenBuilder::withClaim);
        return tokenBuilder.sign(Algorithm.RSA256((getInstance().getPUBLIC_KEY()), getInstance().getPRIVATE_KEY()));
    }

    /**
     * Method to validate the JWT token to see if it is valid by issuer, and by
     * expiry.
     * 
     * @param token of type String, representing the JWT token.
     * @return of type boolean.
     */
    public static synchronized boolean jwtValidator(String token) {
        try {
            final DecodedJWT jwt = JWT.decode(token);

            if (!jwt.getIssuer().equals(TokenService.ISSUER)) {
                throw new InvalidTokenException("Issuer not valid");
            }

            getInstance().getJwtVerifier().verify(token);

            return true;
        } catch (InvalidTokenException | JWTVerificationException e) {
            LoggerManager.SERVICE_LOGGER.severe(e.getMessage());
            return false;
        }
    }

    /**
     * Gets the token details of a JWT token. Guarantees
     * that if the return value is non-null, the issuer, user id and type are
     * present and
     * valid.
     * 
     * @param token the JWT token, as a String
     * @return the validated token details, or an empty map if the token is invalid
     */
    public static Map<String, String> getTokenDetails(String token) {
        if (token == null) {
            LoggerManager.SERVICE_LOGGER.severe("token is null");
            return Collections.emptyMap();
        }

        String[] tokenParts = token.split("\\.");

        if (tokenParts.length != 3) {
            LoggerManager.SERVICE_LOGGER.severe("token is not a valid JWT token: " + token);
            return Collections.emptyMap();
        }

        String encoded_payload = tokenParts[1];
        byte[] decoded_payload;

        try {
            decoded_payload = Base64.getUrlDecoder().decode(encoded_payload);
        } catch (IllegalArgumentException e) {
            LoggerManager.SERVICE_LOGGER.severe("token payload is not valid base64: " + token);
            return Collections.emptyMap();
        }

        String payload = new String(decoded_payload);

        ObjectMapper objectMapper = new ObjectMapper();
        JsonNode payloadNode;

        try {
            payloadNode = objectMapper.readTree(payload);
        } catch (JsonProcessingException e) {
            LoggerManager.SERVICE_LOGGER.severe("cannot process token payload: " + token);
            return Collections.emptyMap();
        }

        JsonNode issuerNode = payloadNode.get("iss");

        if (issuerNode == null || issuerNode instanceof NullNode) {
            LoggerManager.SERVICE_LOGGER.severe("issuer is not present or set to null in token: " + token);
            return Collections.emptyMap();
        }

        JsonNode idNode = payloadNode.get("user_id");

        if (idNode == null || idNode instanceof NullNode) {
            LoggerManager.SERVICE_LOGGER.severe("user ID is not present or set to null in token: " + token);
            return Collections.emptyMap();
        }

        JsonNode typeNode = payloadNode.get("user_type");

        if (typeNode == null || typeNode instanceof NullNode) {
            LoggerManager.SERVICE_LOGGER.severe("user type is not present or set to null in token: " + token);
            return Collections.emptyMap();
        }

        String issuer = issuerNode.asText();

        if (issuer.isEmpty()) {
            LoggerManager.SERVICE_LOGGER.severe("issuer is empty in token: " + token);
            return Collections.emptyMap();
        }

        String id = idNode.asText();

        if (id.isEmpty()) {
            LoggerManager.SERVICE_LOGGER.severe("user ID is empty in token: " + token);
            return Collections.emptyMap();
        }

        String type = typeNode.asText();

        if (type.isEmpty()) {
            LoggerManager.SERVICE_LOGGER.severe("user type is empty in token: " + token);
            return Collections.emptyMap();
        }

        Map<String, String> tokenDetails = new HashMap<>();

        try {
            tokenDetails.put("issuer", issuer);

            UUID user_id = UUID.fromString(id);
            tokenDetails.put("user_id", user_id.toString());

            UserType user_type = UserType.valueOf(type);
            tokenDetails.put("user_type", user_type.toString());

            return tokenDetails;
        } catch (IllegalArgumentException e) {
            LoggerManager.SERVICE_LOGGER.severe("invalid issuer, user ID or user type in token: " + token);
            return Collections.emptyMap();
        }
    }

    public static void main(String[] args) {
        UUID id = UUID.randomUUID();
        UserType type = UserType.GUARDIAN;
        String token = jwtTokenCreator(id.toString(), type.toString());

        Map<String, String> tokenDetails = getTokenDetails(token);

        if (tokenDetails.isEmpty()) {
            LoggerManager.SERVICE_LOGGER.severe("token details are empty");
            return;
        }

        Logger.getLogger("default").info("Issuer: " + tokenDetails.get("issuer"));
        Logger.getLogger("default").info("User ID: " + tokenDetails.get("user_id"));
        Logger.getLogger("default").info("User Type: " + tokenDetails.get("user_type"));
    }
}
