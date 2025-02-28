package org.Topicus.Service;

import jakarta.ws.rs.core.Cookie;
import jakarta.ws.rs.core.NewCookie;

import java.util.Date;

public class CookieService {
    // FIELD(S) --------------------------------------------------------------------
    private static CookieService instance;

    // CONSTRUCTOR(S) --------------------------------------------------------------

    /**
     * Private constructor the generate instance of singleton.
     */
    private CookieService() {

    }

    /**
     * Access for the instance.
     * @return of type CookieService.
     */
    public static synchronized CookieService getInstance() {
        if (instance == null) {
            instance = new CookieService();
        }
        return instance;
    }

    // METHOD(S) -------------------------------------------------------------------
    /**
     * This method is used to create a new cookie which can be issued by the back-end to respond
     * to a request for logging-in.
     * @param userID of type String (parsed from UUID before).
     * @param userType of type String, representing the access role.
     * @return NewCookie.
     */
    public synchronized NewCookie createLoginCookie(String userID, String userType) {
        String token = TokenService.jwtTokenCreator(userID, userType);
        Date date = new Date();
        date.setTime(date.getTime() + 1000 * 60 * 60 * 3); // 3 hours
        return new NewCookie.Builder("authorization_token").value(token).path("/").httpOnly(false).expiry(date).build();
    }

    /**
     * Method that checks if the cookie being passed is valid or not.
     * @param inputCookie of type Cookie.
     * @return of type boolean.
     */
    public synchronized boolean checkCookie(Cookie inputCookie) {
        return TokenService.jwtValidator(inputCookie.getValue());
    }
}
