package org.Topicus.Security.PermissionCheck;

import java.io.IOException;
import java.util.Map;

import org.Topicus.Model.SystemUser.UserType;
import org.Topicus.Service.TokenService;
import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.ws.rs.container.ContainerRequestContext;
import jakarta.ws.rs.container.ContainerRequestFilter;
import jakarta.ws.rs.core.Cookie;
import jakarta.ws.rs.core.Response;
import jakarta.ws.rs.ext.Provider;

@Provider
public class PermissionFilter implements ContainerRequestFilter {

    /**
     * Filters incoming container requests and applies access control logic.
     *
     * @param requestContext The context of the container request.
     * @throws IOException If an I/O error occurs during the filtering process.
     */
    @Override
    public void filter(ContainerRequestContext requestContext) throws IOException {

        boolean allowed_with_default_permission = PermissionValidator.validatePermission(UserType.PUBLIC,
                requestContext);

        if (allowed_with_default_permission) {
            return;
        }

        Response unauthorizedResponse = Response.status(Response.Status.UNAUTHORIZED).build();

        Map<String, Cookie> cookies = requestContext.getCookies();

        if (cookies == null) {
            LoggerManager.SECURITY_LOGGER
                    .severe("a request for a restricted access resource was made without cookies.");
            requestContext.abortWith(unauthorizedResponse);
            return;
        }

        Cookie tokenCookie = cookies.get("authorization_token");

        if (tokenCookie == null) {
            LoggerManager.SECURITY_LOGGER.severe(
                    "a request for a restricted access resource was made without an authorization_token cookie.");
            requestContext.abortWith(unauthorizedResponse);
            return;
        }

        String authorization_token = tokenCookie.getValue();

        if (authorization_token == null) {
            LoggerManager.SECURITY_LOGGER.severe(
                    "a request for a restricted access resource was made with an empty authorization_token cookie.");
            requestContext.abortWith(unauthorizedResponse);
            return;
        }

        boolean valid_token = TokenService.jwtValidator(authorization_token);

        if (!valid_token) {
            LoggerManager.SECURITY_LOGGER.severe(
                    "a request for a restricted access resource was made with an invalid authorization token.");
            requestContext.abortWith(unauthorizedResponse);
            return;
        }

        Map<String, String> tokenDetails = TokenService.getTokenDetails(authorization_token);

        if (tokenDetails.isEmpty()) {
            LoggerManager.SECURITY_LOGGER.severe(
                    "a request for a restricted access resource was made with an authorization token that did not contain any details.");
            requestContext.abortWith(unauthorizedResponse);
            return;
        }

        String issuer = tokenDetails.get("issuer");

        if (!issuer.equals(TokenService.ISSUER)) {
            LoggerManager.SECURITY_LOGGER.severe(
                    "a request for a restricted access resource was made with an authorization token that had an invalid issuer.");
            requestContext.abortWith(unauthorizedResponse);
            return;
        }

        UserType user_type = UserType.valueOf(tokenDetails.get("user_type"));

        if (user_type.equals(UserType.TOPICUS_ADMIN)) {
            return;
        }

        boolean valid_permission = PermissionValidator.validatePermission(user_type, requestContext);

        if (!valid_permission) {
            LoggerManager.SECURITY_LOGGER.severe(
                    "a request for a restricted access resource was made with an invalid authorization token.");
            requestContext.abortWith(unauthorizedResponse);
            return;
        }
    }
}