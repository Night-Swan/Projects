package org.Topicus.Security.PermissionCheck;

import java.util.Arrays;
import java.util.List;

import org.Topicus.Model.SystemUser.UserType;
import org.Topicus.Utility.Logs.LoggerManager;
import org.glassfish.jersey.server.ExtendedUriInfo;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.container.ContainerRequestContext;

public class PermissionValidator {
    /**
     * Validates whether the given user type has permission based on the roles allowed for the resource method.
     *
     * @param userType        The user type to validate permission for.
     * @param requestContext  The context of the container request.
     * @return                {@code true} if the user type has permission, {@code false} otherwise.
     */
    public static boolean validatePermission(UserType userType, ContainerRequestContext requestContext) {

        if (userType == null) {
            return false;
        }

        RolesAllowed rolesAllowed = ((ExtendedUriInfo) requestContext.getUriInfo()).getMatchedResourceMethod()
                .getInvocable().getHandlingMethod().getAnnotation(RolesAllowed.class);

        if (rolesAllowed == null) {
            return false;
        }

        String[] allowedRoles = rolesAllowed.value();

        if (allowedRoles == null || allowedRoles.length == 0) {
            return false;
        }

        List<UserType> allowedUserTypes = Arrays.asList(allowedRoles).stream().map(role -> {
            try {
                return UserType.valueOf(role);
            } catch (IllegalArgumentException e) {
                LoggerManager.SECURITY_LOGGER.severe("found invalid role in annotation: " + role);
                return null;
            }
        }).filter(role -> role != null).toList();

        if (allowedUserTypes == null || allowedUserTypes.isEmpty()) {
            return false;
        }

        return allowedUserTypes.contains(userType);
    }
}
