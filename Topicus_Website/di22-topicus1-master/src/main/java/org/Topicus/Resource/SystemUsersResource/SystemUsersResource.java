package org.Topicus.Resource.SystemUsersResource;

import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.SystemUserDAO.SystemUserDAO;
import org.Topicus.Model.SystemUser.SystemUser;
import org.Topicus.Payload.Request.SystemUser.SystemUserCreationRequest;
import org.Topicus.Resource.SchoolAdminsResource.SchoolAdminsResource;
import org.Topicus.Resource.SystemUserResource.SystemUserResource;
import org.Topicus.Security.ThreatPrevention.InputValidator;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.SystemUserParser;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.GET;
import jakarta.ws.rs.POST;
import jakarta.ws.rs.Path;
import jakarta.ws.rs.PathParam;
import jakarta.ws.rs.Produces;
import jakarta.ws.rs.core.Context;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.UriInfo;

/**
 * Class to handle requests for System Users.
 */
@Path("/users")
public class SystemUsersResource {
    // FIELD VARIABLE(S) ------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;

    // METHOD(S) --------------------------------

    /**
     * This method is used to get all system users.
     *
     * @return of type List<SystemUser>, representing the list of system users.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    public List<SystemUser> getSystemUsers() {
        return SystemUserDAO.instance.getAll();
    }

    /**
     * This method is used to create a system user
     * 
     * @param systemUserCreationRequest of type SystemUserCreationRequest,
     *                                  representing the system user to be created.
     * @return of type SystemUser, representing the created system user.
     */
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public SystemUser createSystemUser(SystemUserCreationRequest systemUserCreationRequest) {

        if (!InputValidator.isValidUser(systemUserCreationRequest)) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid input for system user creation request, aborting.");
            return null;
        }

        SystemUser createdSystemUser = SystemUserDAO.getInstance()
                .save(SystemUserParser.parseSystemUserCreationRequest(systemUserCreationRequest));

        if (createdSystemUser == null) {
            LoggerManager.RESOURCE_LOGGER.warning("Failed to create system user, aborting.");
        }

        return createdSystemUser;
    }

    /**
     * This method is used to get a specific system user.
     *
     * @param id of type UUID, representing the id of the system user.
     * @return of type SystemUserResource, representing the system user.
     */
    @Path("{id}")
    @RolesAllowed("PUBLIC")
    public SystemUserResource handleSystemUser(@PathParam("id") String id) {
        UUID userID;

        try {
            userID = UUID.fromString(id);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }

        return new SystemUserResource(uriInfo, request, userID);
    }

    /**
     * This method is used to instantiate the school admins resource in the event that a request is directed to a school admin.
     * @return of type SchoolAdminsResource.
     */
    @Path("/school_admins")
    @RolesAllowed("SCHOOL_ADMIN")
    public SchoolAdminsResource getSchoolAdminsResource() {
        return new SchoolAdminsResource(uriInfo, request);
    }
}
