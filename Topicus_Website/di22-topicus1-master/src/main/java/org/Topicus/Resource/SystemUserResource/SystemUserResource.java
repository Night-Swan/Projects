package org.Topicus.Resource.SystemUserResource;

import java.util.UUID;

import org.Topicus.DAO.SystemUserDAO.SystemUserDAO;
import org.Topicus.Model.SystemUser.SystemUser;
import org.Topicus.Security.ThreatPrevention.InputValidator;
import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.DELETE;
import jakarta.ws.rs.GET;
import jakarta.ws.rs.PUT;
import jakarta.ws.rs.Produces;
import jakarta.ws.rs.core.Context;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.UriInfo;

public class SystemUserResource {
    // FIELD VARIABLE(S) ----------------------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;
    UUID userID;

    // CONSTRUCTOR(S) ----------------------------------------------------
    public SystemUserResource(UriInfo uriInfo, Request request, UUID userID) {
        this.uriInfo = uriInfo;
        this.request = request;
        this.userID = userID;
    }

    // METHOD(S) -----------------------------------------------------------

    /**
     * This method is used to get a system user by id
     * 
     * @return of type SystemUser, representing the system user to be retrieved.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public SystemUser getSystemUser() {
        SystemUser systemUser = SystemUserDAO.getInstance().get(userID);

        if (systemUser == null) {
            LoggerManager.RESOURCE_LOGGER.warning("no system user with id: " + userID);
            return null;
        }

        return systemUser;
    }

    /**
     * This method is used to update a system user by id
     * 
     * @param systemUser of type SystemUser, representing the system user to be
     *                   updated.
     * @return of type SystemUser, representing the updated system user.
     */
    @PUT
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("GUARDIAN")
    public SystemUser updateSystemUser(SystemUser systemUser) {

        if (!InputValidator.isValidUser(systemUser)) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid input for system user update, aborting.");
            return null;
        }

        if (!systemUser.getAccount_id().equals(userID)) {
            LoggerManager.RESOURCE_LOGGER.warning("id " + userID + " deduced from the path is different from the id "
                    + systemUser.getAccount_id() + " of the JSON object");
        }

        SystemUser updatedSystemUser = SystemUserDAO.getInstance().update(systemUser);

        if (updatedSystemUser == null) {
            LoggerManager.RESOURCE_LOGGER.warning("failed to update system user for id: " + userID);
        }

        return updatedSystemUser;
    }

    /**
     * This method is used to delete a system user by id
     */
    @DELETE
    @RolesAllowed("GUARDIAN")
    public void deleteSystemUser() {
        SystemUserDAO.getInstance().delete(userID);
    }
}
