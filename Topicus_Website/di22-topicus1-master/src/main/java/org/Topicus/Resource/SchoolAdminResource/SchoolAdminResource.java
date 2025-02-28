package org.Topicus.Resource.SchoolAdminResource;

import java.util.UUID;

import org.Topicus.DAO.SystemUserDAO.SystemUserDAO;
import org.Topicus.Model.SchoolAdmin.SchoolAdmin;
import org.Topicus.Payload.Response.SchoolAdmin.SchoolAdminDetails;
import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.DELETE;
import jakarta.ws.rs.GET;
import jakarta.ws.rs.PUT;
import jakarta.ws.rs.Path;
import jakarta.ws.rs.Produces;
import jakarta.ws.rs.core.Context;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.UriInfo;

public class SchoolAdminResource {

    // FIELD VARIABLE(S) ----------------------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;
    UUID schoolAdminID;

    // CONSTRUCTOR(S) ----------------------------------------------------

    public SchoolAdminResource(UriInfo uriInfo, Request request, UUID schoolAdminID) {
        this.uriInfo = uriInfo;
        this.request = request;
        this.schoolAdminID = schoolAdminID;
    }

    // METHOD(S) -----------------------------------------------------------

    /**
     * This method is used to get a school admin by id
     * 
     * @return of type SchoolAdmin, representing the school admin to be retrieved.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public SchoolAdmin getSchoolAdmin() {
        SchoolAdmin schoolAdmin = SystemUserDAO.getInstance().getSchoolAdmin(schoolAdminID);

        if (schoolAdmin == null) {
            LoggerManager.RESOURCE_LOGGER.warning("no school admin with id: " + schoolAdminID);
            return null;
        }

        return schoolAdmin;
    }

    /**
     * Method used for getting the details of a school admin by id
     * 
     * @return of type SchoolAdminDetails, representing the details of the school
     *         admin to be retrieved.
     */
    @Path("details")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public SchoolAdminDetails getSchoolAdminDetails() {
        SchoolAdminDetails schoolAdminDetails = SystemUserDAO.getInstance().getSchoolAdminDetails(schoolAdminID);

        if (schoolAdminDetails == null) {
            LoggerManager.RESOURCE_LOGGER.warning("no school admin details for id: " + schoolAdminID);
            return null;
        }

        return schoolAdminDetails;
    }

    /**
     * This method is used to update a school admin by id
     * 
     * @param schoolAdmin of type SchoolAdmin, representing the school admin to be
     *                    updated.
     * @return of type SchoolAdmin, representing the updated school admin.
     */
    @PUT
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public SchoolAdmin updateSchoolAdmin(SchoolAdmin schoolAdmin) {

        if (!schoolAdminID.equals(schoolAdmin.getAdminID())) {
            LoggerManager.RESOURCE_LOGGER
                    .warning("id " + schoolAdminID + " deduced from the path is different from the id "
                            + schoolAdmin.getAdminID() + " of the JSON object.");
            return null;
        }

        SchoolAdmin updatedSchoolAdmin = SystemUserDAO.getInstance().updateSchoolAdmin(schoolAdmin);

        if (updatedSchoolAdmin == null) {
            LoggerManager.RESOURCE_LOGGER.warning("failed to update school admin for id: " + schoolAdminID);
        }

        return updatedSchoolAdmin;
    }

    /**
     * This method is used to delete a school admin by id
     */
    @DELETE
    public void deleteSchoolAdmin() {
        SystemUserDAO.getInstance().deleteSchoolAdmin(schoolAdminID);
    }

}
