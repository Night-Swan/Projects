package org.Topicus.Resource.SchoolAdminsResource;

import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.SystemUserDAO.SystemUserDAO;
import org.Topicus.Model.SchoolAdmin.SchoolAdmin;
import org.Topicus.Payload.Response.SchoolAdmin.SchoolAdminDetails;
import org.Topicus.Resource.SchoolAdminResource.SchoolAdminResource;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.SystemUserParser;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.GET;
import jakarta.ws.rs.POST;
import jakarta.ws.rs.Path;
import jakarta.ws.rs.PathParam;
import jakarta.ws.rs.Produces;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.UriInfo;

/**
 * Class to handle requests for School Admins.
 */
public class SchoolAdminsResource {
    // FIELD VARIABLE(S) ------------------
    UriInfo uriInfo;
    Request request;

    // CONSTRUCTOR(S) ---------------------

    /**
     * Constructor for the SchoolAdminsResource class.
     */
    public SchoolAdminsResource(UriInfo uriInfo, Request request) {
        this.uriInfo = uriInfo;
        this.request = request;
    }

    // METHOD(S) --------------------------------

    /**
     * This method is used to get all school admins in the system.
     *
     * @return of type List<SchoolAdminDetails>, representing the list of school
     *         admins.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    public List<SchoolAdminDetails> getSchoolAdmins() {
        return SystemUserDAO.getInstance().getSchoolAdminDetails();
    }

    /**
     * This method is used to create a school admin.
     * 
     * @param schoolAdmin of type SchoolAdmin, representing the school admin to be
     *                    created.
     * @return of type SchoolAdmin, representing the created school admin.
     */
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    public SchoolAdmin createSchoolAdmin(SchoolAdmin schoolAdmin) {

        SchoolAdmin createSchoolAdmin = SystemUserDAO.getInstance()
                .saveSchoolAdmin(SystemUserParser.parseSchoolAdminCreation(schoolAdmin));

        if (createSchoolAdmin == null) {
            LoggerManager.RESOURCE_LOGGER.warning("Failed to create system user, aborting.");
        }

        return createSchoolAdmin;
    }

    /**
     * This method is used to handle requests for a specific school admin.
     * 
     * @param id of type UUID, representing the id of the school admin.
     * @return of type SchoolAdminResource, representing the school admin resource.
     */
    @Path("/{schoolAdminId}")
    @RolesAllowed("SCHOOL_ADMIN")
    public SchoolAdminResource handleSchoolAdmin(@PathParam("schoolAdminId") String id) {
        UUID schoolAdminId;

        try {
            schoolAdminId = UUID.fromString(id);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }

        return new SchoolAdminResource(uriInfo, request, schoolAdminId);
    }
}
