package org.Topicus.Resource.SchoolResource;

import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.RegistrationDAO.RegistrationDAO;
import org.Topicus.DAO.SchoolDAO.SchoolDAO;
import org.Topicus.Model.Registration.Status;
import org.Topicus.Model.School.School;
import org.Topicus.Payload.Response.Registration.RegistrationView;
import org.Topicus.Payload.Response.SchoolAdmin.SchoolAdminDetails;
import org.Topicus.Resource.RegistrationFormsResource.RegistrationFormsResource;
import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.DELETE;
import jakarta.ws.rs.GET;
import jakarta.ws.rs.PUT;
import jakarta.ws.rs.Path;
import jakarta.ws.rs.PathParam;
import jakarta.ws.rs.Produces;
import jakarta.ws.rs.QueryParam;
import jakarta.ws.rs.core.Context;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.UriInfo;

/*
This class is related to managing the resource requests to individual schools.
 */
public class SchoolResource {
    // FIELD VARIABLE(S) -------------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;
    UUID schoolID;

    // CONSTRUCTOR(S) ------------------------------------------
    public SchoolResource(UriInfo uriInfo, Request request, UUID schoolID) {
        this.uriInfo = uriInfo;
        this.request = request;
        this.schoolID = schoolID;
    }

    // METHOD(S) ------------------------------------------------

    /**
     * Method to get details of school.
     * 
     * @return of type School.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public School getSchoolDetails() {
        School school = SchoolDAO.getInstance().get(schoolID);

        if (school == null) {
            LoggerManager.RESOURCE_LOGGER.warning("no school with id: " + schoolID);
            return null;
        }

        return school;
    }

    @GET
    @Path("/admins")
    @Produces(MediaType.APPLICATION_JSON)
    public List<SchoolAdminDetails> getSAdminsBySchool() {
        return SchoolDAO.getInstance().getAdminDetailsBySchool(schoolID);
    }

    /**
     * Method to update school details (done by SchoolAdmin or Topicus Member).
     * 
     * @return of type School, representing updated school.
     */
    @PUT
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    public School updateSchoolDetails(School school) {
        return SchoolDAO.getInstance().update(school);
    }

    /**
     * Method to delete a school from the database.
     */
    @DELETE
    public void deleteSchool() {
        SchoolDAO.getInstance().delete(schoolID);
    }

    /**
     * For school administrator, getting all registrations on a form.
     * 
     * @return of type List<RegistrationView>
     */
    @Path("/form/{registrationFormID}/registrations")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public List<RegistrationView> getAllRegistrationsForForm(
            @PathParam("registrationFormID") String registrationFormID) {

        if (registrationFormID == null) {
            return null;
        }

        UUID registration_form_id;

        try {
            registration_form_id = UUID.fromString(registrationFormID);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(registrationFormID + " is not a valid UUID.");
            return null;
        }

        return RegistrationDAO.getInstance().loadRegistrationsByForm(registration_form_id);
    }

    /**
     * This method is used to provide the list view of the registrations for the
     * school.
     * 
     * @param status
     * @return of type List<RegistrationView>.
     */
    @Path("/registrationViews")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public List<RegistrationView> getRegistrationsForSchool(@QueryParam("status") String status) {
        if (status == null || status.isEmpty()) {
            LoggerManager.RESOURCE_LOGGER.info("No status provided, returning all registrations.");
            return RegistrationDAO.getInstance().loadSchoolRegistrations(schoolID);
        }

        try {
            Status stat = Status.valueOf(status);
            return RegistrationDAO.getInstance().loadSchoolRegistrationsByStatus(schoolID, stat);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.warning(status + " is not a valid status.");
            return RegistrationDAO.getInstance().loadSchoolRegistrations(schoolID);
        }
    }

    @Path("/forms")
    @RolesAllowed("PUBLIC")
    public RegistrationFormsResource handleRegistrationForm() {

        if (SchoolDAO.getInstance().get(schoolID) == null) {
            LoggerManager.RESOURCE_LOGGER.warning("School with ID " + schoolID + " does not exist.");
            return null;
        }

        return new RegistrationFormsResource(uriInfo, request, schoolID);
    }
}
