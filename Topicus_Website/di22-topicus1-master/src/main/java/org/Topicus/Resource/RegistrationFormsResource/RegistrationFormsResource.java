package org.Topicus.Resource.RegistrationFormsResource;

import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.RegistrationFormDAO.RegistrationFormDAO;
import org.Topicus.DAO.RegistrationFormDAO.RegistrationFormMetadataDAO;
import org.Topicus.Model.RegistrationForm.RegistrationFormMetadata;
import org.Topicus.Payload.Response.RegistrationForm.RegistrationFormContainer;
import org.Topicus.Resource.RegistrationFormResource.RegistrationFormResource;
import org.Topicus.Utility.Logs.LoggerManager;

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

/*
Class to manage forms for a school
 */

public class RegistrationFormsResource {
    // FIELD VARIABLE(S) ------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;
    UUID schoolID;

    // CONSTRUCTOR(S) --------------------------
    public RegistrationFormsResource(UriInfo uriInfo, Request request, UUID schoolID) {
        this.uriInfo = uriInfo;
        this.request = request;
        this.schoolID = schoolID;
    }

    // METHOD(S) --------------------------------

    /**
     * Method to return all the registration forms for a school
     * 
     * @return of type RegistrationFormContainer.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public List<RegistrationFormContainer> getForms() {
        return RegistrationFormDAO.getInstance().getFormContainersForSchool(schoolID);
    }

    /**
     * Method to return all the metadata for the registration forms for a school
     * 
     * @return of type List<RegistrationFormMetadata>.
     */
    @Path("metadata")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public List<RegistrationFormMetadata> getFormsMetadata() {
        return RegistrationFormMetadataDAO.getInstance().getRegistrationFormMetadataForSchool(schoolID);
    }

    /**
     * Method to create or update a registration form for a school
     * 
     * @param formContainer of type FormContainerUpdateRequest
     * @return of type RegistrationFormContainer.
     */
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public RegistrationFormContainer saveForm(RegistrationFormContainer formContainer) {
        return RegistrationFormDAO.getInstance().updateRecord(formContainer);
    }

    /**
     * Method to get the active registration form for a school
     * 
     * @return of type RegistrationFormContainer.
     */
    @Path("active")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public RegistrationFormContainer getActiveForm() {
        RegistrationFormMetadata activeFormMetadata = RegistrationFormMetadataDAO.getInstance()
                .getActiveFormMetadata(schoolID);

        if (activeFormMetadata == null) {
            LoggerManager.RESOURCE_LOGGER.severe("No active form found for school with id: " + schoolID);
            return null;
        }

        UUID formID = activeFormMetadata.getRegistration_form_id();

        if (formID == null) {
            LoggerManager.RESOURCE_LOGGER.severe("Active form metadata has no form id for school id: " + schoolID);
            return null;
        }

        RegistrationFormContainer activeForm = RegistrationFormDAO.getInstance().get(formID);

        if (activeForm == null) {
            LoggerManager.RESOURCE_LOGGER.severe("School with id: " + schoolID
                    + " has active form metadata but no form container for form id: " + formID);
        }

        return activeForm;
    }

    /**
     * Method to handle a specific registration form for a school
     * 
     * @param id of type String
     * @return of type RegistrationFormResource.
     */
    @Path("{registration_form_id}")
    @RolesAllowed("PUBLIC")
    public RegistrationFormResource handleForm(@PathParam("registration_form_id") String id) {
        UUID formID;

        try {
            formID = UUID.fromString(id);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }

        return new RegistrationFormResource(uriInfo, request, schoolID, formID);
    }

}
