package org.Topicus.Resource.RegistrationFormResource;

import java.util.UUID;

import jakarta.ws.rs.*;
import org.Topicus.DAO.RegistrationFormDAO.RegistrationFormDAO;
import org.Topicus.DAO.RegistrationFormDAO.StyleDAO;
import org.Topicus.DAO.SchoolDAO.SchoolDAO;
import org.Topicus.Model.RegistrationForm.Style.Style;
import org.Topicus.Model.School.School;
import org.Topicus.Payload.Response.RegistrationForm.RegistrationFormContainer;
import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.core.*;

/*
Class to manage registration form for a School.
 */

public class RegistrationFormResource {
    // FIELD VARIABLE(S) ------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;
    UUID schoolID;
    UUID formID;

    // CONSTRUCTOR(S) --------------------------
    public RegistrationFormResource(UriInfo uriInfo, Request request, UUID schoolID, UUID formID) {
        this.uriInfo = uriInfo;
        this.request = request;
        School school = SchoolDAO.getInstance().get(schoolID);
        if (school == null) {
            LoggerManager.RESOURCE_LOGGER.warning("School with id " + schoolID + " not found.");
        }
        this.schoolID = schoolID;
        this.formID = formID;
    }

    // METHOD(S) --------------------------------

    /**
     * Method to return a registration form based on an id
     * 
     * @return of type RegistrationForm.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public RegistrationFormContainer getForm() {
        RegistrationFormContainer form_container = RegistrationFormDAO.getInstance().get(formID);

        if (form_container == null) {
            LoggerManager.RESOURCE_LOGGER.warning("could not find form with id: " + formID);
        }

        return form_container;
    }

    /**
     * Method to update the details of the form.
     * 
     * @param form type RegistrationForm
     * @return of type RegistrationForm, representing updated RegistrationForm.
     */
    @PUT
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public RegistrationFormContainer updateForm(RegistrationFormContainer form) {
        return RegistrationFormDAO.getInstance().updateRecord(form);
    }

    /**
     * Method for deleting a form from the DB. WARNING: only to be used for topicus
     * admins
     */
    @DELETE
    @RolesAllowed("SCHOOL_ADMIN")
    public void deleteForm() {
        RegistrationFormDAO.getInstance().delete(formID);
    }

    /**
     * For getting the style of the registration form.
     * @return
     */
    @Path("/style")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Style getStyle() {
        return StyleDAO.getInstance().get(formID);
    }
}
