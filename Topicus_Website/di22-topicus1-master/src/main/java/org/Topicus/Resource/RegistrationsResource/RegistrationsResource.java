package org.Topicus.Resource.RegistrationsResource;

import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.RegistrationDAO.RegistrationDAO;
import org.Topicus.Model.Registration.Registration;
import org.Topicus.Payload.Request.Registration.RegistrationCreationRequest;
import org.Topicus.Payload.Response.Registration.RegistrationContainer;
import org.Topicus.Payload.Response.Registration.RegistrationView;
import org.Topicus.Resource.RegistrationResource.RegistrationResource;
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
This class defines the Registrations Resource, mostly used for administrative purposes to deduce the Registrations that
a school may have,
 */
@Path("/registrations")
public class RegistrationsResource {
    // FIELD VARIABLES ------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;

    // CONSTRUCTOR(S) --------------------------------------
    public RegistrationsResource(UriInfo uriInfo, Request request) {
        this.uriInfo = uriInfo;
        this.request = request;
    }

    public RegistrationsResource() {

    }

    // METHOD(S) ------------------------------------------

    /**
     * This method is used to produce a list of RegistrationViews for a particular guardian to render their dashboard.
     * @param guardianID of type String.
     * @return of type List<RegistrationView>
     */
    @Path("/registrationViews/{guardianID}")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public List<RegistrationView> getGuardianRegistrationsView(@PathParam("guardianID") String guardianID) {
        try {
            UUID guardian_id = UUID.fromString(guardianID);

            return RegistrationDAO.getInstance().loadGuardianRegistrations(guardian_id);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * This method is used to create a Registration.
     * @param registrationRequest of type RegistrationRequest.
     * @return of type Registration.
     */
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Registration saveRegistration(RegistrationCreationRequest registrationRequest) {
        if (registrationRequest == null || !registrationRequest.isValidRequest()) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid Registration Creation Request.");
            return null;
        }

        return RegistrationDAO.getInstance()
                .save(new Registration(registrationRequest.getConvertedGID(), registrationRequest.getConvertedCID(),
                        registrationRequest.getConvertedSID(), registrationRequest.getConvertedRegistrationFormID(),
                        registrationRequest.getConvertedStatus()));
    }

    /**
     * This method is used to export a list of RegistrationContainers to process the export of all the registration containers
     * for a particular registration form.
     * @param formID of type String.
     * @return of type List<RegistrationContainer>
     */
    @Path("/export/{form_id}")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public List<RegistrationContainer> exportRegistrations(@PathParam("form_id") String formID) {
        UUID form_id;

        try {
            form_id = UUID.fromString(formID);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }
        return RegistrationDAO.getInstance().loadRegistrationContainersForForm(form_id);
    }

    /**
     * This method is used to load a RegistrationResource to follow through with the request.
     * @param id of type String, representing the RegistrationID.
     * @return of type RegistrationResource.
     */
    @Path("/{registrationID}")
    @RolesAllowed("PUBLIC")
    public RegistrationResource handleRegistration(@PathParam("registrationID") String id) {
        UUID registrationID;

        try {
            registrationID = UUID.fromString(id);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }

        return new RegistrationResource(uriInfo, request, registrationID);
    }
}
