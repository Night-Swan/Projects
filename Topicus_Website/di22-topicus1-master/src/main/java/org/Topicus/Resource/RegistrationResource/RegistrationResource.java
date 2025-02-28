package org.Topicus.Resource.RegistrationResource;

import java.util.List;
import java.util.UUID;

import jakarta.ws.rs.*;
import org.Topicus.DAO.RegistrationDAO.RegistrationDAO;
import org.Topicus.Model.Modification.Modification;
import org.Topicus.Model.Registration.DBDataField;
import org.Topicus.Model.Registration.Registration;
import org.Topicus.Model.RegistrationForm.Style.Style;
import org.Topicus.Payload.Request.Registration.FieldCreationRequest;
import org.Topicus.Payload.Request.Registration.FieldUpdateRequest;
import org.Topicus.Payload.Request.Registration.ModificationCreationRequest;
import org.Topicus.Payload.Request.Registration.RegistrationStatusUpdateRequest;
import org.Topicus.Payload.Response.Registration.ModificationListView;
import org.Topicus.Payload.Response.Registration.RegistrationContainer;
import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.DELETE;
import jakarta.ws.rs.GET;
import jakarta.ws.rs.POST;
import jakarta.ws.rs.PUT;
import jakarta.ws.rs.Path;
import jakarta.ws.rs.Produces;
import jakarta.ws.rs.core.Context;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.Response;
import jakarta.ws.rs.core.UriInfo;

/*
This class is used for managing queries and updates for specific Registrations, which may be required by Parents or Administrators alike.
 */
public class RegistrationResource {
    // FIELD VARIABLES ----------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;
    UUID registrationID;

    // CONSTRUCTOR(S) ---------------------------------------
    public RegistrationResource(UriInfo uriInfo, Request request, UUID registrationID) {
        this.uriInfo = uriInfo;
        this.request = request;
        this.registrationID = registrationID;
    }

    // METHOD(S) -----------------------------------------------

    /**
     * This method is used to return a singular registration corresponding to the
     * URI the request was sent to.
     * 
     * @return of type Registration.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Registration getRegistration() {
        Registration registration = RegistrationDAO.getInstance().get(registrationID);

        if (registration == null) {
            LoggerManager.RESOURCE_LOGGER.warning("no registration for id: " + registrationID);
            return null;
        }

        return registration;
    }

    /**
     * This method is used to update a registration with the appropriate
     * changes/data.
     * 
     * @return of type Registration, representing the updated registration (update
     *         changes need to be validated in the database).
     */
    @PUT
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Registration updateRegistrationData(RegistrationStatusUpdateRequest registration) {
        if (registrationID == null || registration == null || !registration.isValidRequest()) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid registration status update request");
            return null;
        }

        return RegistrationDAO.getInstance().updateRegistrationStatus(registration);
    }

    /**
     * This method is invoked when a DELETE request is sent to the URI.
     */
    @DELETE
    @RolesAllowed("PUBLIC")
    public Response deleteRegistration() {
        if (registrationID != null) {
            if (RegistrationDAO.getInstance().deleteFields(registrationID)) {
                RegistrationDAO.getInstance().delete(registrationID);
                return Response.noContent().build();
            }
        }
        return Response.status(500).build();
    }

    /**
     * This method is used to return the data fields corresponding to the
     * Registration.
     * 
     * @return of type RegistrationContainer.
     */
    @Path("/fields")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public RegistrationContainer getDataFields() {
        Registration registration = RegistrationDAO.getInstance().get(registrationID);

        if (registration == null) {
            LoggerManager.RESOURCE_LOGGER.warning("no registration for id: " + registrationID);
            return null;
        }

        RegistrationContainer container = RegistrationDAO.getInstance().loadDataFieldsForRegistration(registrationID,
                registration);

        if (container == null) {
            LoggerManager.RESOURCE_LOGGER.warning("no registration container for registration id: " + registrationID);
            return null;
        }

        return container;
    }

    /**
     * This method is used to update the data fields corresponding to a
     * Registration.
     * 
     * @return of RegistrationContainer, the object sent back to show the changes.
     */
    @Path("/fields")
    @PUT
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public List<DBDataField> updateDataFields(List<FieldUpdateRequest> dataFields) {
        if (registrationID == null || dataFields == null) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid data field update request");
            return null;
        }

        List<FieldUpdateRequest> impurities = dataFields.stream().filter(df -> {
            if (!df.isValidRequest()) {
                return df.getConvertedRegistrationID() != registrationID;
            }
            return false; // if an invalid request, it is marked as an impurity, and transaction not
                          // carried out.
        }).toList();

        if (impurities.size() > 0) {
            LoggerManager.RESOURCE_LOGGER.warning("data field update request contains impurities");
            return null;
        }

        if (RegistrationDAO.getInstance().validateListCountDataField(registrationID) != dataFields.size()) {
            LoggerManager.RESOURCE_LOGGER.warning("data field update request contains invalid count");
            return null;
        }

        return RegistrationDAO.getInstance().updateDataFieldsForRegistration(dataFields, registrationID);
    }

    /**
     * This is the method to add the data fields to a Registration.
     * 
     * @param dataFieldAdditions representing the additions from the client.
     * @return of type List<DataField>.
     */
    @Path("/fields")
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public List<DBDataField> saveDataFields(List<FieldCreationRequest> dataFieldAdditions) {
        if (dataFieldAdditions == null || dataFieldAdditions.isEmpty()) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid data field addition request");
            return null;
        }

        if (RegistrationDAO.getInstance().validateListCountFormComponent(registrationID) != dataFieldAdditions.size()) {
            LoggerManager.RESOURCE_LOGGER.warning("data field addition request contains invalid form component count");
            return null;
        }

        return RegistrationDAO.getInstance().saveDataFields(dataFieldAdditions);
    }

    /**
     * This is the method for being able to see historic modifications to a
     * registration.
     * checked ones.
     * 
     * @return of type ModificationListView.
     */
    @Path("/modifications")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public List<ModificationListView> getModifications() {
        System.out.println("Modifications Path Reached");
        return RegistrationDAO.getInstance().loadModificationsForRegistration(registrationID);
    }

    /**
     * This method is used to provide the modifications for a parent that are
     * visible.
     * 
     * @return of type List<ModificationListView>
     */
    @Path("/modificationsForParent")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public List<ModificationListView> getParentModifications() {
        System.out.println("Modifications Path Reached");
        return RegistrationDAO.getInstance().loadModificationsForParent(registrationID);
    }

    /**
     * This is a method for the school administrator to perform a modification.
     * 
     * @param mcr of type ModificationCreationRequest.
     * @return of type Modification.
     */
    @Path("/modifications")
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("SCHOOL_ADMIN")
    public Modification addModification(ModificationCreationRequest mcr) {
        if (mcr != null && mcr.isValidRequest()) {
            return RegistrationDAO.getInstance().saveModification(mcr.getConvertedSA_ID(), mcr.getConvertedREG_ID(),
                    mcr.getDescription(), mcr.isVisible());
        }
        return null;
    }

    /**
     * This method is used to retrieve the style for a particular school.
     * @param formID of type String, representing the ID of the form.
     * @return of type Style.
     */
    @Path("/style")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Style getFormStyle(@QueryParam("formID") String formID) {
        UUID uuid;
        try {
            uuid = UUID.fromString(formID);
            System.out.println(uuid);
        } catch (IllegalArgumentException e) {
            return null;
        }
        return RegistrationDAO.getInstance().getStyle(uuid);
    }
}
