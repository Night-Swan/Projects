package org.Topicus.Resource.ChildrenResource;

import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.ChildDAO.ChildDAO;
import org.Topicus.Model.Child.Child;
import org.Topicus.Payload.Request.Child.ChildCreationRequest;
import org.Topicus.Resource.ChildResource.ChildResource;
import org.Topicus.Security.ThreatPrevention.InputValidator;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.ChildParser;

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
* This class is used to handle all requests to the /children endpoint.
*/
@Path("/children")
public class ChildrenResource {
    // FIELD VARIABLE(S) -------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;

    // METHOD(S) -----------------------------------------------

    /**
     * This method is used to get all children
     * 
     * @return of type List<Child>, representing all children.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    public List<Child> getChildren() {
        return ChildDAO.getInstance().getAll();
    }

    /**
     * This method is used to create a new child
     * 
     * @param childCreationRequest the request to create a child
     * @return of type Child, representing the created child.
     */
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Child createChild(ChildCreationRequest childCreationRequest) {

        if (!InputValidator.isValidChild(childCreationRequest)) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid input for child creation request");
            return null;
        }

        Child createdChild = ChildDAO.getInstance().saveAndLink(
                ChildParser.parseChildCreationRequest(childCreationRequest), childCreationRequest.getGuardianId());

        if (createdChild == null) {
            LoggerManager.RESOURCE_LOGGER
                    .warning("Failed to create child for guardian id: " + childCreationRequest.getGuardianId());
            return null;
        }

        return createdChild;
    }

    /**
     * This method is used to handle a child by id
     * 
     * @param id of type UUID, representing the id of the child to be retrieved.
     * @return of ChildResource, representing the child to be retrieved.
     */
    @Path("{child_id}")
    @RolesAllowed("PUBLIC")
    public ChildResource handleChild(@PathParam("child_id") String id) {
        UUID childId;

        try {
            childId = UUID.fromString(id);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }

        return new ChildResource(uriInfo, request, childId);
    }
}
