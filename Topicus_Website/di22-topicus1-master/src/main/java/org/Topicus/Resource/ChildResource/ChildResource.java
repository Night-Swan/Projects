package org.Topicus.Resource.ChildResource;

import java.util.UUID;

import org.Topicus.DAO.ChildDAO.ChildDAO;
import org.Topicus.DAO.ParentDAO.ParentDAO;
import org.Topicus.Model.Child.Child;
import org.Topicus.Security.ThreatPrevention.InputValidator;
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

/**
 * Class to handle requests for a specific child.
 */
public class ChildResource {
    // FIELD VARIABLE(S) ------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;
    UUID childID;

    // CONSTRUCTOR(S) --------------------------
    public ChildResource(UriInfo uriInfo, Request request, UUID childID) {
        this.uriInfo = uriInfo;
        this.request = request;
        this.childID = childID;
    }

    // METHOD(S) --------------------------------

    /**
     * Method to return the details of the child.
     * 
     * @return of type Child, representing the child.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("GUARDIAN")
    public Child getChild() {
        Child child = ChildDAO.getInstance().get(childID);

        if (child == null) {
            LoggerManager.RESOURCE_LOGGER.warning("could not find child with id: " + childID);
        }

        return child;
    }

    /**
     * This method is used to update a child.
     * 
     * @param child of type Child, representing the child to be updated.
     * @return of type Child, representing the updated child.
     */
    @PUT
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("GUARDIAN")
    public Child updateChild(Child child) {

        if (!InputValidator.isValidChild(child)) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid input for updating child with id: " + childID);
            return null;
        }

        if (!child.getChildID().equals(childID)) {
            LoggerManager.RESOURCE_LOGGER.warning("id " + childID + " deduced from the path is different from the id "
                    + child.getChildID() + " of the JSON object");
            return null;
        }

        Child updatedChild = ChildDAO.getInstance().update(child);

        if (updatedChild == null) {
            LoggerManager.RESOURCE_LOGGER.warning("Child with id: " + childID + " could not be updated");
        }

        return updatedChild;
    }

    /**
     * This method is used to delete a child.
     * 
     */
    @DELETE
    @RolesAllowed("GUARDIAN")
    public void deleteChild() {
        ChildDAO.getInstance().delete(childID);
    }

    /**
     * Method for linking a child to a guardian. Remember that
     * a child can have multiple guardians, and a guardian can have multiple
     * children.
     * 
     * @param guardianID of type UUID, representing the id of the guardian to be
     *                   linked.
     */
    @Path("/link")
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @RolesAllowed("GUARDIAN")
    public Response linkGuardian(UUID guardianID) {

        Response badRequestResponse = Response.status(Response.Status.BAD_REQUEST).build();

        if (ParentDAO.getInstance().get(guardianID) == null) {
            LoggerManager.RESOURCE_LOGGER.warning("Parent with id: " + guardianID + " does not exist");
            return badRequestResponse;
        }

        boolean linked = ChildDAO.getInstance().linkChildToParent(guardianID, childID);

        return linked ? Response.ok().build() : badRequestResponse;
    }
}
