package org.Topicus.Resource.ParentResource;

import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.ChildDAO.ChildDAO;
import org.Topicus.DAO.ParentDAO.ParentDAO;
import org.Topicus.Model.Child.Child;
import org.Topicus.Model.Guardian.Guardian;
import org.Topicus.Security.ThreatPrevention.InputValidator;
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

/*
Class to manage resource requests for a singular parent.
 */
public class ParentResource {
    // FIELD VARIABLE(S) ----------------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;
    UUID parentID;

    // CONSTRUCTOR(S) ---------------------------------------------
    public ParentResource(UriInfo uriInfo, Request request, UUID parentID) {
        this.uriInfo = uriInfo;
        this.request = request;
        this.parentID = parentID;
    }

    // METHOD(S) --------------------------------------------------

    /**
     * This method is used to retrieve a particular guardian with the ID that is passed to the constructor of the class.
     * @return of type Guardian.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Guardian getGuardian() {
        Guardian guardian = ParentDAO.getInstance().get(parentID);

        if (guardian == null) {
            LoggerManager.RESOURCE_LOGGER.warning("could not find parent with id: " + parentID);
        }

        return guardian;
    }

    /**
     * This method returns a list of the children that are linked to a particular guardian.
     * @return of type List<Child>
     */
    @Path("/children")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("GUARDIAN")
    public List<Child> getChildren() {
        return ChildDAO.getInstance().getChildrenForParent(parentID);
    }

    /**
     * This method is used to update a parent with the appropriate changes/data.
     * 
     * @return the updated parent
     */
    @PUT
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Guardian updateParent(Guardian guardian) {

        if (!InputValidator.isValidParent(guardian)) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid input for parent update for id: " + parentID);
            return null;
        }

        if (parentID == null || guardian == null) {
            LoggerManager.RESOURCE_LOGGER.warning("cannot perform update on null parent or id");
            return null;
        }

        return ParentDAO.getInstance().update(guardian);
    }

    /**
     * This method is invoked when a DELETE request is sent to the URI.
     */
    @DELETE
    public void deleteParent() {
        if (parentID != null) {
            ParentDAO.getInstance().delete(parentID);
        }
    }
}
