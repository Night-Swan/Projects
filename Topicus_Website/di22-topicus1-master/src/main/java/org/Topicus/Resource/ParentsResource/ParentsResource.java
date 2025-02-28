package org.Topicus.Resource.ParentsResource;

import java.util.List;
import java.util.Map;
import java.util.UUID;

import org.Topicus.DAO.ParentDAO.ParentDAO;
import org.Topicus.Model.Guardian.Guardian;
import org.Topicus.Payload.Request.Parent.ParentCreationRequest;
import org.Topicus.Resource.ParentResource.ParentResource;
import org.Topicus.Security.ThreatPrevention.InputValidator;
import org.Topicus.Service.TokenService;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.ParentParser;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.CookieParam;
import jakarta.ws.rs.GET;
import jakarta.ws.rs.POST;
import jakarta.ws.rs.Path;
import jakarta.ws.rs.PathParam;
import jakarta.ws.rs.Produces;
import jakarta.ws.rs.core.Context;
import jakarta.ws.rs.core.Cookie;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.UriInfo;

/*
A class to access information regarding parents.
 */
@Path("/parents")
public class ParentsResource {
    // FIELD VARIABLE(S) ----------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;

    // CONSTRUCTOR(S) --------------------------
    public ParentsResource(UriInfo uriInfo, Request request) {
        this.uriInfo = uriInfo;
        this.request = request;
    }

    public ParentsResource() {

    }

    /**
     * This method will be invoked when a GET request is sent to the URI, which will
     * return a list of all parents in system
     * 
     * @return of type List<Guardian>.
     */

    @GET
    @Produces(MediaType.APPLICATION_JSON)
    public List<Guardian> getAllParents() {
        return ParentDAO.getInstance().getAll();
    }

    /**
     * This method will be invoked when a POST request is sent to the URI to create
     * a new parent.
     * 
     * @param parent of type Parent.
     * @return of type Parent, representing created Parent.
     */

    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Guardian createParent(@CookieParam("authorization_token") Cookie cookie, ParentCreationRequest parent) {

        if (!InputValidator.isValidParentWithoutAccount(parent)) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid input for creating parent");
            return null;
        }

        if (cookie == null) {
            LoggerManager.RESOURCE_LOGGER.info("no cookie, creating guardian without account");
        } else {
            LoggerManager.RESOURCE_LOGGER.info("found the cookie, creating guardian using token");
            Map<String, String> tokenDetails = TokenService.getTokenDetails(cookie.getValue());

            if (tokenDetails.isEmpty()) {
                LoggerManager.RESOURCE_LOGGER.severe("cookie has no token details, aborting creation of guardian");
                return null;
            }

            UUID user_id = UUID.fromString(tokenDetails.get("user_id"));
            parent.setAccount_id(user_id);
        }

        return ParentDAO.getInstance().save(ParentParser.parseParentCreationRequest(parent));
    }

    // alternative

    /**
     * Method to return a parent by account id.
     * 
     * @param cookie the cookie containing the authorization_token
     * @return of type Parent.
     */
    @Path("/accounts")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Guardian getGuardianByAccount(@CookieParam("authorization_token") Cookie cookie) {

        if (cookie == null) {
            LoggerManager.RESOURCE_LOGGER.warning("no cookie, cannot find guardian");
            return null;
        }

        Map<String, String> tokenDetails = TokenService.getTokenDetails(cookie.getValue());

        if (tokenDetails.isEmpty()) {
            LoggerManager.RESOURCE_LOGGER.severe("cookie has no token details, cannot find guardian");
            return null;
        }

        UUID user_id = UUID.fromString(tokenDetails.get("user_id"));

        Guardian guardian = ParentDAO.instance.getByAccount(user_id);

        if (guardian == null) {
            LoggerManager.RESOURCE_LOGGER.warning("no guardian found for account id: " + user_id);
        }

        return guardian;
    }

    /**
     * creating ParentResource
     * 
     * @param id the id of the parent
     * @return a ParentResource object for the given id
     */
    @Path("{parentID}")
    @RolesAllowed("PUBLIC")
    public ParentResource handleParent(@PathParam("parentID") String id) {
        UUID parentID;

        try {
            parentID = UUID.fromString(id);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }

        return new ParentResource(uriInfo, request, parentID);
    }
}
