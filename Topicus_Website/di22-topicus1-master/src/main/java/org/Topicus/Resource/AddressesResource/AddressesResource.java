package org.Topicus.Resource.AddressesResource;

import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.AddressDAO.AddressDAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Payload.Request.Address.AddressCreationRequest;
import org.Topicus.Resource.AddressResource.AddressResource;
import org.Topicus.Security.ThreatPrevention.InputValidator;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.AddressParser;

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
* This class is used to handle all requests to the /addresses endpoint.
*/
@Path("/addresses")
public class AddressesResource {
    // FIELD VARIABLE(S) -------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;

    // METHOD(S) -----------------------------------------------

    /**
     * This method is used to get all addresses
     * 
     * @return of type List<Address>, representing all addresses.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    public List<Address> getAddresses() {
        return AddressDAO.getInstance().getAll();
    }

    /**
     * This method is used to create a new address
     * 
     * @param addressCreationRequest of type Address, representing the address to be
     *                               created.
     * @return of type Address, representing the created address.
     */
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Address createAddress(AddressCreationRequest addressCreationRequest) {

        if (!InputValidator.isValidAddress(addressCreationRequest)) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid input for address creation request");
            return null;
        }

        Address createdAddress = AddressDAO.getInstance()
                .save(AddressParser.parseAddressCreationRequest(addressCreationRequest));

        if (createdAddress == null) {
            LoggerManager.RESOURCE_LOGGER.warning("Address creation failed");
        }

        return createdAddress;
    }

    /**
     * This method is used to get a address by id
     * 
     * @param id of type UUID, representing the id of the address to be retrieved.
     * @return of AddressResource, representing the address to be retrieved.
     */
    @Path("{address_id}")
    @RolesAllowed("PUBLIC")
    public AddressResource getAddress(@PathParam("address_id") String id) {
        UUID addressID;

        try {
            addressID = UUID.fromString(id);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }

        return new AddressResource(uriInfo, request, addressID);
    }
}
