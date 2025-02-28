package org.Topicus.Resource.AddressResource;

import java.util.UUID;

import org.Topicus.DAO.AddressDAO.AddressDAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Security.ThreatPrevention.InputValidator;
import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.CookieParam;
import jakarta.ws.rs.DELETE;
import jakarta.ws.rs.GET;
import jakarta.ws.rs.PUT;
import jakarta.ws.rs.Produces;
import jakarta.ws.rs.core.Context;
import jakarta.ws.rs.core.Cookie;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.UriInfo;

/**
 * Class to handle requests for a specific address.
 */
public class AddressResource {
    // FIELD VARIABLE(S) ------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;
    UUID addressID;

    // CONSTRUCTOR(S) --------------------------
    public AddressResource(UriInfo uriInfo, Request request, UUID addressID) {
        this.uriInfo = uriInfo;
        this.request = request;
        this.addressID = addressID;
    }

    // METHOD(S) --------------------------------

    /**
     * Method to return the details of the address.
     * 
     * @return of type Address, representing the address.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Address getAddress(@CookieParam("authorization_token") Cookie cookie) {
        Address address = AddressDAO.getInstance().get(addressID);

        if (address == null) {
            LoggerManager.RESOURCE_LOGGER.warning("could not find address with id: " + addressID);
        }

        return address;
    }

    /**
     * This method is used to update a address.
     * 
     * @param address of type Address, representing the address to be updated.
     * @return of type Address, representing the updated address.
     */
    @PUT
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed({ "GUARDIAN", "SCHOOL_ADMIN" })
    public Address updateAddress(Address address) {
        if (!InputValidator.isValidAddress(address)) {
            LoggerManager.RESOURCE_LOGGER.warning("Invalid input for address update");
            return null;
        }

        if (!address.getAddressID().equals(addressID)) {
            LoggerManager.RESOURCE_LOGGER.warning("id " + addressID + " deduced from the path is different from the id "
                    + address.getAddressID() + " of the JSON object");
            return null;
        }

        Address updatedAddress = AddressDAO.getInstance().update(address);

        if (updatedAddress == null) {
            LoggerManager.RESOURCE_LOGGER.warning("could not perform update for address id: " + addressID);
            return null;
        }

        return updatedAddress;
    }

    /**
     * This method is used to delete a address.
     * 
     */
    @DELETE
    public void deleteAddress() {
        AddressDAO.getInstance().delete(addressID);
    }

}
