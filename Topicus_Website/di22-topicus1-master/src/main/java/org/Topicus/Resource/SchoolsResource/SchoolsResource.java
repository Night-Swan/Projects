package org.Topicus.Resource.SchoolsResource;

import java.util.ArrayList;
import java.util.List;
import java.util.UUID;
import java.util.stream.Collectors;

import org.Topicus.DAO.SchoolDAO.SchoolDAO;
import org.Topicus.Model.School.School;
import org.Topicus.Payload.Request.School.SchoolCreationRequest;
import org.Topicus.Payload.Response.School.SchoolDetails;
import org.Topicus.Payload.Response.School.SchoolName;
import org.Topicus.Resource.SchoolResource.SchoolResource;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.SchoolParser;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.GET;
import jakarta.ws.rs.POST;
import jakarta.ws.rs.Path;
import jakarta.ws.rs.PathParam;
import jakarta.ws.rs.Produces;
import jakarta.ws.rs.QueryParam;
import jakarta.ws.rs.core.Context;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.UriInfo;

/*
This resource class is used to access information about the school.
 */
@Path("/schools")
public class SchoolsResource {
    // FIELD VARIABLE(S) -------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;

    // METHOD(S) -----------------------------------------------

    /**
     * This method is used to return all the schools which are currently on the
     * application.
     * 
     * @return of type List<School>.
     */
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public List<School> getAllSchools() {
        return SchoolDAO.getInstance().getAll();
    }

    @Path("/details")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public List<SchoolDetails> getAllSchoolDetails() {
        return SchoolDAO.getInstance().getAllSchoolDetails();
    }

    /**
     * This method is used to return all the names of the schools in the database
     * that contain a specific string
     * 
     * @return of type List<SchoolName>.
     */
    @Path("/names")
    @GET
    @Produces(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public List<SchoolName> getAllNames(@QueryParam("term") String searchTerm) {
        List<SchoolName> allNames = SchoolDAO.getInstance().getAllNames();
        List<SchoolName> filteredNames = new ArrayList<>();
        // Filter the results based on the search term
        if (searchTerm != null && !searchTerm.isEmpty()) {
            String searchTermLowerCase = searchTerm.toLowerCase();
            filteredNames = allNames.stream()
                    .filter(schoolName -> schoolName.getName().toLowerCase().contains(searchTermLowerCase))
                    .collect(Collectors.toList());
        }
        return filteredNames;
    }

    /**
     * This method is used to create a new school.
     * 
     * @param schoolCreationRequest of type SchoolCreationRequest.
     * @return of type School.
     */
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @Produces(MediaType.APPLICATION_JSON)
    public School createSchool(SchoolCreationRequest schoolCreationRequest) {
        return SchoolDAO.getInstance().save(SchoolParser.parseSchoolCreationRequest(schoolCreationRequest));
    }

    /**
     * This method is used to handle a request to a particular school by instantiating the SchoolResource.
     * @param id of type String.
     * @return of type SchoolResource.
     */
    @Path("{school_id}")
    @RolesAllowed("PUBLIC")
    public SchoolResource handleSchool(@PathParam("school_id") String id) {
        UUID schoolID;

        try {
            schoolID = UUID.fromString(id);
        } catch (IllegalArgumentException e) {
            LoggerManager.RESOURCE_LOGGER.severe(e.getMessage());
            return null;
        }

        return new SchoolResource(uriInfo, request, schoolID);
    }
}
