package org.Topicus.Resource.FileResource;

import jakarta.ws.rs.GET;
import jakarta.ws.rs.Path;
import jakarta.ws.rs.core.Context;
import jakarta.ws.rs.core.Request;
import jakarta.ws.rs.core.UriInfo;

import java.io.File;

/**
 * This class is used to manage any file upload from the client to the application.
 */
@Path("/fileUpload")
public class FileResource {
    // FIELD VARIABLE(S)
    // -----------------------------------------------------------------------------------------------
    @Context
    UriInfo uriInfo;
    @Context
    Request request;

    // CONSTRUCTOR(S)
    // --------------------------------------------------------------------------------------------------
    public FileResource(UriInfo uriInfo, Request request) {
        this.uriInfo = uriInfo;
        this.request = request;
    }

    @GET
    public File getFile(String fileRequest) {
        return null;
    }

    // METHOD(S) -------------------------------------------------------------------------------------------------------

}
