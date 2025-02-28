package org.Topicus.Resource.Access;

import org.Topicus.DAO.SystemUserDAO.SystemUserDAO;
import org.Topicus.Model.SystemUser.SystemUser;
import org.Topicus.Payload.Request.Login.LoginRequest;
import org.Topicus.Service.CookieService;
import org.Topicus.Service.PasswordService;

import jakarta.annotation.security.RolesAllowed;
import jakarta.ws.rs.Consumes;
import jakarta.ws.rs.POST;
import jakarta.ws.rs.Path;
import jakarta.ws.rs.core.MediaType;
import jakarta.ws.rs.core.Response;

/**
 * A specific resource for log-in requests, which takes the requests, processes it, compares values with ones that are stored,
 * and then returns an appropriate response.
 */
@Path("/login")
public class LoginResource {

    /**
     * This method processes the log-in request and then handles any necessary processing.
     * @param request of type LoginRequest.
     * @return of type Response.
     */
    @POST
    @Consumes(MediaType.APPLICATION_JSON)
    @RolesAllowed("PUBLIC")
    public Response processLogin(LoginRequest request) {
        SystemUser user = SystemUserDAO.instance.get(request.getEmail());

        if(user == null) {
            // return not found
            return Response.status(Response.Status.NOT_FOUND).build();
        }

        String user_id = user.getAccount_id().toString();
        String stored_hash = user.getPassword_value();
        byte[] salt = SystemUserDAO.instance.getPasswordSaltforUser(user.getAccount_id());
        String hashed = PasswordService.hashPassword(request.getPassword(), salt);
        if (hashed.equals(stored_hash)) {
            return Response.ok().cookie(CookieService.getInstance().createLoginCookie(user_id, user.getType().toString())).build();
        }

        return Response.status(Response.Status.UNAUTHORIZED).entity("{\"message\":\"Invalid password.\"}").build();
    }
}
