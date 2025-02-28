package org.Topicus.Utility.Parsers;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.List;
import java.util.UUID;

import org.Topicus.Model.Address.Address;
import org.Topicus.Model.Guardian.Guardian;
import org.Topicus.Payload.Request.Parent.ParentCreationRequest;
import org.Topicus.Payload.Response.Parent.GuardianDetails;
import org.Topicus.Utility.Logs.LoggerManager;

public interface ParentParser {
    /**
     * parse a parent from the database
     *
     * @param resultSet the result of a query which returns a parent
     * @return the Guardian object created with the info from the resultSet
     */
    default Guardian parseParent(ResultSet resultSet) throws SQLException {
        Guardian guardian;
        UUID guardian_id = resultSet.getObject(1, UUID.class);
        UUID account_id = resultSet.getObject(2, UUID.class);
        UUID address_id = resultSet.getObject(3, UUID.class);
        String nationality = resultSet.getString(4);
        String surname = resultSet.getString(5);
        String phone_number = resultSet.getString(6);
        Date date_of_birth = getConvertedDate(resultSet.getDate(7));// take a look
        String given_names = resultSet.getString(8);
        List<String> names = given_names == null ? null : Arrays.asList(resultSet.getString(8).split(", "));
        String occupation = resultSet.getString(9);
        String company_name = resultSet.getString(10);
        guardian = new Guardian(guardian_id, account_id, address_id, nationality, surname, phone_number, date_of_birth,
                names, occupation, company_name);
        return guardian;
    }

    /**
     * parses multiple parents from the database
     *
     * @param resultSet result of a query for multiple parent rows
     * @return a list of Guardian objects containing the info from the resultSet
     */
    default List<Guardian> parseParents(ResultSet resultSet) throws SQLException {
        List<Guardian> guardians = new ArrayList<>();
        while (resultSet.next()) {
            guardians.add(parseParent(resultSet));
        }
        return guardians;
    }

    /**
     * parse the details of a guardian
     *
     * @param resultSet the result of a query which returns details of a parent
     * @return a GuardianDetails object containing the info from the resultSet
     */
    default GuardianDetails parseGuardianDetails(ResultSet resultSet) throws SQLException {
        GuardianDetails detail = new GuardianDetails(
                resultSet.getObject(1, UUID.class), // account_id ?
                resultSet.getObject(2, UUID.class), // guardian_id ?
                resultSet.getString(3), // email
                resultSet.getString(4), // nationality
                resultSet.getString(5), // surname
                resultSet.getString(6), // "phone_number"
                getConvertedDate(resultSet.getDate(7)), // "date_of_birth"
                resultSet.getString(8), // "given_names"
                resultSet.getString(9), // "occupation"
                resultSet.getString(10));// "company_name"
        return detail;
    }

    /**
     * parse the address of a guardian
     *
     * @param resultSet the result of a query which returns address of a parent
     * @return an Address object containing the info from the resultSet
     */
    default Address parseGuardianAddress(ResultSet resultSet) throws SQLException {
        Address address = new Address(
                resultSet.getObject(1, UUID.class), // address_id
                resultSet.getString(2), // postal_code
                resultSet.getString(3), // street_name
                resultSet.getInt(4), // street_number
                resultSet.getString(5), // city
                resultSet.getString(6), // country
                resultSet.getString(7));// phone_number
        return address;
    }

    /**
     * convert a date into the right format and check it
     * 
     * @param date_of_birth the date_of _birth from the database
     * @return the correct date
     */
    default Date getConvertedDate(Date date_of_birth) {
        if (date_of_birth == null) {
            return null;
        }
        Date date = null;
        SimpleDateFormat formatter1 = new SimpleDateFormat("yyyy-MM-dd");
        String dateString = formatter1.format(date_of_birth);
        try {
            date = formatter1.parse(dateString);
        } catch (ParseException e) {
            LoggerManager.UTILITY_LOGGER.severe(e.getMessage());
        }

        return date;
    }

    static Guardian parseParentCreationRequest(ParentCreationRequest parent) {
        return new Guardian(parent.getAccount_id(), parent.getAddress_id(), parent.getNationality(),
                parent.getSurname(),
                parent.getPhone_number(), parent.getBirth_date(), parent.getGiven_names(), parent.getOccupation(),
                parent.getCompany_name());
    }
}
