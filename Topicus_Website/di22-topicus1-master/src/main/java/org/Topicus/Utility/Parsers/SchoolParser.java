package org.Topicus.Utility.Parsers;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

import org.Topicus.Model.School.School;
import org.Topicus.Payload.Request.School.SchoolCreationRequest;
import org.Topicus.Payload.Response.School.SchoolDetails;
import org.Topicus.Payload.Response.School.SchoolName;

public interface SchoolParser {
    /**
     * parse the information from the database about a school into a School object
     * 
     * @param resultSet the result of a query which returns data for a school
     * @return the School object created with the data from the query
     * @throws SQLException
     */
    static School parseSchool(ResultSet resultSet) throws SQLException {
        return new School(
                resultSet.getObject(1, UUID.class),
                resultSet.getObject(2, UUID.class),
                resultSet.getString(3),
                resultSet.getString(4),
                resultSet.getString(5),
                resultSet.getString(6));
    }

    static SchoolDetails parseSchoolDetails(ResultSet rs) throws SQLException {
        return new SchoolDetails(
                rs.getObject(1, UUID.class),
                rs.getObject(2, UUID.class),
                rs.getString(3),
                rs.getString(4),
                rs.getString(5),
                rs.getString(6),
                rs.getString(7),
                rs.getString(8),
                rs.getInt(9),
                rs.getString(10),
                rs.getString(11),
                rs.getString(12));
    }

    /**
     * parse the information for multiple schools from the database
     * 
     * @param resultSet result of a query for multiple rows of school
     * @return a list with all the school objects retrieved from the database
     * @throws SQLException
     */
    default List<School> parseSchools(ResultSet resultSet) throws SQLException {
        List<School> schools = new ArrayList<>();
        while (resultSet.next()) {
            schools.add(parseSchool(resultSet));
        }
        return schools;
    }

    /**
     * method for parsing the SchoolName class used to get the name of a single
     * school
     * 
     * @param resultSet a single row containing the name of a school
     * @return a SchoolName object
     * @throws SQLException
     */
    default SchoolName parseName(ResultSet resultSet) throws SQLException {
        return new SchoolName(resultSet.getString(1), resultSet.getString(2));
    }

    /**
     * method for creating a list of objects with the names of all schools
     * 
     * @param resultSet all the name of each school in the database
     * @return a list of SchoolName
     * @throws SQLException
     */
    default List<SchoolName> parseSchoolNames(ResultSet resultSet) throws SQLException {
        List<SchoolName> names = new ArrayList<>();
        while (resultSet.next()) {
            names.add(parseName(resultSet));
        }
        return names;
    }

    /**
     * Method for parsing a SchoolCreationRequest object into a School object
     * 
     * @param schoolCreationRequest the request to be parsed
     * @return a School object
     */
    static School parseSchoolCreationRequest(SchoolCreationRequest schoolCreationRequest) {
        return new School(schoolCreationRequest.getAddress_id(), schoolCreationRequest.getName(),
                schoolCreationRequest.getType(), schoolCreationRequest.getPhone_number(),
                schoolCreationRequest.getEmail());
    }
}
