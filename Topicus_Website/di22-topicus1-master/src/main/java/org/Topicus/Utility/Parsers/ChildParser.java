package org.Topicus.Utility.Parsers;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.List;
import java.util.UUID;

import org.Topicus.Model.Child.Child;
import org.Topicus.Payload.Request.Child.ChildCreationRequest;

public interface ChildParser {
    /**
     * parse a child from the database
     * 
     * @param resultSet the result of a query which returns a child
     * @return the Child object created with the info from the resultSet
     */
    static Child parseChild(ResultSet resultSet) throws SQLException {
        Child child;
        UUID child_id = resultSet.getObject(1, UUID.class);
        String surname = resultSet.getString(2);
        List<String> given_names = Arrays.asList(resultSet.getString(3).split(", "));
        String preferred_name = resultSet.getString(4);
        Date date_of_birth = new java.util.Date((resultSet.getDate(5)).getTime());
        String bsn = resultSet.getString(6);
        String nationality = resultSet.getString(7);
        List<String> languages = Arrays.asList(resultSet.getString(8).split(", "));
        child = new Child(child_id, surname, given_names, preferred_name, date_of_birth, bsn, nationality, languages);
        return child;
    }

    /**
     * parses multiple children from the database
     * 
     * @param resultSet result of a query for multiple children rows
     * @return a list of Child objects containing the info from the resultSet
     */
    default List<Child> parseChildren(ResultSet resultSet) throws SQLException {
        List<Child> children = new ArrayList<>();
        while (resultSet.next()) {
            children.add(parseChild(resultSet));
        }
        return children;
    }

    static Child parseChildCreationRequest(ChildCreationRequest childCreationRequest) {
        return new Child(childCreationRequest.getSurname(), childCreationRequest.getGivenNames(),
                childCreationRequest.getPreferredName(), childCreationRequest.getBirthDate(),
                childCreationRequest.getBsn(), childCreationRequest.getNationality(),
                childCreationRequest.getLanguages());
    }
}
