package org.Topicus.Utility.Parsers;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.UUID;

import org.Topicus.Model.Address.Address;
import org.Topicus.Payload.Request.Address.AddressCreationRequest;

public class AddressParser {
    /**
     * Method for parsing an address from a result set.
     * 
     * @param resultSet of type ResultSet.
     * @return of type Address.
     */
    public static Address parseAddress(ResultSet resultSet) throws SQLException {
        UUID address_id = resultSet.getObject(1, UUID.class);
        String postal_code = resultSet.getString(2);
        String street_name = resultSet.getString(3);
        int street_number = resultSet.getInt(4);
        String city = resultSet.getString(5);
        String country = resultSet.getString(6);
        String phone_number = resultSet.getString(7);

        return new Address(address_id, postal_code, street_name, street_number, city, country, phone_number);
    }

    public static Address parseAddressCreationRequest(AddressCreationRequest addressCreationRequest) {
        return new Address(addressCreationRequest.getPostalCode(), addressCreationRequest.getStreetName(),
                addressCreationRequest.getStreetNumber(), addressCreationRequest.getCity(),
                addressCreationRequest.getCountry(), addressCreationRequest.getPhoneNumber());
    }

}
