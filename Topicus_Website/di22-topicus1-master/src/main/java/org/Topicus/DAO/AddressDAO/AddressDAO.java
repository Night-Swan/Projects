package org.Topicus.DAO.AddressDAO;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.Contract.DAO;
import org.Topicus.Model.Address.Address;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.AddressParser;

public enum AddressDAO implements DAO<Address> {
    instance;

    // QUERY(IES) ------------------------------------------

    private final static String LOAD_ADDRESS = "SELECT * FROM t_address WHERE address_id = ?";

    private final static String LOAD_ALL_ADDRESSES = "SELECT * FROM t_address";

    private final static String INSERT_ADDRESS = "INSERT INTO t_address(address_id, postal_code, street_name, street_number, city, country, phone_number) VALUES (?, ?, ?, ?, ?, ?, ?) RETURNING *";

    private final static String UPDATE_ADDRESS = "UPDATE t_address SET address_id = ?, postal_code = ?, street_name = ?, street_number = ?, city = ?, country = ?, phone_number = ? WHERE address_id = ? RETURNING *";

    private final static String DELETE_ADDRESS = "DELETE FROM t_address WHERE address_id = ?";

    // CONSTRUCTOR(S) --------------------------------------
    AddressDAO() {

    }

    // ACCESS METHOD(S) ------------------------------------

    /**
     * Method to return enum instance of DAO class.
     * @return of type AddressDAO.
     */
    public static AddressDAO getInstance() {
        return instance;
    }

    // METHOD(S) ----------------------------------------------

    /**
     * Method for getting an address from the database.
     * 
     * @param id of type UUID.
     * @return of type Address.
     */
    @Override
    public Address get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
             PreparedStatement preparedStatement = connection.prepareStatement(LOAD_ADDRESS);) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();

            ResultSet resultSet = preparedStatement.getResultSet();

            if (!resultSet.next()) {
                return null;
            }

            Address address = AddressParser.parseAddress(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("More than one address found with id: " + id);
            }

            return address;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for getting all addresses from the database.
     * 
     * @return of type List<Address>.
     */
    @Override
    public List<Address> getAll() {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(LOAD_ALL_ADDRESSES)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<Address> addresses = new ArrayList<>();
            while (resultSet.next()) {
                addresses.add(AddressParser.parseAddress(resultSet));
            }
            return addresses;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for updating the record of an address in the database(either insert or
     * update).
     * 
     * @param address     of type Address.
     * @param modifyQuery of type String.
     * @param is_update   of type boolean.
     * @return of type Address.
     */
    private Address updateRecord(Address address, String modifyQuery, boolean is_update) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(modifyQuery)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, address.getAddressID());
            preparedStatement.setString(2, address.getPostalCode());
            preparedStatement.setString(3, address.getStreetName());
            preparedStatement.setInt(4, address.getStreetNumber());
            preparedStatement.setString(5, address.getCity());
            preparedStatement.setString(6, address.getCountry());
            preparedStatement.setString(7, address.getPhoneNumber());

            if (is_update) {
                preparedStatement.setObject(8, address.getAddressID());
            }

            preparedStatement.execute();
            ResultSet result = preparedStatement.getResultSet();

            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("no address record was updated for address id: " + address.getAddressID());
                return null;
            }

            return AddressParser.parseAddress(result);

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to save an address to the database.
     * 
     * @param address of type Address.
     * @return of type Address.
     */
    @Override
    public Address save(Address address) {
        address.setAddressID(UUID.randomUUID());
        if (get(address.getAddressID()) != null) {
            LoggerManager.DAO_LOGGER.warning("address with id " + address.getAddressID() + " already exists");
            return null;
        }
        return updateRecord(address, INSERT_ADDRESS, false);
    }

    /**
     * Method to update an address in the database.
     * 
     * @param address of type Address.
     * @return of type Address.
     */
    @Override
    public Address update(Address address) {
        if (get(address.getAddressID()) == null) {
            throw new RuntimeException("address with id " + address.getAddressID() + " does not exist");
        }
        return updateRecord(address, UPDATE_ADDRESS, true);
    }

    /**
     * Method to delete an address from the database.
     * 
     * @param id of type UUID.
     */
    @Override
    public void delete(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_ADDRESS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, id);
            int rowUpdateCount = preparedStatement.executeUpdate();
            if (rowUpdateCount != 1) {
                LoggerManager.DAO_LOGGER.warning(
                        rowUpdateCount + " rows were updated(out of 1) when trying to delete address with id: " + id);
                return;
            }
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
        }
    }

    @Override
    public Connection requestConnection() {
        return null;
    }
}
