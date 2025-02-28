package org.Topicus.DAO.ChildDAO;

import java.sql.Connection;
import java.sql.Date;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.Contract.DAO;
import org.Topicus.Model.Child.Child;
import org.Topicus.Utility.Builders.ConnectionPackageBuilder;
import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.ChildParser;
import org.Topicus.Utility.Parsers.DateParser;
import org.Topicus.Utility.Parsers.ListParser;

public enum ChildDAO implements DAO<Child>, ListParser, DateParser {
    instance;

    // QUERY(IES) ------------------------------------------

    private final static String LOAD_CHILD = "SELECT * FROM t_child WHERE child_id = ?";

    private final static String LOAD_ALL_CHILDREN = "SELECT * FROM t_child";

    private final static String LOAD_CHILDREN_FOR_PARENT = "SELECT * FROM t_child WHERE child_id IN (SELECT child_id FROM t_guardian_child WHERE guardian_id = ?)";

    private final static String LINK_CHILD_TO_PARENT = "INSERT INTO t_guardian_child(guardian_id, child_id) VALUES(?, ?) RETURNING *";

    private final static String INSERT_CHILD = "INSERT INTO t_child(child_id, surname, given_names, preferred_name, date_of_birth, bsn, nationality, languages) VALUES(?, ? , ?, ?, ?, ?, ?, ?) RETURNING *";

    private final static String UPDATE_CHILD = "UPDATE t_child SET child_id = ?, surname = ?, given_names = ?, preferred_name = ?, date_of_birth = ?, bsn = ?, nationality = ?, languages = ? WHERE child_id = ? RETURNING *";

    private final static String DELETE_CHILD_LINKS = "DELETE FROM t_guardian_child WHERE child_id = ?";

    private final static String DELETE_CHILD_LINK = "DELETE FROM t_guardian_child WHERE guardian_id = ? AND child_id = ?";

    // CONSTRUCTOR(S) --------------------------------------
    ChildDAO() {

    }

    // ACCESS METHOD(S) ------------------------------------

    /**
     * Method to return enum instance of DAO class.
     * 
     * @return of type ChildDAO.
     */
    public static ChildDAO getInstance() {
        return instance;
    }

    // METHOD(S) ----------------------------------------------

    /**
     * Method for getting a child from the database.
     * 
     * @param id of type UUID.
     * @return of type Child.
     */
    @Override
    public Child get(UUID id) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(LOAD_CHILD)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, id);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();
            if (!resultSet.next()) {
                return null;
            }

            Child child = ChildParser.parseChild(resultSet);

            if (resultSet.next()) {
                LoggerManager.DAO_LOGGER.warning("more than one child with id: " + id);
            }

            return child;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for getting all children from the database.
     * 
     * @return of type List<Child>.
     */
    @Override
    public List<Child> getAll() {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(LOAD_ALL_CHILDREN)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<Child> children = new ArrayList<>();
            while (resultSet.next()) {
                children.add(ChildParser.parseChild(resultSet));
            }
            return children;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for getting all children for a specific parent from the database.
     * 
     * @param parentID of type UUID.
     * @return of type List<Child>.
     */
    public List<Child> getChildrenForParent(UUID parentID) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(LOAD_CHILDREN_FOR_PARENT)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);
            preparedStatement.setObject(1, parentID);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            List<Child> children = new ArrayList<>();
            while (resultSet.next()) {
                children.add(ChildParser.parseChild(resultSet));
            }
            return children;
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method for linking a child to a parent in the database.
     * 
     * @param parentID of type UUID.
     * @param childID  of type UUID.
     * @return of type boolean.
     */
    public boolean linkChildToParent(UUID parentID, UUID childID) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(LINK_CHILD_TO_PARENT)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, parentID);
            preparedStatement.setObject(2, childID);
            preparedStatement.execute();
            ResultSet resultSet = preparedStatement.getResultSet();

            return resultSet.next();
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return false;
        }
    }

    /**
     * Method for updating the record of a child in the database(either insert or
     * update).
     * 
     * @param child       of type Child.
     * @param modifyQuery of type String.
     * @return of type Child.
     */
    private Child updateRecord(Child child, String modifyQuery, boolean is_update) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(modifyQuery)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            String given_names = getStringFromList(child.getGivenNames());
            Date birth_date = getDate(child.getBirthDate());
            String languages = getStringFromList(child.getLanguages());
            preparedStatement.setObject(1, child.getChildID());
            preparedStatement.setString(2, child.getSurname());
            preparedStatement.setString(3, given_names);
            preparedStatement.setString(4, child.getPreferredName());
            preparedStatement.setDate(5, birth_date);
            preparedStatement.setString(6, child.getBsn());
            preparedStatement.setString(7, child.getNationality());
            preparedStatement.setString(8, languages);
            if (is_update) {
                preparedStatement.setObject(9, child.getChildID());
            }
            preparedStatement.execute();
            ResultSet result = preparedStatement.getResultSet();

            if (!result.next()) {
                LoggerManager.DAO_LOGGER
                        .warning("no records were updated when updating child with id: " + child.getChildID());
                return null;
            }

            return ChildParser.parseChild(result);

        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return null;
        }
    }

    /**
     * Method to save a child to the database.
     * 
     * @param child of type Child.
     * @return of type Child.
     */
    @Override
    public Child save(Child child) {
        child.setChildID(UUID.randomUUID());
        if (get(child.getChildID()) != null) {
            LoggerManager.DAO_LOGGER.warning("Child with id: " + child.getChildID() + " already exists");
            return null;
        }
        return updateRecord(child, INSERT_CHILD, false);
    }

    /**
     * Method for saving and linking a child to a parent in the database.
     * 
     * @param child    of type Child.
     * @param parentID of type UUID.
     * @return of type Child.
     */
    public Child saveAndLink(Child child, UUID parentID) {
        Child savedChild = save(child);
        if (savedChild == null) {
            return null;
        }

        if (!linkChildToParent(parentID, savedChild.getChildID())) {
            LoggerManager.DAO_LOGGER.warning("Failed to link child with id: " + savedChild.getChildID()
                    + " to parent with id: " + parentID);
        }

        return savedChild;
    }

    /**
     * Method to update a child in the database.
     * 
     * @param child of type Child.
     * @return of type Child.
     */
    @Override
    public Child update(Child child) {
        if (get(child.getChildID()) == null) {
            LoggerManager.DAO_LOGGER.warning("child with id " + child.getChildID() + " does not exist");
            return null;
        }
        return updateRecord(child, UPDATE_CHILD, true);
    }

    /**
     * Method to delete a child from the database.
     * 
     * @param id of type UUID.
     */
    @Override
    public void delete(UUID id) {
        // delete all links to parents
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_CHILD_LINKS)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, id);
            preparedStatement.executeUpdate();
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    /**
     * Method to delete a link between a child and a parent in the database.
     * 
     * @param guardianID of type UUID.
     * @param childID    of type UUID.
     */
    public void deleteLink(UUID guardianID, UUID childID) {
        try (Connection connection = DriverManager.getConnection(ConnectionPackageBuilder.CONNECTION_STRING,
                ConnectionPackageBuilder.USERNAME, ConnectionPackageBuilder.PASSWORD);
                PreparedStatement preparedStatement = connection.prepareStatement(DELETE_CHILD_LINK)) {
            connection.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
            preparedStatement.setObject(1, guardianID);
            preparedStatement.setObject(2, childID);
            preparedStatement.execute();
        } catch (SQLException e) {
            LoggerManager.DAO_LOGGER.severe(e.getMessage());
            return;
        }
    }

    @Override
    public Connection requestConnection() {
        return null;
    }
}
