package org.Topicus.DAO.Contract;

import java.sql.Connection;
import java.sql.SQLException;
import java.util.List;
import java.util.UUID;

/**
 * Simple Interface for Data Access Object class, performing CRUD operations on objects of type <T>.
 * @param <T>
 */
public interface DAO<T> {
    /**
     * Method to get the particular instance of an object by the UUID parameter.
     * @param id of type UUID, representing the id of the element.
     * @return of type <T>.
     */
    T get(UUID id) throws SQLException;

    /**
     * Method for returning all objects from the database.
     * @return of type <T>
     */
    List<T> getAll();

    /**
     * Method to save an object (store it in the database).
     * Better practice to return the newly created object.
     * @param t of type <T>
     * @return of type <T>
     */
    T save(T t);

    /**
     * Method to update an existing object in the database (if not found, create new).
     * @param t of type <T>
     * @return T of type <T>, representing the object with the changes.
     */
    T update(T t);

    /**
     * Method to delete an object in the database.
     * @param id the id of the object
     */
    void delete(UUID id);

    /**
     * Method to request a connection over which the SQL Transactions can take place.
     * @return of type Connection.
     */
    Connection requestConnection();

}
