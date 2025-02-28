package org.Topicus.Utility.Parsers;

import java.util.UUID;

import org.Topicus.Utility.Logs.LoggerManager;

public interface UUIDParser {
    /**
     * Method to convert Strings to UUIDs in the way the application uses them.
     * 
     * @param id of type String.
     * @return of type UUID.
     */
    default UUID convertFromString(String id) {
        try {
            return UUID.fromString(id);
        } catch (IllegalArgumentException e) {
            LoggerManager.UTILITY_LOGGER.warning(e.getMessage());
            return null;
        }
    }
}
