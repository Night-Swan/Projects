package org.Topicus.Utility.Parsers;

import org.Topicus.Utility.Logs.LoggerManager;

public interface YearParser {
    /**
     * Method to convert Strings to ints that represent years.
     * 
     * @param year of type String.
     * @return of type int.
     */
    default int convertYearFromString(String year) {
        try {
            return Integer.parseInt(year);
        } catch (NumberFormatException e) {
            LoggerManager.UTILITY_LOGGER.warning(e.getMessage());
            return -1;
        }
    }
}
