package org.Topicus.Utility.Parsers;

import java.util.Date;

public interface DateParser {

    /**
     * convert a date into the right format and check it
     * 
     * @param date_of_birth the date_of _birth from the database
     * @return the correct date
     */
    static java.sql.Date getConvertedDate(String date_of_birth) {
        if (date_of_birth != null)
            return java.sql.Date.valueOf(date_of_birth);
        else
            return null;
    }

    default java.sql.Date getDate(Date date) {
        if (date != null)
            return new java.sql.Date(date.getTime());
        return null;
    }
}
