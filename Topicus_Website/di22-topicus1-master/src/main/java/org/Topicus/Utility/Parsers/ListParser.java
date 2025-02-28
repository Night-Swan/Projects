package org.Topicus.Utility.Parsers;

import java.util.Arrays;
import java.util.List;

public interface ListParser {
    default List<String> getListFromString(String given_names) {
        return Arrays.asList(given_names.split(", "));
    }
    default String getStringFromList(List<String> given_names) {
        if(given_names != null) return String.join(", ", given_names);
        else return null;
    }
}
