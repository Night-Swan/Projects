package org.Topicus;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;

public class ApplicationTests {

    public static void main(String[] args) {
        List<String> countryList = new ArrayList<>(Arrays.asList(Locale.getISOCountries()));

        for (String countryCode : countryList) {
            Locale locale = new Locale("", countryCode);
            String countryName = locale.getDisplayCountry();
            System.out.println(countryCode);
            System.out.println(countryName);
        }
    }
}
