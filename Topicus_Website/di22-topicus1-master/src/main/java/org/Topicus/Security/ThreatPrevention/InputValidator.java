package org.Topicus.Security.ThreatPrevention;

import java.time.LocalDate;
import java.time.ZoneId;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.List;
import java.util.Locale;
import java.util.regex.Pattern;

import org.Topicus.Model.Address.Address;
import org.Topicus.Model.Child.Child;
import org.Topicus.Model.Guardian.Guardian;
import org.Topicus.Model.SystemUser.SystemUser;
import org.Topicus.Payload.Request.Address.AddressCreationRequest;
import org.Topicus.Payload.Request.Child.ChildCreationRequest;
import org.Topicus.Payload.Request.Parent.ParentCreationRequest;
import org.Topicus.Payload.Request.SystemUser.SystemUserCreationRequest;
import org.Topicus.Utility.Logs.LoggerManager;

/**
 * this class checks all user input if suits the patterns expected for the
 * database
 */
public class InputValidator {
    // FIELD VARIABLE(S) -----------------------------------
    public static final List<String> NATIONALITIES = Arrays.asList(
            "Afghan", "Albanian", "Algerian", "American", "Andorran", "Angolan", "Antiguans", "Argentinean", "Armenian",
            "Australian",
            "Austrian", "Azerbaijani", "Bahamian", "Bahraini", "Bangladeshi", "Barbadian", "Barbudans", "Batswana",
            "Belarusian",
            "Belgian", "Belizean", "Beninese", "Bhutanese", "Bolivian", "Bosnian", "Brazilian", "British", "Bruneian",
            "Bulgarian",
            "Burkinabe", "Burmese", "Burundian", "Cambodian", "Cameroonian", "Canadian", "Cape Verdean",
            "Central African", "Chadian",
            "Chilean", "Chinese", "Colombian", "Comoran", "Congolese", "Costa Rican", "Croatian", "Cuban", "Cypriot",
            "Czech",
            "Danish", "Djibouti", "Dominican", "Dutch", "East Timorese", "Ecuadorean", "Egyptian", "Emirian",
            "Equatorial Guinean",
            "Eritrean", "Estonian", "Ethiopian", "Fijian", "Filipino", "Finnish", "French", "Gabonese", "Gambian",
            "Georgian", "German",
            "Ghanaian", "Greek", "Grenadian", "Guatemalan", "Guinea-Bissauan", "Guinean", "Guyanese", "Haitian",
            "Herzegovinian",
            "Honduran", "Hungarian", "I-Kiribati", "Icelander", "Indian", "Indonesian", "Iranian", "Iraqi", "Irish",
            "Israeli", "Italian",
            "Ivorian", "Jamaican", "Japanese", "Jordanian", "Kazakhstani", "Kenyan", "Kittian and Nevisian", "Kuwaiti",
            "Kyrgyz", "Laotian",
            "Latvian", "Lebanese", "Liberian", "Libyan", "Liechtensteiner", "Lithuanian", "Luxembourger", "Macedonian",
            "Malagasy",
            "Malawian", "Malaysian", "Maldivian", "Malian", "Maltese", "Marshallese", "Mauritanian", "Mauritian",
            "Mexican",
            "Micronesian", "Moldovan", "Monacan", "Mongolian", "Moroccan", "Mosotho", "Motswana", "Mozambican",
            "Namibian", "Nauruan",
            "Nepalese", "New Zealander", "Ni-Vanuatu", "Nicaraguan", "Nigerian", "Nigerien", "North Korean",
            "Northern Irish", "Norwegian",
            "Omani", "Pakistani", "Palauan", "Panamanian", "Papua New Guinean", "Paraguayan", "Peruvian", "Polish",
            "Portuguese",
            "Qatari", "Romanian", "Russian", "Rwandan", "Saint Lucian", "Salvadoran", "Samoan", "San Marinese",
            "Sao Tomean", "Saudi",
            "Scottish", "Senegalese", "Serbian", "Seychellois", "Sierra Leonean", "Singaporean", "Slovakian",
            "Slovenian", "Solomon Islander",
            "Somali", "South African", "South Korean", "Spanish", "Sri Lankan", "Sudanese", "Surinamer", "Swazi",
            "Swedish", "Swiss",
            "Syrian", "Taiwanese", "Tajik", "Tanzanian", "Thai", "Togolese", "Tongan", "Trinidadian or Tobagonian",
            "Tunisian",
            "Turkish", "Tuvaluan", "Ugandan", "Ukrainian", "Uruguayan", "Uzbekistani", "Venezuelan", "Vietnamese",
            "Welsh", "Yemenite",
            "Zambian", "Zimbabwean");

    private static final Pattern EMAIL_PATTERN = Pattern.compile("^(\\w+\\.?)+@(\\w{2,}\\.?)+$");
    private static final Pattern TEXT_PATTERN = Pattern.compile("^[a-zA-Z\\s-]+$");
    private static final Pattern PHONE_NUMBER_PATTERN = Pattern.compile("^[\\d()+-]+$");
    private static final DateTimeFormatter DATE_FORMATTER = DateTimeFormatter.ofPattern("yyyy-MM-dd");
    private static final Pattern COMPANY_NAME_PATTERN = Pattern.compile("^[\\w\\.\\s-]+$");
    private static final Pattern GIVEN_NAMES_PATTERN = Pattern.compile("^([A-Z][a-z]+(?:\\s+[A-Z][a-z]+)*)$");
    private static final Pattern ROMAN_LETTERS = Pattern
            .compile("^(M{0,3})(CM|CD|D?C{0,3})(XC|XL|L?X{0,3})(IX|IV|V?I{0,3})$");
    private static final Pattern USERNAME_PATTERN = Pattern.compile("^\\w{6,20}$");
    private static final Pattern BSN_PATTERN = Pattern.compile("^\\d{8,9}$");
    private static final Pattern STREET_NUMBER_PATTERN = Pattern.compile("^\\d{0,7}$");

    private static final Pattern STREET_PATTERN = Pattern.compile("^[\\w-\\s]+$");

    // FIELD VALIDITY
    // METHODS--------------------------------------------------------------------------------------------

    /**
     * checks if the language typed in by the user exists
     * 
     * @param g_lang user's language
     * @return true if exists, otherwise false
     */
    private static boolean isValidLanguage(String g_lang) {
        List<String> languageList = new ArrayList<>(Arrays.asList(Locale.getISOLanguages()));

        for (String languageCode : languageList) {
            Locale locale = new Locale(languageCode);
            String languageName = locale.getDisplayLanguage();
            if (g_lang.equals(languageName))
                return true;
        }
        return false;
    }

    /**
     * checks if the country typed in by the user exists
     * 
     * @param g_country user's country
     * @return true if exists, otherwise false
     */
    private static boolean isValidCountry(String g_country) {
        List<String> countryList = new ArrayList<>(Arrays.asList(Locale.getISOCountries()));
        for (String countryCode : countryList) {
            Locale locale = new Locale("", countryCode);
            String countryName = locale.getDisplayCountry();
            if (g_country.equals(countryName))
                return true;
        }
        return false;
    }

    /**
     * checks if the city typed in by the user exists
     * 
     * @param g_city user's city
     * @return true if exists, otherwise false
     */
    private static boolean isValidCity(String g_city) {
        return TEXT_PATTERN.matcher(g_city).matches();
    }

    /**
     * checks if the date of birth typed in by is in the right format
     * 
     * @param date user's birthdate
     * @return true if it is, otherwise false
     */
    private static boolean isDateInFormat(Date date) {
        try {
            LocalDate localDate = date.toInstant().atZone(ZoneId.systemDefault()).toLocalDate();
            String dateString = localDate.format(DATE_FORMATTER);
            LocalDate.parse(dateString, DATE_FORMATTER);
            return true;
        } catch (DateTimeParseException e) {
            LoggerManager.SECURITY_LOGGER.warning("Date must be in the yyyy-MM-dd format");
            return false;
        }
    }

    /**
     * checks if the email typed in by the user is in the right format
     * 
     * @param email user's email
     * @return true if it is, otherwise false
     */
    private static boolean isValidEmailFormat(String email) {

        return EMAIL_PATTERN.matcher(email).matches();
    }
    // OBJECTS
    // VALIDITY-------------------------------------------------------------------------------------------------------

    // PARENT
    // VALIDATION-------------------------------------------------------------------------------------------------------------
    /**
     * checks if the Guardian object sent by the front-end in a PUT request,
     * contains proper input
     * 
     * @param guardian the Guardian object received
     * @return true if it has proper input, otherwise false
     */
    public static boolean isValidParent(Guardian guardian) {
        return isValidParent(guardian.getSurname(), guardian.getOccupation(),
                guardian.getNationality(), guardian.getPhone_number(), guardian.getCompany_name(),
                guardian.getGiven_names(), guardian.getDate_of_birth());
    }

    /**
     * checks if the ParentCreationRequest object sent by the front-end in a POST
     * request, contains proper input
     * 
     * @param guardian the ParentCreationRequest object received
     * @return true if it has proper input, otherwise false
     */
    public static boolean isValidParentWithoutAccount(ParentCreationRequest guardian) {
        if (guardian == null) {
            return false;
        }

        return isValidParent(guardian.getSurname(), guardian.getOccupation(),
                guardian.getNationality(), guardian.getPhone_number(), guardian.getCompany_name(),
                guardian.getGiven_names(), guardian.getBirth_date());
    }

    /**
     * this method performs specific checks on different fields to ensure that they
     * meet the required format or criteria
     * 
     * @param surname     the surname that the user typed in
     * @param occupation  the occupation that the user typed in
     * @param nationality the nationality that the user typed in
     * @param phoneNumber the phoneNumber that the user typed in
     * @param companyName the companyName that the user typed in
     * @param givenNames  the givenNames that the user typed in
     * @param dateOfBirth the dateOfBirth that the user typed in
     * @return true if the parameters are fitting the criteria, otherwise false
     */
    private static boolean isValidParent(String surname, String occupation,
            String nationality, String phoneNumber, String companyName,
            List<String> givenNames, Date dateOfBirth) {
        boolean valid = true;

        if (surname != null && !TEXT_PATTERN.matcher(surname).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("surname not valid");
            valid = false;
        }

        if (occupation != null && !TEXT_PATTERN.matcher(occupation).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("occupation not valid");
            valid = false;
        }

        if (nationality != null && !NATIONALITIES.contains(nationality)) {
            LoggerManager.SECURITY_LOGGER.warning("nationality not valid");
            valid = false;
        }

        if (phoneNumber != null && !PHONE_NUMBER_PATTERN.matcher(phoneNumber).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("phone number not valid");
            valid = false;
        }

        if (companyName != null && !COMPANY_NAME_PATTERN.matcher(companyName).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("company name not valid");
            valid = false;
        }

        if (givenNames != null) {
            for (String givenName : givenNames) {
                if (!GIVEN_NAMES_PATTERN.matcher(givenName).matches()) {
                    LoggerManager.SECURITY_LOGGER.warning("given name not valid");
                    valid = false;
                }
            }
        }

        if (dateOfBirth != null && !isDateInFormat(dateOfBirth)) {
            LoggerManager.SECURITY_LOGGER.warning("date of birth not valid");
            valid = false;
        }

        return valid;
    }

    // ADDRESS
    // VALIDATION----------------------------------------------------------------------------------------------------------
    /**
     * checks if the AddressCreationRequest object sent by the front-end in a POST
     * request, contains proper input
     * 
     * @param address the AddressCreationRequest object received
     * @return true if it has proper input, otherwise false
     */
    public static boolean isValidAddress(AddressCreationRequest address) {
        return isValidAddress(address.getPhoneNumber(), address.getCountry(),
                address.getStreetNumber(), address.getCity(), address.getStreetName());
    }

    /**
     * checks if the Address object sent by the front-end in a PUT request, contains
     * proper input
     * 
     * @param address the Address object received
     * @return true if it has proper input, otherwise false
     */
    public static boolean isValidAddress(Address address) {
        return isValidAddress(address.getPhoneNumber(), address.getCountry(),
                address.getStreetNumber(), address.getCity(), address.getStreetName());
    }

    /**
     * this method performs specific checks on different fields to ensure that they
     * meet the required format or criteria
     * 
     * @param phoneNumber  the phoneNumber that the user typed in
     * @param country      the country that the user typed in
     * @param streetNumber the streetNumber that the user typed in
     * @param city         the city that the user typed in
     * @return true if the parameters are fitting the criteria, otherwise false
     */
    private static boolean isValidAddress(String phoneNumber, String country, int streetNumber, String city,
            String streetName) {
        boolean valid = true;

        if (phoneNumber != null && !PHONE_NUMBER_PATTERN.matcher(phoneNumber).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("phone number not valid");
            valid = false;
        }

        if (!isValidCountry(country)) {
            LoggerManager.SECURITY_LOGGER.warning("country not valid");
            valid = false;
        }

        if (Integer.toString(streetNumber) != null
                && !STREET_NUMBER_PATTERN.matcher(Integer.toString(streetNumber)).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("street number not valid");
            valid = false;
        }

        if (city != null && !isValidCity(city)) {
            LoggerManager.SECURITY_LOGGER.warning("city not valid");
            valid = false;
        }

        if (streetName != null && !STREET_PATTERN.matcher(streetName).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("street name not valid");
            valid = false;
        }

        return valid;
    }

    // CHILD
    // VALIDATION---------------------------------------------------------------------------------------------------------------
    /**
     * checks if the Child object sent by the front-end in a POST request, contains
     * proper input
     * 
     * @param child the Child object received
     * @return true if it has proper input, otherwise false
     */
    public static boolean isValidChild(Child child) {
        return isValidChild(child.getSurname(), child.getGivenNames(), child.getPreferredName(),
                child.getBirthDate(), child.getBsn(), child.getNationality(), child.getLanguages());
    }

    /**
     * checks if the ChildCreationRequest object sent by the front-end in a PUT
     * request, contains proper input
     * 
     * @param child the ChildCreationRequest object received
     * @return true if it has proper input, otherwise false
     */
    public static boolean isValidChild(ChildCreationRequest child) {
        return isValidChild(child.getSurname(), child.getGivenNames(), child.getPreferredName(),
                child.getBirthDate(), child.getBsn(), child.getNationality(), child.getLanguages());
    }

    /**
     * method used to check each individual field if it is formatted according to
     * the application's expectation.
     * 
     * @param surname       the surname that the user typed in
     * @param givenNames    the givenNames that the user typed in
     * @param preferredName the preferredName that the user typed in
     * @param birthDate     the birthDate that the user typed in
     * @param bsn           the bsn that the user typed in
     * @param nationality   the nationality that the user typed in
     * @param languages     the languages that the user typed in
     * @return true if the parameters are fitting the criteria, otherwise false
     */
    private static boolean isValidChild(String surname, List<String> givenNames, String preferredName,
            Date birthDate, String bsn, String nationality, List<String> languages) {
        boolean valid = true;

        if (surname != null && !TEXT_PATTERN.matcher(surname).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("surname not valid");
            valid = false;
        }

        if (givenNames != null) {
            for (String givenName : givenNames) {
                if (!GIVEN_NAMES_PATTERN.matcher(givenName).matches() && !ROMAN_LETTERS.matcher(givenName).matches()) {
                    System.out.println(givenName);
                    LoggerManager.SECURITY_LOGGER.warning("given name not valid");
                    valid = false;
                }
            }
        }

        if (preferredName != null && !GIVEN_NAMES_PATTERN.matcher(preferredName).matches()
                && !ROMAN_LETTERS.matcher(preferredName).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("preferred name not valid");
            valid = false;
        }

        if (birthDate != null && !isDateInFormat(birthDate)) {
            LoggerManager.SECURITY_LOGGER.warning("birth date not valid");
            valid = false;
        }

        if (bsn != null && !BSN_PATTERN.matcher(bsn).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("bsn not valid");
            valid = false;
        }

        if (nationality != null && !NATIONALITIES.contains(nationality)) {
            LoggerManager.SECURITY_LOGGER.warning("nationality not valid");
            valid = false;
        }

        if (languages != null) {
            for (String language : languages) {
                if (!isValidLanguage(language)) {
                    LoggerManager.SECURITY_LOGGER.warning("language not valid: " + language);
                    valid = false;
                }
            }
        }

        return valid;
    }

    // USER
    // VALIDATION--------------------------------------------------------------------------------------------------------------
    /**
     * checks if the SystemUserCreationRequest object sent by the front-end in a
     * POST request, contains proper input
     * 
     * @param su the SystemUserCreationRequest object received
     * @return true if it has proper input, otherwise false
     */
    public static boolean isValidUser(SystemUserCreationRequest su) {
        return isValidUser(su.getEmail(), su.getUsername());
    }

    /**
     * checks if the SystemUser object sent by the front-end in a PUT request,
     * contains proper input
     * 
     * @param su the SystemUser object received
     * @return true if it has proper input, otherwise false
     */
    public static boolean isValidUser(SystemUser su) {
        return isValidUser(su.getEmail(), su.getUsername());
    }

    /**
     * method used to check each individual field if it is formatted according to
     * the application's expectation.
     * 
     * @param email    the email that the user typed in
     * @param username the username that the user typed in
     * @return true if the parameters are fitting the criteria, otherwise false
     */
    private static boolean isValidUser(String email, String username) {
        boolean valid = true;

        if (email != null && !isValidEmailFormat(email)) {
            LoggerManager.SECURITY_LOGGER.warning("email not valid");
            valid = false;
        }

        if (username != null && !USERNAME_PATTERN.matcher(username).matches()) {
            LoggerManager.SECURITY_LOGGER.warning("username not valid");
            valid = false;
        }

        return valid;
    }

}
