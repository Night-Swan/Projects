package org.Topicus.Security.ThreatPrevention;

import org.apache.commons.text.StringEscapeUtils;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Pattern;

public class InputSanitizer {
    /**
     * Sanitizes the input string by escaping HTML special characters.
     *
     * @param input The input string to sanitize.
     * @return The sanitized string with escaped HTML special characters.
     */
    public String sanitizeHTML(String input) {
        return StringEscapeUtils.escapeHtml4(input);
    }

    /**
     * Sanitizes the input string for SQL usage (currently not implemented).
     *
     * @param input The input string to sanitize.
     * @return Always returns null as the method is not implemented.
     */
    public String sanitizeSQL(String input) {
        return null;//StringEscapeUtils.escapeSql(input);
    }

    /**
     * Sanitizes the input string by performing various operations, such as trimming, lowercasing,
     * removing extra spaces, and handling email-specific rules.
     *
     * @param input The input string to sanitize.
     * @return The sanitized string after applying the specified operations.
     */
    public String sanitizeInput(String input) {
        // Remove leading and trailing whitespace
        String sanitizedInput = input.trim();

        // Convert input to lowercase
        sanitizedInput = sanitizedInput.toLowerCase();

        // Remove any extra spaces within the email
        sanitizedInput = sanitizedInput.replaceAll("\\s+", "");

        // Remove any leading or trailing dots in the local part of the email
        sanitizedInput = sanitizedInput.replaceAll("^\\.|\\.$", "");

        return sanitizedInput;
    }


    private static final List<String> sqlRejectWords = Arrays.asList(
            "SELECT", "FROM", "ALTER", "TABLE", "DROP", "TRUNCATE", "UNION", "INSERT",
            "UPDATE", "DELETE", "JOIN", "WHERE", "EXEC", "CREATE", "GRANT", "REVOKE",
            "COMMIT", "ROLLBACK", "--", "'"
    );

    private static final List<String> xssRejectWords = Arrays.asList(
            "script", "<", ">", "javascript", "img", "src"
    );

    /**
     * Checks if the input string contains any potentially malicious content by comparing it with
     * the list of rejected SQL words and XSS words.
     *
     * @param input The input string to check for potential malicious content.
     * @return {@code true} if the input string contains potentially malicious content, {@code false} otherwise.
     */
    public static boolean inputSanitizer(String input) {
        //String lower = input.toLowerCase();
        if (containsPrintableCharacters(input)) {
            for (String word : sqlRejectWords) {
                if (input.contains(word.toLowerCase())) {
                    return true;
                }
            }

            for (String word : xssRejectWords) {
                if (input.contains(word.toLowerCase())) {
                    return true;
                }
            }

            return false;
        }

        return false;
    }

    /**
     * Checks if the input string is empty.
     *
     * @param input The input string to check.
     * @return {@code true} if the input string is empty, {@code false} otherwise.
     */
    public static boolean isEmpty(String input) {
        return input.isEmpty();
    }

    /**
     * Validates if the provided string is a valid email address.
     *
     * @param email The email address to validate.
     * @return {@code true} if the email address is valid, {@code false} otherwise.
     */
    public static boolean validEmail(String email) {
        Pattern emailRegex = Pattern.compile("(\\w+\\.?)+@(\\w{2,}\\.?)+");
        return emailRegex.matcher(email).matches();
    }

    /**
     * Sanitizes the input URI by encoding it using UTF-8.
     *
     * @param URI The URI to sanitize.
     * @return The sanitized URI with UTF-8 encoding.
     */
    public static String URISanitizer(String URI) {
        return java.net.URLEncoder.encode(URI, StandardCharsets.UTF_8);
    }

    /**
     * Manages the display of text by replacing certain characters with their corresponding HTML entities.
     *
     * @param text The text to manage the display for.
     * @return The text with replaced characters using HTML entities.
     */
    public static String manageDisplay(String text) {
        return text.replace("<", "&lt;")
                .replace(">", "&gt;")
                .replace("'", "&#x27;")
                .replace("`", "&#x60;")
                .replace("\"", "&quot;")
                .replace("&", "&amp;");
    }

    /**
     * Checks if the input string contains only alphanumeric characters.
     *
     * @param input The input string to check.
     * @return {@code true} if the input string contains only alphanumeric characters, {@code false} otherwise.
     */
    public static boolean containsPrintableCharacters(String input) {
        Pattern alNum = Pattern.compile("^[a-zA-Z0-9.,]+$");
        return alNum.matcher(input).matches();
    }

    /**
     * Encodes the input string using UTF-8 encoding.
     *
     * @param input The input string to encode.
     * @return The encoded string using UTF-8 encoding.
     */
    public static String encodeUTF8(String input) {
        byte[] bytes = input.getBytes(StandardCharsets.UTF_8);
        return new String(bytes, StandardCharsets.UTF_8);
    }


}
