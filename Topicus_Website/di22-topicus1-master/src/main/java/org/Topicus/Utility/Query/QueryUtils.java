package org.Topicus.Utility.Query;

import java.util.List;

import org.Topicus.Utility.Logs.LoggerManager;

public class QueryUtils {

    public static String generateInsertPlaceholders(int placeholder_count, int row_count) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < row_count; i++) {
            sb.append("(");
            for (int j = 0; j < placeholder_count; j++) {
                sb.append("?");
                if (j < placeholder_count - 1) {
                    sb.append(", ");
                }
            }
            sb.append(")");
            if (i < row_count - 1) {
                sb.append(", ");
            }
        }

        return sb.toString();
    }

    public static String generateUpdatePlaceholders(String matchingColumn, String filterColumn, List<String> columns,
            int row_count) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < columns.size(); i++) {
            sb.append(columns.get(i));
            sb.append(" = CASE ");
            for (int j = 0; j < row_count; j++) {
                sb.append("WHEN ");
                sb.append(matchingColumn);
                sb.append(" = ? ");
                sb.append("THEN ? ");
            }

            sb.append("ELSE ");
            sb.append(columns.get(i));
            sb.append(" END");

            if (i < columns.size() - 1) {
                sb.append(", ");
            }
        }

        sb.append(" WHERE ");
        sb.append(filterColumn);
        sb.append(" = ? ");

        return sb.toString();
    }

    public static String generateDeletePlaceholders(int delete_count) {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        for (int i = 0; i < delete_count; i++) {
            sb.append("?");
            if (i < delete_count - 1) {
                sb.append(", ");
            }
        }

        sb.append(")");
        return sb.toString();
    }

    public static void main(String[] args) {
        LoggerManager.UTILITY_LOGGER.info(generateInsertPlaceholders(3, 2));
    }
}
