package org.Topicus.Utility.Files;

import java.util.UUID;

public enum FileHandler {
    getInstance();

    /**
     * This method will take the bytes sent from the front-end to produce the file, and it will then attach it to the
     * appropriate user folder on the server so that the record can be maintained in addition to the file path.
     * The file will be stored as is.
     * @param fileBytes represents the bytes for the file that is returned.
     * @return of type String, representing the file path.
     */
    public synchronized String saveFile(byte[] fileBytes) {
        return "";
    }

    /**
     * This method will be used to return the bytes for a particular file for a user, when the filePath is provided.
     * @param userID of type UUID, representing the identification of the user.
     * @param filePath of type String, representing the location of the file on the server.
     * @return of type byte[] representing the bytes for the file to be returned.
     */
    public synchronized byte[] retrieveFile(UUID userID, String filePath) {
        return null;
    }

    /**
     * This method is used to replace an existing file (for the same data field of a form) so that additional storage
     * is not wasted, and file history records are not maintained.
     * @param newFileBytes of type byte[].
     * @param oldFilePath of type String, representing where the previous file is located.
     * @return of type String, representing the file path.
     */
    public synchronized String replaceFile(byte[] newFileBytes, String oldFilePath) {
        return "";
    }
}
