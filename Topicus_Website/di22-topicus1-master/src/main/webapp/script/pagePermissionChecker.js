import { getSessionUserType } from "./storageManagement.js";

/**
 * This method is used to validate the permissions per page of user type.
 * @param expectedType
 * @returns {boolean}
 */
export function checkPermissions(expectedType) {
    if (expectedType === null || expectedType === undefined || expectedType === "" || expectedType === "PUBLIC") {
        return true;
    }

    let userType = getSessionUserType();

    if (userType === "TOPICUS_ADMIN") {
        return true;
    }

    return userType === expectedType;
}