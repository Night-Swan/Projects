import { getUserDetails } from "./cookieDecoder.js";

export function getSessionUserID() {
    return sessionStorage.getItem('user_id');
}

export function getSessionUserType() {
    return sessionStorage.getItem('user_type');
}

export function setSession() {
    sessionStorage.setItem('user_id', getUserDetails()["user_id"]);
    sessionStorage.setItem('user_type', getUserDetails()["user_type"]);
}

export function clearSession() {
    sessionStorage.removeItem('user_id');
    sessionStorage.removeItem('user_type');
    sessionStorage.removeItem('guardian_id');
    sessionStorage.removeItem('schoolID');
}

export function getSessionGuardianID() {
    return sessionStorage.getItem('guardian_id');
}

export function setSessionGuardianID(guardian_id) {
    sessionStorage.setItem('guardian_id', guardian_id);
}

export function getSessionSchoolID() {
    return sessionStorage.getItem("schoolID");
}

export function setSessionSchoolID(schoolID) {
    sessionStorage.setItem("schoolID", schoolID);
}

export function clearSessionGuardianID() {
    sessionStorage.removeItem('guardian_id');
}

/**
 * Checks if the user is logged in with account and has set their Guardian Code.
 * @returns true if the user is logged in with account and has set their Guardian Code
 */
export function isLoggedInWithAccount() {
    return getSessionUserID() !== null && getSessionUserID() !== undefined && getSessionUserType() !== null && getSessionUserType() !== undefined;
}

/**
 * Checks if there is a GID set in sessionStorage.
 * @returns true if the user has a GID set in sessionStorage
 */
export function sessionWithGID() {
    return !isLoggedInWithAccount() && (getSessionGuardianID() !== undefined && getSessionGuardianID() !== null);
}

/**
 * Checks if a user is logged in and if their GID is set.
 * @returns true if a user is logged in and if their GID is set.
 */
export function isLoggedInWithAccountAndData() {
    return isLoggedInWithAccount() && (getSessionGuardianID() !== undefined && getSessionGuardianID() !== null);
}

/**
 * Checks if the user is logged in with account or has session with just a Guardian Code.
 * @returns true if the guardian is logged in with account or the session includes just their Guardian Code
 */
export function hasSession() {
    return isLoggedInWithAccount() || sessionWithGID();
}