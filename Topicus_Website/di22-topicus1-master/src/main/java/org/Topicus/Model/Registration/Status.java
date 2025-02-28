package org.Topicus.Model.Registration;
/*
An enum to manage the status of the Registration.
 */
public enum Status {
    ACCEPTED, REJECTED, SUBMITTED, AWAITING_SUBMISSION, UNDER_REVIEW, MODIFICATIONS_ALLOWED, MISSING_INFORMATION, UNAVAILABLE_ERROR
}
// ACCEPTED, REJECTED, SUBMITTED, UNDER_REVIEW - no parent can change
// AWAITING_SUBMISSION - only for logged in parents - add Save [changes] button
// , ,, , , , MISSING_INFORMATION, UNAVAILABLE_ERROR