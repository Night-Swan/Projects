package org.Topicus.Model.SystemUser;

/**
 * This enum is used for the management of access across the application. It is used with the Jersey Annotation @RolesAllowed.
 */
public enum UserType {
    PUBLIC(4, "Public"),
    GUARDIAN(2, "Guardian"),
    SCHOOL_ADMIN(1, "School Admin"),
    TOPICUS_ADMIN(0, "Topicus Admin");

    private int access_level;
    private String pretty_name;

    UserType(int access_level, String pretty_name) {
        this.access_level = access_level;
        this.pretty_name = pretty_name;
    }

    public int getAccessLevel() {
        return access_level;
    }

    public String getPrettyName() {
        return pretty_name;
    }
}
