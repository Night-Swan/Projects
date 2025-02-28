package org.Topicus.DAO.RegistrationFormDAO;

import java.sql.Connection;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

import org.Topicus.DAO.Contract.DAO;
import org.Topicus.Model.RegistrationForm.FormComponent;
import org.Topicus.Model.RegistrationForm.RegistrationFormMetadata;
import org.Topicus.Model.RegistrationForm.Section;
import org.Topicus.Model.RegistrationForm.Style.Style;
import org.Topicus.Payload.Response.RegistrationForm.RegistrationFormContainer;
import org.Topicus.Payload.Response.RegistrationForm.SectionContainer;
import org.Topicus.Utility.Logs.LoggerManager;

public enum RegistrationFormDAO implements DAO<RegistrationFormContainer> {
    instance;

    /**
     * Method to return singleton instance of DAO class.
     * 
     * @return of type RegistrationFormDAO.
     */
    public static RegistrationFormDAO getInstance() {
        return instance;
    }

    /**
     * This method is used to return a RegistrationFormContainer, which is a body
     * to be sent to the front-end to format and manage
     * 
     * @param registrationFormID of type UUID.
     * @return of type RegistrationFormContainer
     */
    @Override
    public RegistrationFormContainer get(UUID registrationFormID) {
        RegistrationFormMetadata registrationForm = RegistrationFormMetadataDAO.getInstance().get(registrationFormID);
        List<Section> sectionList = SectionDAO.getInstance().getAllSectionsForForm(registrationFormID);
        List<FormComponent> formComponentList = FormComponentDAO.getInstance()
                .getAllComponentsForForm(registrationFormID);

        List<SectionContainer> sectionContainerList = new ArrayList<>();

        for (Section section : sectionList) {
            List<FormComponent> formComponentsForSection = formComponentList.stream()
                    .filter(formComponent -> formComponent.getSection_id().equals(section.getSection_id())).toList();
            sectionContainerList.add(new SectionContainer(section, formComponentsForSection));
        }

        Style formStyle = StyleDAO.getInstance().get(registrationFormID);

        return new RegistrationFormContainer(registrationForm, sectionContainerList, formStyle);
    }

    @Override
    public List<RegistrationFormContainer> getAll() {
        LoggerManager.DAO_LOGGER.warning("getAll() method is not supposed to be used for RegistrationFormDAO");
        return null;
    }

    /**
     * Get all registration form containers for a school.
     * 
     * @param schoolID of type UUID.
     * @return of type List<RegistrationFormContainer>.
     */
    public List<RegistrationFormContainer> getFormContainersForSchool(UUID schoolID) {
        List<RegistrationFormMetadata> registrationFormMetadataList = RegistrationFormMetadataDAO.getInstance()
                .getRegistrationFormMetadataForSchool(schoolID);
        List<RegistrationFormContainer> registrationFormContainerList = new ArrayList<>();

        for (RegistrationFormMetadata registrationFormMetadata : registrationFormMetadataList) {
            registrationFormContainerList.add(get(registrationFormMetadata.getRegistration_form_id()));
        }

        return registrationFormContainerList;
    }

    public static Double millisToSeconds(long millis) {
        return Math.round(millis / 1000.0 * 100.0) / 100.0;
    }

    /**
     * Method for either updating or creating a new registration form(INSERT or
     * UPDATE).
     * 
     * @param registrationFormContainer of type RegistrationFormContainer.
     * @return of type RegistrationFormContainer.
     */
    public RegistrationFormContainer updateRecord(RegistrationFormContainer registrationFormContainer) {

        long startTime = System.currentTimeMillis();
        long currentTimeCheckpoint = startTime;

        // initialize DAOs
        RegistrationFormMetadataDAO registrationFormMetadataDAO = RegistrationFormMetadataDAO.getInstance();
        SectionDAO sectionDAO = SectionDAO.getInstance();
        FormComponentDAO formComponentDAO = FormComponentDAO.getInstance();

        LoggerManager.DAO_LOGGER.info("DAOs initialized in "
                + millisToSeconds(System.currentTimeMillis() - currentTimeCheckpoint) + " seconds");
        currentTimeCheckpoint = System.currentTimeMillis();

        // initialize lists for all section and form component ids
        List<UUID> sectionIds = new ArrayList<>();
        List<UUID> formComponentIds = new ArrayList<>();

        // initialize list for sections to be created and updated
        List<Section> sectionsToCreate = new ArrayList<>();
        List<Section> sectionsToUpdate = new ArrayList<>();

        // initialize list for form components to be created and updated
        List<FormComponent> formComponentsToCreate = new ArrayList<>();
        List<FormComponent> formComponentsToUpdate = new ArrayList<>();

        // get metadata from container
        RegistrationFormMetadata registrationFormMetadata = registrationFormContainer.getFormMetadata();

        LoggerManager.DAO_LOGGER.info("Metadata retrieved from container in "
                + millisToSeconds(System.currentTimeMillis() - currentTimeCheckpoint) + " seconds");
        currentTimeCheckpoint = System.currentTimeMillis();

        // check if metadata is new or existing
        boolean update_metadata = registrationFormMetadata.getRegistration_form_id() != null;

        // if metadata is new, generate new id
        if (!update_metadata) {
            registrationFormMetadata.setRegistration_form_id(UUID.randomUUID());
        }

        RegistrationFormMetadata registrationFormMetadataFromDB = update_metadata
                ? registrationFormMetadataDAO.update(registrationFormMetadata)
                : registrationFormMetadataDAO.save(registrationFormMetadata);

        LoggerManager.DAO_LOGGER.info("Metadata record updated in "
                + millisToSeconds(System.currentTimeMillis() - currentTimeCheckpoint) + " seconds");
        currentTimeCheckpoint = System.currentTimeMillis();

        // get style from container
        Style style = registrationFormContainer.getFormStyle();

        if (style != null) {
            boolean update_style = style.getRegistration_form_id() != null;
            
            if (!update_style) {
                style.setRegistration_form_id(registrationFormMetadataFromDB.getRegistration_form_id());
            }

            // update style
            if (update_style) {
                StyleDAO.getInstance().update(style);
            } else {
                StyleDAO.getInstance().save(style);
            }
        }

        LoggerManager.DAO_LOGGER.info("Style record updated in "
                + millisToSeconds(System.currentTimeMillis() - currentTimeCheckpoint) + " seconds");
        currentTimeCheckpoint = System.currentTimeMillis();

        // get section containers from container
        List<SectionContainer> sectionContainerList = registrationFormContainer.getSectionContainerList();

        // iterate over section containers
        for (SectionContainer sectionContainer : sectionContainerList) {

            // get section from container
            Section section = sectionContainer.getSection();

            // check if section is new or existing
            boolean update_section = section.getSection_id() != null;

            // if section is new, generate new id
            if (!update_section) {
                section.setSection_id(UUID.randomUUID());
            }

            // update registration form id for the section accordingly
            section.setRegistration_form_id(update_section
                    ? section.getRegistration_form_id()
                    : registrationFormMetadataFromDB.getRegistration_form_id());

            // add section id to list
            sectionIds.add(section.getSection_id());

            // add section to list of sections to be created or updated
            if (update_section) {
                sectionsToUpdate.add(section);
            } else {
                sectionsToCreate.add(section);
            }

            // get form components from container
            List<FormComponent> formComponentList = sectionContainer.getFormComponentList();

            // iterate over form components
            for (FormComponent formComponent : formComponentList) {

                // check if form component is new or existing
                boolean update_form_component = formComponent.getComponent_id() != null;

                // if form component is new, generate new id
                if (!update_form_component) {
                    formComponent.setComponent_id(UUID.randomUUID());
                }

                // update the registration form id for the form component accordingly
                formComponent.setRegistration_form_id(update_form_component
                        ? formComponent.getRegistration_form_id()
                        : registrationFormMetadata.getRegistration_form_id());

                // update the section id for the form component accordingly
                formComponent.setSection_id(update_form_component
                        ? formComponent.getSection_id()
                        : section.getSection_id());

                // add form component id to list
                formComponentIds.add(formComponent.getComponent_id());

                // add form component to list of form components to be created or updated
                if (update_form_component) {
                    formComponentsToUpdate.add(formComponent);
                } else {
                    formComponentsToCreate.add(formComponent);
                }
            }
        }

        // create new sections
        long sectionCreationStartTime = System.currentTimeMillis();

        if (!sectionsToCreate.isEmpty()) {
            sectionDAO.bulkCreateSections(sectionsToCreate);
        } else {
            LoggerManager.DAO_LOGGER.info("No new sections to create");
        }

        LoggerManager.DAO_LOGGER.info("New sections created in "
                + millisToSeconds(System.currentTimeMillis() - sectionCreationStartTime) + " seconds");

        // update existing sections
        long sectionUpdateStartTime = System.currentTimeMillis();

        if (!sectionsToUpdate.isEmpty()) {
            sectionDAO.bulkUpdateSectionsForForm(registrationFormMetadata.getRegistration_form_id(), sectionsToUpdate);
        } else {
            LoggerManager.DAO_LOGGER.info("No existing sections to update");
        }

        LoggerManager.DAO_LOGGER.info("Existing sections updated in "
                + millisToSeconds(System.currentTimeMillis() - sectionUpdateStartTime) + " seconds");

        // delete old sections
        long sectionDeleteStartTime = System.currentTimeMillis();

        sectionDAO.deleteOldSections(registrationFormMetadata.getRegistration_form_id(), sectionIds);

        LoggerManager.DAO_LOGGER.info("Old sections deleted in "
                + millisToSeconds(System.currentTimeMillis() - sectionDeleteStartTime) + " seconds");

        // create new form components
        long formComponentCreationStartTime = System.currentTimeMillis();

        if (!formComponentsToCreate.isEmpty()) {
            formComponentDAO.bulkCreateFormComponents(formComponentsToCreate);
        } else {
            LoggerManager.DAO_LOGGER.info("No new form components to create");
        }

        LoggerManager.DAO_LOGGER.info("New form components created in "
                + millisToSeconds(System.currentTimeMillis() - formComponentCreationStartTime) + " seconds");

        // update existing form components
        long formComponentUpdateStartTime = System.currentTimeMillis();

        if (!formComponentsToUpdate.isEmpty()) {
            formComponentDAO.bulkUpdateFormComponentsForForm(registrationFormMetadata.getRegistration_form_id(),
                    formComponentsToUpdate);
        } else {
            LoggerManager.DAO_LOGGER.info("No existing form components to update");
        }

        LoggerManager.DAO_LOGGER.info("Existing form components updated in "
                + millisToSeconds(System.currentTimeMillis() - formComponentUpdateStartTime) + " seconds");

        // delete old form components
        long formComponentDeleteStartTime = System.currentTimeMillis();

        formComponentDAO.deleteOldFormComponents(registrationFormMetadata.getRegistration_form_id(), formComponentIds);

        LoggerManager.DAO_LOGGER.info("Old form components deleted in "
                + millisToSeconds(System.currentTimeMillis() - formComponentDeleteStartTime) + " seconds");

        LoggerManager.DAO_LOGGER.info("Registration form updated in " + millisToSeconds(
                System.currentTimeMillis() - currentTimeCheckpoint) + " seconds");

        return registrationFormContainer;
    }

    /**
     * Method for deleting a registration form(DELETE).
     * 
     * @param id of type UUID.
     */
    @Override
    public void delete(UUID id) {
        RegistrationFormMetadataDAO registrationFormMetadataDAO = RegistrationFormMetadataDAO.getInstance();
        SectionDAO sectionDAO = SectionDAO.getInstance();
        FormComponentDAO formComponentDAO = FormComponentDAO.getInstance();

        formComponentDAO.deleteComponentsForForm(id);
        sectionDAO.deleteSectionsForForm(id);
        registrationFormMetadataDAO.delete(id);
    }

    @Override
    public Connection requestConnection() {
        LoggerManager.DAO_LOGGER.warning("requestConnection() is not supposed to be called on RegistrationFormDAO");
        return null;
    }

    @Override
    public RegistrationFormContainer save(RegistrationFormContainer t) {
        LoggerManager.DAO_LOGGER.warning("save() is not supposed to be called on RegistrationFormDAO");
        return null;
    }

    @Override
    public RegistrationFormContainer update(RegistrationFormContainer t) {
        LoggerManager.DAO_LOGGER.warning("update() is not supposed to be called on RegistrationFormDAO");
        return null;
    }
}
