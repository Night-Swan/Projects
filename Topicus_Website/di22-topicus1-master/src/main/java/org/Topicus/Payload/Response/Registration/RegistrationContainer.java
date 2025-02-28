package org.Topicus.Payload.Response.Registration;

import org.Topicus.Model.Registration.FEDataField;
import org.Topicus.Model.Registration.Registration;
import org.Topicus.Model.RegistrationForm.Section;

import jakarta.xml.bind.annotation.XmlRootElement;

import java.util.List;

/**
 * Used for sending the data corresponding to a Registration to the front-end.
 */
@XmlRootElement
public class RegistrationContainer {
    // FIELD VARIABLE(S) ---------------------------------------------------------
    private Registration reg;
    private List<FEDataField> df_pos;
    private List<Section> sections;

    // CONSTRUCTOR(S) -------------------------------------------------------------
    /**
     * Constructor for instantiating a RegistrationContainer.
     * @param reg of type Registration.
     * @param df_pos of type Map<DataField, Integer> representing the data field and its position.
     */
    public RegistrationContainer(Registration reg, List<FEDataField> df_pos, List<Section> sections) {
        this.reg = reg;
        this.df_pos = df_pos;
        this.sections = sections;
    }

    // METHOD(S) --------------------------------------------------------------------
    public Registration getReg() {
        return reg;
    }

    public List<FEDataField> getDf_pos() {
        return df_pos;
    }

    public List<Section> getSections() {
        return sections;
    }
}
