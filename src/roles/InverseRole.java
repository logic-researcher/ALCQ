package roles;

import formula.Formula;

public class InverseRole extends RoleExpression {

    public InverseRole() {
        super();
    }

    public InverseRole(String str) {
        super(str);
    }

    public InverseRole(Formula role) {
        super(role);
        this.setText(role.getText());
    }

    @Override
    public String toString() {
        return this.getText() + "\u207B";
    }

    public String getRoleStr() {
        return this.getText();
    }
}
