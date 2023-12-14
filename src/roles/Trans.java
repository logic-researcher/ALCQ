package roles;

import java.util.Objects;

public class Trans extends RoleExpression{
    public Trans(){
        super();
    }

    public Trans(String role){
        super(role);
    }

    public Trans(RoleExpression role){
        super(role);
    }


    public String toString(){
        return "Trans("+ this.getSubFormulas().get(0).getText() +")";
    }


}
