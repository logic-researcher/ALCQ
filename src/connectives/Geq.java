package connectives;
import concepts.ConceptExpression;
import formula.Formula;

public class Geq extends ConceptExpression{

	private Integer number;
	
	public Geq() {
		super();
	}
	
	public Geq(Integer num, Formula role, Formula filler) {
		super(role,filler);
		this.number=num;
	}
	
	public Integer get_num() {
		return this.number;
	}
	
	public String toString() {
		Formula role = this.getSubFormulas().get(0);
		Formula filler = this.getSubFormulas().get(1);
		Integer int1=this.number;
		if (filler instanceof And || filler instanceof Or) {
			return "\u2265"+int1 + role + ".(" + filler + ")";
		} else {
			return "\u2265"+int1 + role + "." + filler;
		}
	}
	
	public void setnum(Integer num) {
		this.number = num;
	}
}
