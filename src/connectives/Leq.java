package connectives;

import concepts.ConceptExpression;
import formula.Formula;

public class Leq extends ConceptExpression{
	
	private Integer number;
	
	public Leq() {
		super();
	}
	
	public Leq(Integer num, Formula role, Formula filler) {
		super(role,filler);
		this.number=num;
		
	}
	
	public Integer get_num() {
		return this.number;
	}
	
	@Override
	public String toString() {
		Formula role = this.getSubFormulas().get(0);
		Formula filler = this.getSubFormulas().get(1);
		Integer int1=this.number;
		if (filler instanceof And || filler instanceof Or) {
			return "\u2264"+int1 + role + ".(" + filler + ")";
		} else {
			return "\u2264"+int1 + role + "." + filler;
		}
	}

}
