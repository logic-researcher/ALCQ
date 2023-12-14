package checkfrequency;

import java.util.List;

import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Geq;
import connectives.Inclusion;
import connectives.Leq;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import roles.AtomicRole;

public class FChecker {

	public FChecker() {

	}
	
	public int positive(AtomicConcept concept, List<Formula> formula_list) {

		int positive = 0;

		for (Formula formula : formula_list) {
			positive = positive + positive(concept, formula);
		}

		return positive;
	}

	/*public int positive(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? 1 : 0;
		} else if (formula instanceof Negation) {
			return negative(concept, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists || formula instanceof Forall) {
			return positive(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return negative(concept, formula.getSubFormulas().get(0))
					+ positive(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + positive(concept, operand);
			}
			return sum;
		}

		return 0;
	}*/
	
	public int positive(AtomicConcept concept, Formula formula) {  //For SHQ

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? 1 : 0;
			
		} else if (formula instanceof Negation) {
			return negative(concept, formula.getSubFormulas().get(0));
			
		} else if (formula instanceof Leq) {
			return negative(concept,formula.getSubFormulas().get(1));
		
		} else if (formula instanceof Geq) {
			return positive(concept, formula.getSubFormulas().get(1));
			
		} else if (formula instanceof Inclusion) {
			return negative(concept, formula.getSubFormulas().get(0))
					+ positive(concept, formula.getSubFormulas().get(1));
			
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + positive(concept, operand);
			}
			return sum;
		}

		return 0;
	}
	

	public int negative(AtomicConcept concept, List<Formula> formula_list) {

		int negative = 0;

		for (Formula formula : formula_list) {
			negative = negative + negative(concept, formula);
		}

		return negative;
	}

	/*public int negative(AtomicConcept concept, Formula formula) {

		if (formula instanceof Negation) {
			return positive(concept, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists || formula instanceof Forall) {
			return negative(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return positive(concept, formula.getSubFormulas().get(0))
					+ negative(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + negative(concept, operand);
			}
			return sum;
		}

		return 0;
	}*/
	
	public int negative(AtomicConcept concept, Formula formula) { //for SHQ

		if (formula instanceof Negation) {
			return positive(concept, formula.getSubFormulas().get(0));
		} else if (formula instanceof Leq) {
			return positive(concept,formula.getSubFormulas().get(1));
		} else if (formula instanceof Geq) {
			return negative(concept, formula.getSubFormulas().get(1));
			
		} else if (formula instanceof Inclusion) {
			return positive(concept, formula.getSubFormulas().get(0))
					+ negative(concept, formula.getSubFormulas().get(1));
			
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + negative(concept, operand);
			}
			return sum;
		}

		return 0;
	}
	
	public int positive(AtomicRole role, List<Formula> formula_list) {
		
		int positive = 0;
		
		for (Formula formula : formula_list) {
			positive = positive + positive(role, formula);
		}
		
		return positive;		
	}
		
	/*public int positive(AtomicRole role, Formula formula) {

		if (formula instanceof AtomicRole) {
			return formula.equals(role) ? 1 : 0;
		} else if (formula instanceof Negation) {
			return negative(role, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists) {
			return positive(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Forall) {
			return negative(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return negative(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + positive(role, operand);
			}
			return sum;
		}

		return 0;
	}*/
	
	public int positive(AtomicRole role, Formula formula) { //for SHQ

		if (formula instanceof AtomicRole) {
			return formula.equals(role) ? 1 : 0;
		} else if (formula instanceof Negation) {
			return negative(role, formula.getSubFormulas().get(0));
		} else if (formula instanceof Geq) {
			return positive(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Leq) {
			return negative(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return negative(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + positive(role, operand);
			}
			return sum;
		}

		return 0;
	}
	
	public int negative(AtomicRole role, List<Formula> formula_list) {

		int negative = 0;

		for (Formula formula : formula_list) {
			negative = negative + negative(role, formula);
		}

		return negative;
	}
	
	/*public int negative(AtomicRole role, Formula formula) {

		if (formula instanceof Negation) {
			return positive(role, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists) {
			return negative(role, formula.getSubFormulas().get(0)) + negative(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Forall) {
			return positive(role, formula.getSubFormulas().get(0)) + negative(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return positive(role, formula.getSubFormulas().get(0))
					+ negative(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas(); 
			for (Formula operand : operand_list) {
				sum = sum + negative(role, operand);
			}
			return sum;
		}

		return 0;
	}*/
	
	public int negative(AtomicRole role, Formula formula) { //for SHQ

		if (formula instanceof Negation) {
			return positive(role, formula.getSubFormulas().get(0));
			
		} else if (formula instanceof Geq) {
			return negative(role, formula.getSubFormulas().get(0)) + negative(role, formula.getSubFormulas().get(1));
			
		} else if (formula instanceof Leq) {
			return positive(role, formula.getSubFormulas().get(0)) + negative(role, formula.getSubFormulas().get(1));
			
		} else if (formula instanceof Inclusion) {
			return positive(role, formula.getSubFormulas().get(0))
					+ negative(role, formula.getSubFormulas().get(1));
			
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas(); 
			for (Formula operand : operand_list) {
				sum = sum + negative(role, operand);
			}
			return sum;
		}

		return 0;
	}

	public int getRestrictionNum(Formula formula){
		if (formula instanceof Negation){
			return getRestrictionNum(formula.getSubFormulas().get(0));

		} else if (formula instanceof Geq || formula instanceof Leq){
			return getRestrictionNum(formula.getSubFormulas().get(1))+1;

		} else if (formula instanceof AtomicConcept || formula instanceof AtomicRole){
			return 0;

		} else if (formula instanceof Or || formula instanceof And){
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list){
				sum += getRestrictionNum(operand);
			}
			return sum;
		} else if (formula instanceof Inclusion){
			return getRestrictionNum(formula.getSubFormulas().get(0))+getRestrictionNum(formula.getSubFormulas().get(1));
		}
		return 0;
	}


	public int getRestrictionNum(List<Formula> formula_list){
		int sum = 0;
		for (Formula formula : formula_list){
			sum += getRestrictionNum(formula);
		}
		return sum;
	}
}
