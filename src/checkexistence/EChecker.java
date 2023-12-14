/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package checkexistence;

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

/**
 *
 * @author Yizheng311
 */
public class EChecker {

	public EChecker() {

	}

	/*public boolean isPresent(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept);
		} else if (formula instanceof Negation) {
			return isPresent(concept, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists || formula instanceof Forall) {
			return isPresent(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return isPresent(concept, formula.getSubFormulas().get(0))
					|| isPresent(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				if (isPresent(concept, operand)) {
					return true;
				}
			}
		}

		return false;
	}*/
	public boolean isPresent(AtomicConcept concept, Formula formula) {   //for SHQ
		if (formula instanceof AtomicConcept) {
			return formula.equals(concept);
			
		} else if (formula instanceof Negation) {
			return isPresent(concept, formula.getSubFormulas().get(0));
			
		} else if (formula instanceof Geq || formula instanceof Leq) {
			return isPresent(concept,formula.getSubFormulas().get(1));
			
		} else if (formula instanceof Inclusion) {
			return isPresent(concept, formula.getSubFormulas().get(0))
					|| isPresent(concept, formula.getSubFormulas().get(1));
			
		} else if (formula instanceof Or || formula instanceof And) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				if(isPresent(concept, operand)) {
					return true;
				}
			}
		}
		return false;
	}

	/*public boolean isPresent(AtomicRole role, Formula formula) {

		if (formula instanceof AtomicRole) {
			return formula.equals(role);
		} else if (formula instanceof Negation) {
			return isPresent(role, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists || formula instanceof Forall
				|| formula instanceof Inclusion) {
			return isPresent(role, formula.getSubFormulas().get(0))
					|| isPresent(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				if (isPresent(role, operand)) {
					return true;
				}
			}
		}

		return false;
	}*/
	public boolean isPresent(AtomicRole role, Formula formula) {    //for SHQ 

		if (formula instanceof AtomicRole) {
			return formula.equals(role);
			
		} else if (formula instanceof Negation) {
			return isPresent(role, formula.getSubFormulas().get(0));
			
		} else if (formula instanceof Geq || formula instanceof Leq
				|| formula instanceof Inclusion) {
			return isPresent(role, formula.getSubFormulas().get(0))
					|| isPresent(role, formula.getSubFormulas().get(1));
			
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				if (isPresent(role, operand)) {
					return true;
				}
			}
		}

		return false;
	}
	

	/*public boolean hasRole(Formula formula) {

		if (formula instanceof AtomicRole) {
			return true;
		} else if (formula instanceof Negation) {
			return hasRole(formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists || formula instanceof Forall
				|| formula instanceof Inclusion) {
			return hasRole(formula.getSubFormulas().get(0)) || hasRole(formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				if (hasRole(operand)) {
					return true;
				}
			}
		}

		return false;
	}*/
	
	public boolean hasRole(Formula formula) {  //for SHQ

		if (formula instanceof AtomicRole) {
			return true;
			
		} else if (formula instanceof Negation) {
			return hasRole(formula.getSubFormulas().get(0));
			
		} else if (formula instanceof Geq || formula instanceof Leq
				|| formula instanceof Inclusion) {
			return hasRole(formula.getSubFormulas().get(0)) || hasRole(formula.getSubFormulas().get(1));
			
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				if (hasRole(operand)) {
					return true;
				}
			}
		}

		return false;
	}
	
	
	/*public boolean hasRoleRestriction(Formula formula) {

		if (formula instanceof Negation) {
			return hasRoleRestriction(formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists || formula instanceof Forall) {
			return true;
		} else if (formula instanceof Inclusion) {
			return hasRoleRestriction(formula.getSubFormulas().get(0))
					|| hasRoleRestriction(formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				if (hasRoleRestriction(operand)) {
					return true;
				}
			}
		}

		return false;
	}*/
	public boolean hasRoleRestriction(Formula formula) {   //for SHQ

		if (formula instanceof Negation) {
			return hasRoleRestriction(formula.getSubFormulas().get(0));
			
		} else if (formula instanceof Geq || formula instanceof Leq) {
			return true;
			
		} else if (formula instanceof Inclusion) {
			return hasRoleRestriction(formula.getSubFormulas().get(0))
					|| hasRoleRestriction(formula.getSubFormulas().get(1));
			
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				if (hasRoleRestriction(operand)) {
					return true;
				}
			}
		}

		return false;
	}

	public boolean isAndInOr(Formula formula) {

		if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();

			for (Formula disjunct : disjunct_list) {
				if (disjunct instanceof And) {
					return true;
				}
			}
		}

		return false;
	}

	public boolean isAndInAnd(Formula formula) {

		if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();

			for (Formula conjunct : conjunct_list) {
				if (conjunct instanceof And) {
					return true;
				}
			}
		}

		return false;
	}

	public boolean isOrInOr(Formula formula) {

		if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();

			for (Formula disjunct : disjunct_list) {
				if (disjunct instanceof Or) {
					return true;
				}
			}
		}

		return false;
	}

	public boolean isOrInAnd(Formula formula) {

		if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();

			for (Formula conjunct : conjunct_list) {
				if (conjunct instanceof Or) {
					return true;
				}
			}
		}

		return false;
	}

	public boolean allNegationsInside(Formula formula) {

		List<Formula> operand_list = formula.getSubFormulas();

		for (Formula operand : operand_list) {
			if (!(operand instanceof Negation)) {
				return false;
			}
		}

		return true;
	}
	
	public boolean isTopLevel(AtomicConcept concept, Geq geq) {
		if(!isPresent(concept,geq)) {
			return false;
		} else {
			Formula tmp = geq.getSubFormulas().get(1);
			if (tmp instanceof AtomicConcept && tmp.equals(concept)) {
				return true;
			} else if (tmp instanceof Or) {
				Or or = (Or) tmp;
				if(or.getSubFormulas().contains(concept) || or.getSubFormulas().contains(new Negation(concept))) {
					return true;
				} else {
					return false;
				}
			} else {
				return false;
			}
				
		}
		
	}

	public boolean isOrInAnd_Strong(Formula formula) {

		if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();

			for (Formula conjunct : conjunct_list) {
				if (conjunct instanceof Or) {
					return true;
				} else {
					if(isOrInAnd_Strong(conjunct)) {
						return true;
					}
				}
			}
		}

		return false;
	}

	public boolean isOrInOr_Strong(Formula formula) {

		if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();

			for (Formula disjunct : disjunct_list) {
				if (disjunct instanceof Or) {
					return true;
				} else {
					if(isOrInOr_Strong(disjunct)) {
						return true;
					}
				}
			}
		}

		return false;
	}

	public boolean isAndInAnd_Strong(Formula formula) {

		if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();

			for (Formula conjunct : conjunct_list) {
				if (conjunct instanceof And) {
					return true;
				} else {
					if (isAndInAnd_Strong(conjunct)) {
						return true;
					}
				}
			}
		}

		return false;
	}

	public boolean isAndInOr_Strong(Formula formula) {
		if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();

			for (Formula disjunct : disjunct_list) {
				if (disjunct instanceof And) {
					return true;
				} else {
					if (isAndInOr_Strong(disjunct)) {
						return true;
					}
				}

			}
		}

		return false;
	}
}
