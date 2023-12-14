package extraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import checkfrequency.FChecker;
import com.google.common.collect.Sets;

import checkexistence.EChecker;
import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Geq;
import connectives.Leq;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import roles.AtomicRole;
import inference.Inferencer;
import inference.DefinerIntroducer;
import simplification.Simplifier;
import Exception.CyclicCaseException;

public class SubsetExtractor {

	public SubsetExtractor() {

	}
		
	/*public Set<AtomicRole> getRolesFromFormula(Formula formula) {
		
		Set<AtomicRole> role_set = new HashSet<>();
		
		if (formula instanceof AtomicRole) {
			AtomicRole role = (AtomicRole) formula;
			role_set.add(role);
			
		} else if (formula instanceof Negation) {
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists || formula instanceof Forall) {
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(0)));
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				role_set.addAll(getRolesFromFormula(operand));
			}			
		}

		return role_set;
	}*/

	public Set<AtomicRole> getRoleFromFormulaList(List<Formula> formula_list){
		Set<AtomicRole> output_list = new HashSet<>();
		for (Formula formula : formula_list){
			output_list.addAll(getRolesFromFormula(formula));
		}
		return output_list;
	}

	public Set<AtomicConcept> getConceptFromFormulaList(List<Formula> formula_list){
		Set<AtomicConcept> output_list = new HashSet<>();
		for (Formula formula : formula_list){
			output_list.addAll(getConceptsFromFormula(formula));
		}
		return output_list;
	}

	public Set<AtomicRole> getRolesFromFormula(Formula formula) {  //for SHQ
		
		Set<AtomicRole> role_set = new HashSet<>();
		
		if (formula instanceof AtomicRole) {
			AtomicRole role = (AtomicRole) formula;
			role_set.add(role);
			
		} else if (formula instanceof Negation) {
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Leq || formula instanceof Geq) {
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(0)));
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				role_set.addAll(getRolesFromFormula(operand));
			}			
		}

		return role_set;
	}
	
	public Set<AtomicConcept> getConceptsFromFormula(Formula formula) {
		
		Set<AtomicConcept> concept_set = new HashSet<>();
		
		if (formula instanceof AtomicConcept) {
			AtomicConcept concept = (AtomicConcept) formula;
			concept_set.add(concept);
			
		} else if (formula instanceof Negation) {
			concept_set.addAll(getConceptsFromFormula(formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists || formula instanceof Forall
				|| formula instanceof Leq || formula instanceof Geq) {
			concept_set.addAll(getConceptsFromFormula(formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				concept_set.addAll(getConceptsFromFormula(operand));
			}
		}

		return concept_set;
	}
		
	/*
	public List<Formula> getConceptSubset(AtomicConcept concept, List<Formula> formula_list) {

		EChecker ce = new EChecker();
		List<Formula> concept_list = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			if (ce.isPresent(concept, formula)) {
				concept_list.add(formula);
				formula_list.remove(i);
				i--;
			}
		}
		
		return concept_list;
	}*/
	
	public List<Formula> getConceptSubset(AtomicConcept concept, List<Formula> formula_list) {

		EChecker ce = new EChecker();
		
		  /*List<Formula> concept_list = new ArrayList<>();
		  
		  for (int i = 0; i < formula_list.size(); i++) { Formula formula =
		 formula_list.get(i); if (ce.isPresent(concept, formula)) {
		  concept_list.add(formula); formula_list.remove(i); i--; } }*/
		 

		List<Formula> concept_list = formula_list.stream()
				.filter(formula -> ce.isPresent(concept, formula))
				.collect(Collectors.toList());
		formula_list.removeAll(concept_list);

		return concept_list;
	}
		
	public List<Formula> getConceptSubset(Set<AtomicConcept> c_sig, List<Formula> formula_list) {

		
		List<Formula> c_sig_subset = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			if (!Sets.intersection(getConceptsFromFormula(formula), c_sig).isEmpty()) {
				//System.out.println("index i = " + i);
				c_sig_subset.add(formula);
				formula_list.remove(i);
				i--;
			}
		}
		
		/*List<Formula> c_sig_subset = formula_list.stream()
				.filter(formula -> !Collections.disjoint(getConceptsFromFormula(formula), c_sig))
				.collect(Collectors.toList());*/
		 

		/*List<Formula> c_sig_subset = formula_list.stream()
				.filter(formula -> !Sets.intersection(getConceptsFromFormula(formula), c_sig).isEmpty())
				.collect(Collectors.toList());*/
		
		//formula_list.removeAll(c_sig_subset);

		return c_sig_subset;
	}
		
	public List<Formula> getRoleSubset(AtomicRole role, List<Formula> formula_list) {

		EChecker ce = new EChecker();
		/*List<Formula> role_list = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			if (ce.isPresent(role, formula)) {
				role_list.add(formula);
				formula_list.remove(i);
				i--;
			}
		}*/
		
		List<Formula> role_list = formula_list.stream()
				.filter(formula -> ce.isPresent(role, formula))
				.collect(Collectors.toList());
		formula_list.removeAll(role_list);

		return role_list;
	}


	public List<Formula> getRoleSubsetNotRm(AtomicRole role, List<Formula> formula_list) {

		EChecker ce = new EChecker();
		/*List<Formula> role_list = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			if (ce.isPresent(role, formula)) {
				role_list.add(formula);
				formula_list.remove(i);
				i--;
			}
		}*/

		List<Formula> role_list = formula_list.stream()
				.filter(formula -> ce.isPresent(role, formula))
				.collect(Collectors.toList());


		return role_list;
	}
	
	public List<Formula> getRoleSubset(Set<AtomicRole> r_sig, List<Formula> formula_list) {

		/* List<Formula> r_sig_subset = new ArrayList<>(); */

		/*
		 * for (int i = 0; i < formula_list.size(); i++) { Formula formula =
		 * formula_list.get(i); if (!Sets.intersection(getRolesFromFormula(formula),
		 * r_sig).isEmpty()) { r_sig_subset.add(formula); formula_list.remove(i); i--; }
		 * }
		 */
		
		List<Formula> r_sig_subset = formula_list.stream()
				.filter(formula -> !Collections.disjoint(getRolesFromFormula(formula), r_sig))
				.collect(Collectors.toList());

		/*List<Formula> r_sig_subset = formula_list.stream()
				.filter(formula -> !Sets.intersection(getRolesFromFormula(formula), r_sig).isEmpty())
				.collect(Collectors.toList());*/
		
		formula_list.removeAll(r_sig_subset);

		return r_sig_subset;
	}

	public Set<AtomicConcept> getDefinersFromFormula(Formula formula) {

		Set<AtomicConcept> concept_set = new HashSet<>();

		if (formula instanceof AtomicConcept && formula.getText().startsWith("Definer")) {
			AtomicConcept concept = (AtomicConcept) formula;
			concept_set.add(concept);

		} else if (formula instanceof Negation) {
			concept_set.addAll(getDefinersFromFormula(formula.getSubFormulas().get(0)));

		} else if (formula instanceof Exists || formula instanceof Forall
				|| formula instanceof Leq || formula instanceof Geq) {
			concept_set.addAll(getDefinersFromFormula(formula.getSubFormulas().get(1)));

		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				concept_set.addAll(getDefinersFromFormula(operand));
			}
		}

		return concept_set;
	}

	public List<Formula> getRoleReplaceEntailment(AtomicRole role,List<Formula> clause_list) throws CloneNotSupportedException, CyclicCaseException {
		FChecker fc = new FChecker();
		Inferencer inf = new Inferencer();
		DefinerIntroducer di = new DefinerIntroducer();
		Simplifier simp = new Simplifier();

		List<Formula> output_list = new ArrayList<>();
		Set<AtomicRole> superRolelist = Inferencer.getsuperRoles(role, new HashSet<>());
		Set<AtomicRole> subRolelist = Inferencer.getsubRoles(role, new HashSet<>());
		subRolelist.remove(role);
		superRolelist.remove(role);
		if (superRolelist.isEmpty() && subRolelist.isEmpty()){
			return output_list;
		}   else {
			if (!subRolelist.isEmpty()){
				for (AtomicRole subRole : subRolelist){
					DefinerIntroducer.reset();
					List<Formula> forget_list = getRoleSubsetNotRm(subRole, clause_list);
					forget_list = simp.getCNF(simp.getSimplifiedForm(di.introduceDefiners(subRole,forget_list)));
					forget_list = simp.getCNF(simp.getSimplifiedForm(inf.RoleReplace_3(subRole,role,forget_list)));
					output_list.addAll(forget_list);
				}
			}

			if (!superRolelist.isEmpty()){
				for (AtomicRole superRole : superRolelist){
					DefinerIntroducer.reset();
					List<Formula> forget_list = getRoleSubsetNotRm(superRole, clause_list);
					forget_list = simp.getCNF(simp.getSimplifiedForm(di.introduceDefiners(superRole,forget_list)));
					forget_list = simp.getCNF(simp.getSimplifiedForm(inf.RoleReplace_2(role,superRole,forget_list)));
					output_list.addAll(forget_list);
				}
			}

		}

		return output_list;
	}

}
