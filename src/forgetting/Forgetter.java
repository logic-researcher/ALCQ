package forgetting;

import java.util.*;

import checkexistence.EChecker;
import inference.ConceptInference;
import inference.RoleInference;
import org.apache.commons.lang3.tuple.Pair;
import org.semanticweb.HermiT.model.Concept;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import checkfrequency.FChecker;
import checkreducedform.RFChecker;
import concepts.AtomicConcept;
import convertion.BackConverter;
import convertion.Converter;
import extraction.SubsetExtractor;
import formula.Formula;
import inference.Inferencer;
import inference.DefinerIntroducer;
import roles.AtomicRole;
import simplification.Simplifier;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import Exception.CyclicCaseException;
import evaluation.ForgetMine;

public class Forgetter {
	


	public OWLOntology Forgetting(Set<OWLEntity> c_sig, Set<OWLEntity> r_sig, OWLOntology onto)
			throws CloneNotSupportedException, OWLOntologyCreationException, CyclicCaseException {

		System.out.println("The Forgetting Starts:");

		Converter ct = new Converter();
		BackConverter bc = new BackConverter();
		Simplifier simp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		DefinerIntroducer di = new DefinerIntroducer();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		RFChecker rfc = new RFChecker();

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, onto,
				ModuleType.BOT);

		if (!c_sig.isEmpty()) {
			OWLOntology c_module = extractor.extractAsOntology(c_sig, IRI.generateDocumentIRI());
			//System.out.println("c_module size = " + c_module.getAxiomCount());
			manager.removeAxioms(onto, c_module.getAxioms());

			AtomicConcept pivot = null;
			OWLOntology pivot_module = null;
			List<Formula> pivot_list = null;
			List<Formula> exact_list = null;
			Set<OWLEntity> pivot_module_sig = null;

			int i = 1;

			for (OWLEntity owlclass : c_sig) {
				//System.out.println("Forgetting Concept [" + i + "] = " + owlclass.getIRI().getShortForm());
				i++;
				pivot_module_sig = new HashSet<>();
				pivot_module_sig.add(owlclass);
				pivot_module = extractor.extractAsOntology(pivot_module_sig, IRI.generateDocumentIRI());
				// System.out.println("pivot_module size = " + pivot_module.getAxiomCount());
				manager.removeAxioms(c_module, pivot_module.getAxioms());
				pivot = ct.getConceptfromClass(owlclass);
				pivot_list = simp.getCNF(simp.getSimplifiedForm(simp.getClauses(ct.OntologyConverter(pivot_module))));
				// System.out.println("pivot_list size = " + pivot_list.size());
				exact_list = se.getConceptSubset(pivot, pivot_list);
				// System.out.println("exact_list size = " + exact_list.size());

				if (pivot_list.isEmpty()) {

				} else if (fc.negative(pivot, exact_list) == 0) {
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(pivot, exact_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));

				} else if (fc.positive(pivot, exact_list) == 0) {
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(pivot, pivot_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));

				} else if (rfc.isAReducedFormPositive(pivot, exact_list)) {
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(pivot, exact_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));

				} else if (rfc.isAReducedFormNegative(pivot, exact_list)) {
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(pivot, exact_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));

				} else {
					exact_list = simp.getCNF(simp.getSimplifiedForm(di.introduceDefiners(pivot, exact_list)));
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.combination_A(pivot, exact_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
				}
			}

			manager.addAxioms(onto, c_module.getAxioms());
		}

		if (!r_sig.isEmpty()) {
			OWLOntology r_module = extractor.extractAsOntology(r_sig, IRI.generateDocumentIRI());
			//System.out.println("r_module size = " + r_module.getAxiomCount());
			manager.removeAxioms(onto, r_module.getAxioms());

			AtomicRole pivot = null;
			OWLOntology pivot_module = null;
			List<Formula> pivot_list = null;
			Set<OWLEntity> pivot_module_sig = null;

			int i = 1;

			for (OWLEntity owlobjectproperty : r_sig) {
				//System.out.println("Forgetting Role [" + i + "] = " + owlobjectproperty.getIRI().getShortForm());
				i++;
				pivot_module_sig = new HashSet<>();
				pivot_module_sig.add(owlobjectproperty);
				pivot_module = extractor.extractAsOntology(pivot_module_sig, IRI.generateDocumentIRI());
				//System.out.println("pivot_module size = " + pivot_module.getAxiomCount());
				manager.removeAxioms(r_module, pivot_module.getAxioms());
				pivot_list = simp.getCNF(simp.getSimplifiedForm(simp.getClauses(ct.OntologyConverter(pivot_module))));
				pivot = ct.getRoleFromObjectProperty(owlobjectproperty);

				if (pivot_list.isEmpty()) {

				} else {
					pivot_list = di.introduceDefiners(pivot, pivot_list);
					pivot_list = simp.getCNF(simp.getSimplifiedForm(inf.Ackermann_R(pivot, pivot_list)));
					manager.addAxioms(r_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
				}
			}

			manager.addAxioms(onto, r_module.getAxioms());
		}

		if (!DefinerIntroducer.owldefiner_set.isEmpty()) {
			OWLOntology d_module = extractor.extractAsOntology(DefinerIntroducer.owldefiner_set,
					IRI.generateDocumentIRI());
			manager.removeAxioms(onto, d_module.getAxioms());

			AtomicConcept pivot = null;
			OWLOntology pivot_module = null;
			List<Formula> pivot_list = null;
			List<Formula> exact_list = null;
			Set<OWLEntity> pivot_module_sig = null;
			Set<OWLEntity> d_sig = new HashSet<>();

			int k = 1;

			do {
				if (DefinerIntroducer.owldefiner_set.isEmpty()) {
					//System.out.println("Forgetting Successful (D1)!");
					//System.out.println("===================================================");
					manager.addAxioms(onto, d_module.getAxioms());
					return onto;
				}

				d_sig.clear();
				d_sig.addAll(DefinerIntroducer.owldefiner_set);

				for (OWLEntity owlclass : d_sig) {
					//System.out.println("Forgetting Definer [" + k + "] = " + owlclass);
					k++;
					pivot_module_sig = new HashSet<>();
					pivot_module_sig.add(owlclass);
					pivot_module = extractor.extractAsOntology(pivot_module_sig, IRI.generateDocumentIRI());
					// System.out.println("pivot_module size = " + pivot_module.getAxiomCount());
					manager.removeAxioms(d_module, pivot_module.getAxioms());
					pivot = ct.getConceptfromClass(owlclass);
					pivot_list = simp
							.getCNF(simp.getSimplifiedForm(simp.getClauses(ct.OntologyConverter(pivot_module))));
					// System.out.println("pivot_list size = " + pivot_list.size());
					exact_list = se.getConceptSubset(pivot, pivot_list);

					if (pivot_list.isEmpty()) {

					} else if (fc.negative(pivot, exact_list) == 0) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (fc.positive(pivot, exact_list) == 0) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(pivot, pivot_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (rfc.isAReducedFormPositive(pivot, exact_list)) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (rfc.isAReducedFormNegative(pivot, exact_list)) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else {
						exact_list = simp.getCNF(simp.getSimplifiedForm(di.introduceDefiners(pivot, exact_list)));
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.combination_A(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);
					}
				}

			} while (d_sig.size() > DefinerIntroducer.definer_set.size());

			do {
				if (DefinerIntroducer.owldefiner_set.isEmpty()) {
					//System.out.println("Forgetting Successful (D2)!");
					//System.out.println("===================================================");
					manager.addAxioms(onto, d_module.getAxioms());
					return onto;
				}

				d_sig.clear();
				d_sig.addAll(DefinerIntroducer.owldefiner_set);

				for (OWLEntity owlclass : d_sig) {
					//System.out.println("Forgetting Definer [" + k + "] = " + owlclass);
					k++;
					pivot_module_sig = new HashSet<>();
					pivot_module_sig.add(owlclass);
					pivot_module = extractor.extractAsOntology(pivot_module_sig, IRI.generateDocumentIRI());
					// System.out.println("pivot_module size = " + pivot_module.getAxiomCount());
					manager.removeAxioms(d_module, pivot_module.getAxioms());
					pivot = ct.getConceptfromClass(owlclass);
					pivot_list = simp
							.getCNF(simp.getSimplifiedForm(simp.getClauses(ct.OntologyConverter(pivot_module))));
					// System.out.println("pivot_list size = " + pivot_list.size());
					exact_list = se.getConceptSubset(pivot, pivot_list);

					if (pivot_list.isEmpty()) {

					} else if (fc.negative(pivot, exact_list) == 0) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (fc.positive(pivot, exact_list) == 0) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(pivot, pivot_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (rfc.isAReducedFormPositive(pivot, exact_list)) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (rfc.isAReducedFormNegative(pivot, exact_list)) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else {			
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
					}
				}

			} while (d_sig.size() > DefinerIntroducer.owldefiner_set.size());

		}
		//// this is the case of the cyclic cases, that's why the ACK_A is not re-used.
		// In case the results of contains this case. report!

		//System.out.println("Forgetting Successful!");

		return onto;
	}
	public List<Formula> Forgetting(Set<AtomicConcept> c_sig, Set<AtomicRole> r_sig,
			List<Formula> clause_list_normalised) throws CloneNotSupportedException, CyclicCaseException {

		//System.out.println("The Forgetting Starts:");

		Simplifier simp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		DefinerIntroducer di = new DefinerIntroducer();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		RFChecker rfc = new RFChecker();

		if (!c_sig.isEmpty()) {
			List<Formula> c_sig_list_normalised = se.getConceptSubset(c_sig, clause_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int j = 1;
			for (AtomicConcept concept : c_sig) {
				//System.out.println("Forgetting Concept [" + j + "] = " + concept);
				j++;
				pivot_list_normalised = simp
						.getCNF(simp.getSimplifiedForm(inf.transitive_rule(concept,se.getConceptSubset(concept, c_sig_list_normalised))));

				if (pivot_list_normalised.isEmpty()) {

				} else if (fc.negative(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));

				} else if (fc.positive(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));

				} else {
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(di.introduceDefiners(concept, pivot_list_normalised)));
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(inf.combination_A(concept, pivot_list_normalised)));
					c_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			clause_list_normalised.addAll(c_sig_list_normalised);
		}

		/*
		 * if (!c_sig.isEmpty()) { List<Formula> c_sig_list_normalised =
		 * se.getConceptSubset(c_sig, formula_list_normalised); List<Formula>
		 * pivot_list_normalised = null; int j = 1; for (AtomicConcept concept : c_sig)
		 * { System.out.println("Forgetting Concept [" + j + "] = " + concept); j++;
		 * pivot_list_normalised = simp
		 * .getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept,
		 * c_sig_list_normalised)));
		 * 
		 * if (pivot_list_normalised.isEmpty()) {
		 * 
		 * } else if (fc.negative(concept, pivot_list_normalised) == 0) {
		 * c_sig_list_normalised.addAll(
		 * simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept,
		 * pivot_list_normalised))));
		 * 
		 * } else if (fc.positive(concept, pivot_list_normalised) == 0) {
		 * c_sig_list_normalised.addAll(
		 * simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept,
		 * pivot_list_normalised))));
		 * 
		 * } else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
		 * c_sig_list_normalised.addAll(
		 * simp.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(concept,
		 * pivot_list_normalised))));
		 * 
		 * } else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
		 * c_sig_list_normalised.addAll(
		 * simp.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(concept,
		 * pivot_list_normalised))));
		 * 
		 * } else { pivot_list_normalised = simp
		 * .getCNF(simp.getSimplifiedForm(inf.introduceDefiners(concept,
		 * pivot_list_normalised)));
		 * 
		 * pivot_list_normalised = simp
		 * .getCNF(simp.getSimplifiedForm(inf.Ackermann_A(concept,
		 * pivot_list_normalised)));
		 * c_sig_list_normalised.addAll(pivot_list_normalised); } }
		 * 
		 * formula_list_normalised.addAll(c_sig_list_normalised); }
		 */

		if (!r_sig.isEmpty()) {
			List<Formula> r_sig_list_normalised = se.getRoleSubset(r_sig, clause_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int i = 1;
			for (AtomicRole role : r_sig) {
				//System.out.println("Forgetting Role [" + i + "] = " + role);
				i++;
				pivot_list_normalised = simp
						.getCNF(simp.getSimplifiedForm(se.getRoleSubset(role, r_sig_list_normalised)));
				if (pivot_list_normalised.isEmpty()) {

				} else if(fc.positive(role,pivot_list_normalised) == 0){
					r_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(role, pivot_list_normalised))));
	
				} else if(fc.negative(role, pivot_list_normalised) == 0){
					r_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(role, pivot_list_normalised))));
					
				} else {
					pivot_list_normalised = di.introduceDefiners(role, pivot_list_normalised);
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(inf.Ackermann_R(role, pivot_list_normalised)));
					r_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			clause_list_normalised.addAll(r_sig_list_normalised);
		}

		if (!DefinerIntroducer.definer_set.isEmpty()) {
			List<Formula> d_sig_list_normalised = se.getConceptSubset(DefinerIntroducer.definer_set,
					clause_list_normalised);
			d_sig_list_normalised = simp.Delete_formula(d_sig_list_normalised);
			List<Formula> pivot_list_normalised = null;
			Set<AtomicConcept> definer_set = null;

			int k = 1;
			do {
				// System.out.println("d_sig_list_normalised = " + d_sig_list_normalised);
				if (DefinerIntroducer.definer_set.isEmpty()) {
					//System.out.println("Forgetting Successful (D1)!");
					//System.out.println("===================================================");
					clause_list_normalised.addAll(d_sig_list_normalised);

					return clause_list_normalised;
				}

				definer_set = new HashSet<>(DefinerIntroducer.definer_set);

				for (AtomicConcept concept : definer_set) {
					//System.out.println("Forgetting Definer [" + k + "] = " + concept);
					k++;
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, d_sig_list_normalised)));
					if (pivot_list_normalised.isEmpty()) {

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));
						DefinerIntroducer.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));
						DefinerIntroducer.definer_set.remove(concept);

					} /*
					 * else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
					 * d_sig_list_normalised.addAll(simp.getCNF(
					 * simp.getSimplifiedForm(inf.AckermannPositive(concept,
					 * pivot_list_normalised)))); Inferencer.definer_set.remove(concept);
					 *
					 * } else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
					 * d_sig_list_normalised.addAll(simp.getCNF(
					 * simp.getSimplifiedForm(inf.AckermannNegative(concept,
					 * pivot_list_normalised)))); Inferencer.definer_set.remove(concept);
					 *
					 * }
					 */ else {
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						pivot_list_normalised = simp
								.getCNF(simp.getSimplifiedForm(inf.combination_A(concept, pivot_list_normalised)));
						d_sig_list_normalised.addAll(pivot_list_normalised);
						DefinerIntroducer.definer_set.remove(concept);

					}
				}

			} while (definer_set.size() > DefinerIntroducer.definer_set.size());
			//// this is the case of the cyclic cases, that's why the ACK_A is not re-used.
			// In case the results of contains this case. report!
			do {
				if (DefinerIntroducer.definer_set.isEmpty()) {
					//System.out.println("Forgetting Successful (D2)!");
					//System.out.println("===================================================");

					clause_list_normalised.addAll(d_sig_list_normalised);
					return clause_list_normalised;
				}

				//System.out.println("The formula might contain cylic case: " + d_sig_list_normalised);

				definer_set = new HashSet<>(DefinerIntroducer.definer_set);

				for (AtomicConcept concept : definer_set) {
					//System.out.println("Forgetting Definer [" + k + "] = " + concept);
					k++;
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, d_sig_list_normalised)));
					if (pivot_list_normalised.isEmpty()) {
						DefinerIntroducer.definer_set.remove(concept);

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));
						DefinerIntroducer.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));
						DefinerIntroducer.definer_set.remove(concept);

					} else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(concept, pivot_list_normalised))));
						DefinerIntroducer.definer_set.remove(concept);

					} else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(concept, pivot_list_normalised))));
						DefinerIntroducer.definer_set.remove(concept);

					} else {
						d_sig_list_normalised.addAll(pivot_list_normalised);
					}
				}

			} while (definer_set.size() > DefinerIntroducer.definer_set.size());

		}
		// in this case, the forgetting solution contain definers.
		//System.out.println("Forgetting Successful!");

		return clause_list_normalised;
	}

	public List<Formula> Forgetting_new(Set<AtomicConcept> c_sig, Set<AtomicRole> r_sig,
										List<Formula> clause_list_normalised) throws CloneNotSupportedException ,CyclicCaseException{
		Simplifier simp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		DefinerIntroducer di = new DefinerIntroducer();
		Inferencer inf = new Inferencer();
		RoleInference rInf = new RoleInference();
		ConceptInference cInf = new ConceptInference();
		FChecker fc = new FChecker();
		RFChecker rfc = new RFChecker();

		if (!c_sig.isEmpty()) {
			List<Formula> c_sig_list_normalised = se.getConceptSubset(c_sig, clause_list_normalised);
			ForgetMine.formula_size1 = c_sig_list_normalised.size();
			List<Formula> pivot_list_normalised = null;
			int j = 1;
			List<AtomicConcept> C_list = ordering(c_sig,c_sig_list_normalised);
			for (AtomicConcept concept : C_list) {
				DefinerIntroducer.reset();

				//System.out.println("Forgetting Concept [" + j + "] = " + concept);
				j++;
				pivot_list_normalised = simp
						.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, c_sig_list_normalised)));
				//System.out.println("forget:["+concept+"]"+"  "+pivot_list_normalised.size()+"  "+pivot_list_normalised);
				if (pivot_list_normalised.isEmpty()) {

				} else if (fc.negative(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));

				} else if (fc.positive(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));

				} else {
					pivot_list_normalised = simp.getCNF(simp.getSimplifiedForm(simp.converge(concept,pivot_list_normalised)));
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(di.introduceDefiners(concept, pivot_list_normalised)));
					//pivot_list_normalised = simp
					//		.getCNF(simp.getSimplifiedForm(di.Intro_Cyclic_Definers(concept, pivot_list_normalised)));
					ForgetMine.formula_size2 = pivot_list_normalised.size();
					ForgetMine.updateMax();

					List<Formula> forgettingResult = cInf.strongForgetting(concept, pivot_list_normalised);
					if (forgettingResult == null) {
						forgettingResult = inf.combination_A(concept, pivot_list_normalised);
					}
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(forgettingResult));
					ForgetMine.formula_size2 = pivot_list_normalised.size();
					ForgetMine.updateMax();

					pivot_list_normalised = simp.getCNF(simp.getSimplifiedForm(S_Definer_forgetting(pivot_list_normalised)));
					c_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}
			clause_list_normalised.addAll(c_sig_list_normalised);
		}
		if (!r_sig.isEmpty()) {
			int j = 1;
			List<Formula> pivot_list_normalised = null;
			for (AtomicRole role : r_sig) {
//				if (Converter.TransitiveRole_Set.contains(role)){
//					System.out.println(role +" is a transitive role, cannot be forgetten");
//					continue;
//				}
				System.out.println("Forgetting Role [" + j + "] = " + role);
				j++;
				pivot_list_normalised = simp
						.getCNF(simp.getSimplifiedForm(se.getRoleSubset(role, clause_list_normalised)));
				pivot_list_normalised.addAll(se.getRoleReplaceEntailment(role,clause_list_normalised));
				DefinerIntroducer.reset();
				if (pivot_list_normalised.isEmpty()) {

				} else if(fc.positive(role,pivot_list_normalised) == 0){
					clause_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(role, pivot_list_normalised))));

				} else if(fc.negative(role, pivot_list_normalised) == 0){
					clause_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(role, pivot_list_normalised))));

				} else {
					pivot_list_normalised = simp.getCNF(simp.getSimplifiedForm(di.introduceDefiners(role, pivot_list_normalised)));
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(rInf.forgettingRole(role, pivot_list_normalised)));
					pivot_list_normalised = forget_definer(pivot_list_normalised);
					clause_list_normalised.addAll(pivot_list_normalised);
				}
			}
		}
		return clause_list_normalised;
	}

	public List<Formula> forget_definer(List<Formula> formula_list) throws CloneNotSupportedException ,CyclicCaseException{
		Simplifier simp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		DefinerIntroducer di = new DefinerIntroducer();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();

		if(!DefinerIntroducer.definer_set.isEmpty()){
			List<Formula> d_sig_list_normalised = simp.getCNF(simp.getSimplifiedForm(se.getConceptSubset(DefinerIntroducer.definer_set,
					formula_list)));
			ForgetMine.formula_size1 = d_sig_list_normalised.size();
			List<Formula> pivot_list_normalised = null;
			Set<AtomicConcept> definer_set = null;

			do {
				if (DefinerIntroducer.definer_set.isEmpty()) {
					formula_list.addAll(d_sig_list_normalised);
					return formula_list;
				} else if (AtomicConcept.getDefiner_index()>500){
					formula_list.addAll(d_sig_list_normalised);
					DefinerIntroducer.reset();
					return formula_list;
				}

				definer_set = new HashSet<>(DefinerIntroducer.definer_set);
				List<AtomicConcept> d_list = ordering(definer_set,d_sig_list_normalised);

				for (AtomicConcept concept : d_list) {
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, d_sig_list_normalised)));
					//System.out.println("forget:["+concept+"]"+"  "+pivot_list_normalised.size());
					if (pivot_list_normalised.isEmpty()) {
						DefinerIntroducer.definer_set.remove(concept);
					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));
						DefinerIntroducer.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));
						DefinerIntroducer.definer_set.remove(concept);

					} else {
						pivot_list_normalised = simp.getCNF(simp.getSimplifiedForm(simp.converge(concept,pivot_list_normalised)));
						pivot_list_normalised = simp.getCNF(simp.getSimplifiedForm(di.introduceDefiners(concept, pivot_list_normalised)));
						ForgetMine.formula_size2 = pivot_list_normalised.size();
						ForgetMine.updateMax();
						pivot_list_normalised = simp
								.getCNF(simp.getSimplifiedForm(inf.combination_A(concept, pivot_list_normalised)));
						ForgetMine.formula_size2 = pivot_list_normalised.size();
						ForgetMine.updateMax();
						d_sig_list_normalised.addAll(pivot_list_normalised);
						DefinerIntroducer.definer_set.remove(concept);

					}
				}
				formula_list.addAll(d_sig_list_normalised);


			} while (definer_set.size()*2+10 > DefinerIntroducer.definer_set.size());

			return formula_list;

		}
		return formula_list;
	}

	public List<Formula> S_Definer_forgetting(List<Formula> formula_list) throws CloneNotSupportedException,CyclicCaseException{
		Simplifier simp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		DefinerIntroducer di = new DefinerIntroducer();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		EChecker ec = new EChecker();

		if(!DefinerIntroducer.cyclic_definer_set.isEmpty()) {
			if (!DefinerIntroducer.definer_set.isEmpty()) {
				formula_list = forget_definer(formula_list);
			}
			while(true) {
				formula_list.addAll(DefinerIntroducer.reuse_formula);
				List<Formula> cd_sig_list_normalised = simp.getCNF(simp.getSimplifiedForm(se.getConceptSubset(DefinerIntroducer.cyclic_definer_set,
						formula_list)));
				List<Formula> pivot_list_normalised = null;
				Set<AtomicConcept> definer_set = new HashSet<>(DefinerIntroducer.cyclic_definer_set);
				List<AtomicConcept> dd_list = ordering(definer_set,cd_sig_list_normalised);
				for (AtomicConcept concept : dd_list ) {

					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, cd_sig_list_normalised)));
					//System.out.println("forget:["+concept+"]"+"  "+pivot_list_normalised.size());
					if (pivot_list_normalised.isEmpty()) {

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						cd_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));


					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						cd_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));


					} else {
						pivot_list_normalised = simp.getCNF(simp.getSimplifiedForm(simp.converge(concept,pivot_list_normalised)));
						pivot_list_normalised = simp.getCNF(simp.getSimplifiedForm(di.introduceDefiners(concept, pivot_list_normalised)));
						if (concept.getText().startsWith("Definer_Cyc")){
							pivot_list_normalised.add(DefinerIntroducer.Cyclic_map.get(concept).clone());
						}
						pivot_list_normalised = simp
								.getCNF(simp.getSimplifiedForm(inf.combination_A(concept, pivot_list_normalised)));
						cd_sig_list_normalised.addAll(pivot_list_normalised);
					}
				}
				formula_list.addAll(cd_sig_list_normalised);
				if (!DefinerIntroducer.definer_set.isEmpty()) {
					formula_list = forget_definer(formula_list);
				} else {
					List<Formula> dup_list = new ArrayList<>(formula_list);
					for (Formula formula : dup_list) {
						for (AtomicConcept concept : DefinerIntroducer.cyclic_definer_set) {
							if (ec.isPresent(concept,formula)){
								formula_list.remove(formula);
								break;
							}
						}
					}
					return formula_list;
				}
			}

		} else {
			if (!DefinerIntroducer.definer_set.isEmpty()) {
				formula_list = forget_definer(formula_list);
			}
			return formula_list;
		}


	}

	public List<AtomicConcept> ordering(Set<AtomicConcept> c_sig,List<Formula> c_sig_list_normalised){
		List<Formula> now_c_sig_list_normalised = new ArrayList<>(c_sig_list_normalised);
		List<AtomicConcept> now = new ArrayList<>(c_sig);
		FChecker fc = new FChecker();
		Queue<Pair<Integer,AtomicConcept>> Q = new PriorityQueue<>(new queueComparator());
		List<AtomicConcept> ans = new ArrayList<>();
		SubsetExtractor se = new SubsetExtractor();
		int t = 0;
		for(AtomicConcept concept : now){
			int num = 0;
			List<Formula>pivot_list_normalised = se.getConceptSubset(concept, now_c_sig_list_normalised);
			num=fc.positive(concept,pivot_list_normalised);
			num*=fc.negative(concept,pivot_list_normalised);
			Pair<Integer,AtomicConcept> temp = Pair.of(num,concept);
			Q.add(temp);
			//System.out.println(now.size()+" "+t);
			t++;

		}
		while(!Q.isEmpty()){
			Pair<Integer,AtomicConcept> temp=Q.poll();
			//System.out.println(temp.getKey());
			ans.add(temp.getValue());
		}
		return ans;

	}


}

class queueComparator implements  Comparator<Pair<Integer,AtomicConcept>>{
	public int compare(Pair<Integer,AtomicConcept> e1, Pair<Integer,AtomicConcept> e2) {
		return e1.getKey() - e2.getKey();//升序
		//return e2.getKey() - e1.getKey();//降序

	}
}