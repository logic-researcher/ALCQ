/*
1 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package convertion;

import concepts.AtomicConcept;
import concepts.BottomConcept;
import concepts.ConceptExpression;
import concepts.TopConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import preasoner.RoleTreeNode;
import connectives.Geq;
import connectives.Inclusion;
import connectives.Leq;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import individual.Individual;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import roles.*;

import java.util.*;

import javax.management.relation.Role;


/**
 *
 * @author Yizheng
 */
public class Converter {
	
	public static Set<AtomicRole> TransitiveRole_Set = new HashSet<>();
	public static Set<AtomicRole> IrreflexiveRole_Set = new HashSet<>();
	public static Map<AtomicRole, OWLObjectProperty> RoleMap = new HashMap<>();
	public static Map<AtomicConcept, OWLClass> ConceptMap = new HashMap<>();
	public static Map<AtomicRole,RoleTreeNode> RoleNodeMap = new HashMap<>();
	public static OWLOntology ontology = null;
	public static OWLReasoner reasoner = null;
	
	private static int i = 0;
	private static int j = 0;
	private static int k = 0;
	private static int l = 0;
	private static int m = 0;
	private static int n = 0;
	private static int o = 0;
	private static int p = 0;
	private static int q = 0;
	private static int r = 0;
	private static int s = 0;

	private OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	private OWLDataFactory factory = manager.getOWLDataFactory();

	public void CReset(){
		TransitiveRole_Set.clear();
		IrreflexiveRole_Set.clear();
		RoleMap.clear();
		ConceptMap.clear();
		RoleNodeMap.clear();
		RoleMap.put(TopRole.getInstance(),factory.getOWLTopObjectProperty());
		RoleMap.put(BottomRole.getInstance(),factory.getOWLBottomObjectProperty());
		RoleNodeMap.put(TopRole.getInstance(),new RoleTreeNode(TopRole.getInstance()));
		RoleNodeMap.put(BottomRole.getInstance(),new RoleTreeNode(BottomRole.getInstance()));
		reasoner = null;
		ontology = null;
	}
		
	public AtomicConcept getConceptfromClass(OWLEntity owlClass) {
		return new AtomicConcept(owlClass.getIRI().toString());
	}
	
	public AtomicRole getRoleFromObjectProperty(OWLEntity owlObjectProperty) {		
		return new AtomicRole(owlObjectProperty.getIRI().toString());
	}
	
	public Individual getIndividualFromNamedIndividual(OWLNamedIndividual owlNamedIndividual) {		
		return new Individual(owlNamedIndividual.getIRI().toString());
	}
	
	public AtomicConcept getConceptfromClass_ShortForm(OWLClass owlClass) {
		return new AtomicConcept(owlClass.getIRI().getShortForm());
	}
	
	public AtomicRole getRoleFromObjectProperty_ShortForm(OWLObjectProperty owlObjectProperty) {		
		return new AtomicRole(owlObjectProperty.getIRI().getShortForm());
	}
	
	public Individual getIndividualFromNamedIndividual_ShortForm(OWLNamedIndividual owlNamedIndividual) {		
		return new Individual(owlNamedIndividual.getIRI().getShortForm());
	}
	
	public Set<AtomicConcept> getConceptsfromClasses(Set<OWLClass> class_set) {

		Set<AtomicConcept> concept_set = new HashSet<>();

		for (OWLClass owlClass : class_set) {
			concept_set.add(getConceptfromClass(owlClass));
		}

		return concept_set;
	}
		
	public Set<AtomicRole> getRolesfromObjectProperties(Set<OWLObjectProperty> op_set) {

		Set<AtomicRole> role_set = new HashSet<>();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_set.add(getRoleFromObjectProperty(owlObjectProperty));
		}

		return role_set;
	}
	
	public Set<Individual> getIndividualsfromNamedIndividuals(Set<OWLNamedIndividual> ni_set) {

		Set<Individual> indi_set = new HashSet<>();

		for (OWLNamedIndividual owlNamedIndividual : ni_set) {
			indi_set.add(getIndividualFromNamedIndividual(owlNamedIndividual));
		}

		return indi_set;
	}
	
	public Set<AtomicConcept> getConceptsfromClasses_ShortForm(Set<OWLClass> class_set) {

		Set<AtomicConcept> concept_set = new HashSet<>();

		for (OWLClass owlClass : class_set) {
			concept_set.add(getConceptfromClass_ShortForm(owlClass));
		}

		return concept_set;
	}
		
	public Set<AtomicRole> getRolesfromObjectProperties_ShortForm(Set<OWLObjectProperty> op_set) {

		Set<AtomicRole> role_set = new HashSet<>();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_set.add(getRoleFromObjectProperty_ShortForm(owlObjectProperty));
		}

		return role_set;
	}
	
	public Set<Individual> getIndividualsfromNamedIndividuals_ShortForm(Set<OWLNamedIndividual> ni_set) {

		Set<Individual> indi_set = new HashSet<>();

		for (OWLNamedIndividual owlNamedIndividual : ni_set) {
			indi_set.add(getIndividualFromNamedIndividual_ShortForm(owlNamedIndividual));
		}

		return indi_set;
	}
				
	public List<AtomicConcept> getConceptsInSignature(OWLOntology ontology) {

		List<AtomicConcept> concept_list = new ArrayList<>();
		Set<OWLClass> class_set = ontology.getClassesInSignature();

		for (OWLClass owlClass : class_set) {
			AtomicConcept concept = getConceptfromClass(owlClass);
			ConceptMap.put(concept,owlClass);
			concept_list.add(concept);
		}

		return concept_list;
	}
		
	public List<AtomicRole> getRolesInSignature(OWLOntology ontology) {

		List<AtomicRole> role_list = new ArrayList<>();
		Set<OWLObjectProperty> op_set = ontology.getObjectPropertiesInSignature();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			AtomicRole role = getRoleFromObjectProperty(owlObjectProperty);
			RoleNodeMap.put(role, new RoleTreeNode(role));
			RoleMap.put(role, owlObjectProperty);
			role_list.add(role);
		}

		return role_list;
	}
	
	public List<Individual> getIndividualsInSignature(OWLOntology ontology) {

		List<Individual> indi_list = new ArrayList<>();
		Set<OWLNamedIndividual> individual_set = ontology.getIndividualsInSignature();

		for (OWLNamedIndividual owlIndividual : individual_set) {
			indi_list.add(getIndividualFromNamedIndividual(owlIndividual));
		}

		return indi_list;
	}
	
	public List<AtomicConcept> getConceptsInSignature_ShortForm(OWLOntology ontology) {

		List<AtomicConcept> concept_list = new ArrayList<>();
		Set<OWLClass> class_set = ontology.getClassesInSignature();

		for (OWLClass owlClass : class_set) {
			AtomicConcept concept = getConceptfromClass_ShortForm(owlClass);
			ConceptMap.put(concept,owlClass);
			concept_list.add(concept);
		}

		return concept_list;
	}
	
	public List<AtomicRole> getRolesInSignature_ShortForm(OWLOntology ontology) {

		List<AtomicRole> role_list = new ArrayList<>();
		Set<OWLObjectProperty> op_set = ontology.getObjectPropertiesInSignature();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			AtomicRole role = getRoleFromObjectProperty_ShortForm(owlObjectProperty);
			RoleNodeMap.put(role, new RoleTreeNode(role));
			RoleMap.put(role, owlObjectProperty);
			role_list.add(role);
		}

		return role_list;
	}
	
	public List<Individual> getIndividualsInSignature_ShortForm(OWLOntology ontology) {

		List<Individual> indi_list = new ArrayList<>();
		Set<OWLNamedIndividual> individual_set = ontology.getIndividualsInSignature();

		for (OWLNamedIndividual owlIndividual : individual_set) {
			indi_list.add(getIndividualFromNamedIndividual_ShortForm(owlIndividual));
		}

		return indi_list;
	}

	public List<Formula> OntologyConverter(OWLOntology ontology) {

		List<Formula> formula_list = new ArrayList<>();
		reasoner = new Reasoner.ReasonerFactory().createReasoner(ontology);
		Set<OWLLogicalAxiom> owlAxiom_set = ontology.getLogicalAxioms();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter(owlAxiom));
		}

		return formula_list;
	}
	
	public List<Formula> OntologyConverter_ShortForm(OWLOntology Ontology) {

		List<Formula> formula_list = new ArrayList<>();
		ontology = Ontology;
		reasoner = new Reasoner.ReasonerFactory().createReasoner(Ontology);
		Set<OWLLogicalAxiom> owlAxiom_set = Ontology.getLogicalAxioms();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter_ShortForm(owlAxiom));
		}

		return formula_list;
	}
	
	public List<Formula> AxiomsConverter(Set<OWLAxiom> owlAxiom_set) {

		List<Formula> formula_list = new ArrayList<>();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter(owlAxiom));
		}

		return formula_list;
	}
	
	public List<Formula> AxiomsConverter_ShortForm(Set<OWLAxiom> owlAxiom_set) {

		List<Formula> formula_list = new ArrayList<>();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter_ShortForm(owlAxiom));
		}

		return formula_list;
	}
		
	public List<Formula> AxiomConverter(OWLAxiom axiom) {

		if (axiom instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
			Formula converted = new Inclusion(ClassExpressionConverter(owlSCOA.getSubClass()),
					ClassExpressionConverter(owlSCOA.getSuperClass()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentClassesAxiom) {
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
			Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter(owlSCOA));
			}
			return converted;

		} else if (axiom instanceof OWLDisjointClassesAxiom) {
			OWLDisjointClassesAxiom owlDCA = (OWLDisjointClassesAxiom) axiom;
			Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlDCA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter(owlSCOA));
			}
			return converted;

		} else if (axiom instanceof OWLDisjointUnionAxiom) {
			OWLDisjointUnionAxiom owlDUA = (OWLDisjointUnionAxiom) axiom;
			OWLEquivalentClassesAxiom owlECA = owlDUA.getOWLEquivalentClassesAxiom();
			OWLDisjointClassesAxiom owlDCA = owlDUA.getOWLDisjointClassesAxiom();
			List<Formula> converted = new ArrayList<>();
			converted.addAll(AxiomConverter(owlECA));
			converted.addAll(AxiomConverter(owlDCA));
			return converted;

		} else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPDA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom owlOPRA = (OWLObjectPropertyRangeAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPRA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} else if (axiom instanceof OWLFunctionalObjectPropertyAxiom) {
			OWLFunctionalObjectPropertyAxiom owlFOPA = (OWLFunctionalObjectPropertyAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlFOPA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} else if (axiom instanceof OWLSubObjectPropertyOfAxiom) {
			OWLSubObjectPropertyOfAxiom owlSOPOA = (OWLSubObjectPropertyOfAxiom) axiom;
			Formula converted = new Inclusion(RoleExpressionConverter(owlSOPOA.getSubProperty()),
					RoleExpressionConverter(owlSOPOA.getSuperProperty()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentObjectPropertiesAxiom) {
			OWLEquivalentObjectPropertiesAxiom owlEOPA = (OWLEquivalentObjectPropertiesAxiom) axiom;
			Collection<OWLSubObjectPropertyOfAxiom> owlSOPOAs = owlEOPA.asSubObjectPropertyOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubObjectPropertyOfAxiom owlSOPOA : owlSOPOAs) {
				converted.addAll(AxiomConverter(owlSOPOA));
			}
			return converted;
		
		} else if (axiom instanceof OWLTransitiveObjectPropertyAxiom) {
			OWLTransitiveObjectPropertyAxiom owlOTOPA = (OWLTransitiveObjectPropertyAxiom) axiom;
			TransitiveRole_Set.add((AtomicRole) RoleExpressionConverter(owlOTOPA.getProperty()));
			return Collections.emptyList();
			
		} else if (axiom instanceof OWLIrreflexiveObjectPropertyAxiom) {
			OWLIrreflexiveObjectPropertyAxiom owlIROPA = (OWLIrreflexiveObjectPropertyAxiom) axiom;
			IrreflexiveRole_Set.add((AtomicRole) RoleExpressionConverter(owlIROPA.getProperty()));
			return Collections.emptyList();
			
		}
			/*else if (axiom instanceof OWLClassAssertionAxiom) {
		}
			OWLClassAssertionAxiom owlCAA = (OWLClassAssertionAxiom) axiom;
			Formula converted = new Inclusion(IndividualConverter(owlCAA.getIndividual()),
					ClassExpressionConverter(owlCAA.getClassExpression()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLObjectPropertyAssertionAxiom) {
			OWLObjectPropertyAssertionAxiom owlOPAA = (OWLObjectPropertyAssertionAxiom) axiom;
			Formula converted = new Inclusion(IndividualConverter(owlOPAA.getSubject()), new Exists(
					RoleExpressionConverter(owlOPAA.getProperty()), IndividualConverter(owlOPAA.getObject())));
			return Collections.singletonList(converted);
		}*/

		return Collections.emptyList();
	}
	
	public List<Formula> AxiomConverter_ShortForm(OWLAxiom axiom) {

		if (axiom instanceof OWLSubClassOfAxiom) {
			setI(getI() + 1);
			OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
			Formula converted = new Inclusion(ClassExpressionConverter_ShortForm(owlSCOA.getSubClass()),
					ClassExpressionConverter_ShortForm(owlSCOA.getSuperClass()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentClassesAxiom) {
			setJ(getJ() + 1);
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
			Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter_ShortForm(owlSCOA));
			}
			return converted;

		} else if (axiom instanceof OWLDisjointClassesAxiom) {
			setK(getK() + 1);
			OWLDisjointClassesAxiom owlDCA = (OWLDisjointClassesAxiom) axiom;
			Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlDCA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter_ShortForm(owlSCOA));
			}
			return converted;

		} else if (axiom instanceof OWLDisjointUnionAxiom) {
			setL(getL() + 1);
			OWLDisjointUnionAxiom owlDUA = (OWLDisjointUnionAxiom) axiom;
			OWLEquivalentClassesAxiom owlECA = owlDUA.getOWLEquivalentClassesAxiom();
			OWLDisjointClassesAxiom owlDCA = owlDUA.getOWLDisjointClassesAxiom();
			List<Formula> converted = new ArrayList<>();
			converted.addAll(AxiomConverter_ShortForm(owlECA));
			converted.addAll(AxiomConverter_ShortForm(owlDCA));
			return converted;

		} else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			setM(getM() + 1);
			OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPDA.asOWLSubClassOfAxiom();
			return AxiomConverter_ShortForm(owlSCOA);

		} else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			setN(getN() + 1);
			OWLObjectPropertyRangeAxiom owlOPRA = (OWLObjectPropertyRangeAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPRA.asOWLSubClassOfAxiom();
			return AxiomConverter_ShortForm(owlSCOA);
		} else if (axiom instanceof OWLFunctionalObjectPropertyAxiom) {
			OWLFunctionalObjectPropertyAxiom owlFOPA = (OWLFunctionalObjectPropertyAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlFOPA.asOWLSubClassOfAxiom();
			return AxiomConverter_ShortForm(owlSCOA);

		}
		/*else if (axiom instanceof OWLSubObjectPropertyOfAxiom) {
			setO(getO() + 1);
			OWLSubObjectPropertyOfAxiom owlSOPOA = (OWLSubObjectPropertyOfAxiom) axiom;
			AtomicRole subrole = (AtomicRole) RoleExpressionConverter_ShortForm(owlSOPOA.getSubProperty());
			AtomicRole superrole = (AtomicRole) RoleExpressionConverter_ShortForm(owlSOPOA.getSuperProperty());
			Formula converted = new Inclusion(subrole,superrole);
			RoleNodeMap.get(subrole).addparent(superrole);
			RoleNodeMap.get(superrole).addchild(subrole);
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentObjectPropertiesAxiom) {
			setP(getP() + 1);
			OWLEquivalentObjectPropertiesAxiom owlEOPA = (OWLEquivalentObjectPropertiesAxiom) axiom;
			Collection<OWLSubObjectPropertyOfAxiom> owlSOPOAs = owlEOPA.asSubObjectPropertyOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubObjectPropertyOfAxiom owlSOPOA : owlSOPOAs) {
				converted.addAll(AxiomConverter_ShortForm(owlSOPOA));
			}
			return converted;
			
		} else if (axiom instanceof OWLTransitiveObjectPropertyAxiom) {
			OWLTransitiveObjectPropertyAxiom owlOTOPA = (OWLTransitiveObjectPropertyAxiom) axiom;
			AtomicRole role = (AtomicRole) RoleExpressionConverter_ShortForm(owlOTOPA.getProperty());
			TransitiveRole_Set.add(role);

			List<Formula> converted = Collections.singletonList(new Trans(role));
			return converted;
			//return Collections.emptyList();
			
		} else if (axiom instanceof OWLIrreflexiveObjectPropertyAxiom) {
			OWLIrreflexiveObjectPropertyAxiom owlIROPA = (OWLIrreflexiveObjectPropertyAxiom) axiom;
			IrreflexiveRole_Set.add((AtomicRole) RoleExpressionConverter(owlIROPA.getProperty()));
			return Collections.emptyList();
			
		} */
		/*else if (axiom instanceof OWLClassAssertionAxiom) {
			setQ(getQ() + 1);
			OWLClassAssertionAxiom owlCAA = (OWLClassAssertionAxiom) axiom;
			Formula converted = new Inclusion(IndividualConverter_ShortForm(owlCAA.getIndividual()),
					ClassExpressionConverter_ShortForm(owlCAA.getClassExpression()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLObjectPropertyAssertionAxiom) {
			setR(getR() + 1);
			OWLObjectPropertyAssertionAxiom owlOPAA = (OWLObjectPropertyAssertionAxiom) axiom;
			Formula converted = new Inclusion(IndividualConverter_ShortForm(owlOPAA.getSubject()),
					new Exists(RoleExpressionConverter_ShortForm(owlOPAA.getProperty()),
							IndividualConverter_ShortForm(owlOPAA.getObject())));
			return Collections.singletonList(converted);
			
		}*/ 
		  else {
			setS(getS() + 1);
			//System.out.println("axiom = " + axiom);
		}

		return Collections.emptyList();
	}

	private Formula ClassExpressionConverter(OWLClassExpression concept) {
	
		if (concept.isTopEntity()) {
			return TopConcept.getInstance();

		} else if (concept.isBottomEntity()) {
			return BottomConcept.getInstance();

		} else if (concept instanceof OWLClass) {
			OWLClass owlClass = (OWLClass) concept;
			return new AtomicConcept(owlClass.getIRI().toString());

		} else if (concept instanceof OWLObjectComplementOf) {
			OWLObjectComplementOf owlOCO = (OWLObjectComplementOf) concept;
			return new Negation(ClassExpressionConverter(owlOCO.getOperand()));

		} else if (concept instanceof OWLObjectSomeValuesFrom) {
			OWLObjectSomeValuesFrom owlOSVF = (OWLObjectSomeValuesFrom) concept;
			return new Geq(1,RoleExpressionConverter(owlOSVF.getProperty()),
					ClassExpressionConverter(owlOSVF.getFiller()));

		} else if (concept instanceof OWLObjectAllValuesFrom) {
			OWLObjectAllValuesFrom owlOAVF = (OWLObjectAllValuesFrom) concept;
			return new Leq(0,RoleExpressionConverter(owlOAVF.getProperty()),
					new Negation(ClassExpressionConverter(owlOAVF.getFiller())));

		} else if(concept instanceof OWLObjectMaxCardinality) { 
			OWLObjectMaxCardinality owlMAX = (OWLObjectMaxCardinality) concept;
			return new Leq(owlMAX.getCardinality(),RoleExpressionConverter(owlMAX.getProperty()),
					ClassExpressionConverter(owlMAX.getFiller()));
					
		} else if(concept instanceof OWLObjectMinCardinality) {	
			OWLObjectMinCardinality owlMIN = (OWLObjectMinCardinality) concept;
			return new Geq(owlMIN.getCardinality(),RoleExpressionConverter(owlMIN.getProperty()),
					ClassExpressionConverter(owlMIN.getFiller()));
			
		} else if (concept instanceof OWLObjectIntersectionOf) {
			OWLObjectIntersectionOf owlOIO = (OWLObjectIntersectionOf) concept;
			List<Formula> conjunct_list = new ArrayList<>();
			for (OWLClassExpression conjunct : owlOIO.getOperands()) {
				conjunct_list.add(ClassExpressionConverter(conjunct));
			}
			return new And(conjunct_list);

		} else if (concept instanceof OWLObjectUnionOf) {
			OWLObjectUnionOf owlOUO = (OWLObjectUnionOf) concept;
			List<Formula> disjunct_list = new ArrayList<>();
			for (OWLClassExpression disjunct : owlOUO.getOperands()) {
				disjunct_list.add(ClassExpressionConverter(disjunct));
			}
			return new Or(disjunct_list);
		}

		return TopConcept.getInstance();
	}
	
	private Formula ClassExpressionConverter_ShortForm(OWLClassExpression concept) {
		
		if (concept.isTopEntity()) {
			return TopConcept.getInstance();

		} else if (concept.isBottomEntity()) {
			return BottomConcept.getInstance();

		} else if (concept instanceof OWLClass) {
			OWLClass owlClass = (OWLClass) concept;
			return new AtomicConcept(owlClass.getIRI().getShortForm());

		} else if (concept instanceof OWLObjectComplementOf) {
			OWLObjectComplementOf owlOCO = (OWLObjectComplementOf) concept;
			return new Negation(ClassExpressionConverter_ShortForm(owlOCO.getOperand()));

		} else if (concept instanceof OWLObjectSomeValuesFrom) {
			OWLObjectSomeValuesFrom owlOSVF = (OWLObjectSomeValuesFrom) concept;
			return new Geq(1,RoleExpressionConverter_ShortForm(owlOSVF.getProperty()),
					ClassExpressionConverter_ShortForm(owlOSVF.getFiller()));

		} else if (concept instanceof OWLObjectAllValuesFrom) {
			OWLObjectAllValuesFrom owlOAVF = (OWLObjectAllValuesFrom) concept;
			return new Leq(0,RoleExpressionConverter_ShortForm(owlOAVF.getProperty()),
					new Negation(ClassExpressionConverter_ShortForm(owlOAVF.getFiller())));

		} else if(concept instanceof OWLObjectMaxCardinality) { 
			OWLObjectMaxCardinality owlMAX = (OWLObjectMaxCardinality) concept;
			return new Leq(owlMAX.getCardinality(),RoleExpressionConverter_ShortForm(owlMAX.getProperty()),
					ClassExpressionConverter_ShortForm(owlMAX.getFiller()));
					
		} else if(concept instanceof OWLObjectMinCardinality) {	
			OWLObjectMinCardinality owlMIN = (OWLObjectMinCardinality) concept;
			return new Geq(owlMIN.getCardinality(),RoleExpressionConverter_ShortForm(owlMIN.getProperty()),
					ClassExpressionConverter_ShortForm(owlMIN.getFiller()));
			
		} else if (concept instanceof OWLObjectIntersectionOf) {
			OWLObjectIntersectionOf owlOIO = (OWLObjectIntersectionOf) concept;
			List<Formula> conjunct_list = new ArrayList<>();
			for (OWLClassExpression conjunct : owlOIO.getOperands()) {
				conjunct_list.add(ClassExpressionConverter_ShortForm(conjunct));
			}
			return new And(conjunct_list);

		} else if (concept instanceof OWLObjectUnionOf) {
			OWLObjectUnionOf owlOUO = (OWLObjectUnionOf) concept;
			List<Formula> disjunct_list = new ArrayList<>();
			for (OWLClassExpression disjunct : owlOUO.getOperands()) {
				disjunct_list.add(ClassExpressionConverter_ShortForm(disjunct));
			}
			return new Or(disjunct_list);
		} 

		return TopConcept.getInstance();
	}
	
	private RoleExpression RoleExpressionConverter(OWLObjectPropertyExpression role) {

		if (role.isTopEntity()) {
			return TopRole.getInstance();
			
		} else if (role.isBottomEntity()) {
			return BottomRole.getInstance();
			
		} else if (role instanceof OWLObjectProperty) {
			OWLObjectProperty owlOP = (OWLObjectProperty) role;
			return new AtomicRole(owlOP.getIRI().toString());
			
		}

		return TopRole.getInstance();
	}
	
	private RoleExpression RoleExpressionConverter_ShortForm(OWLObjectPropertyExpression role) {

		if (role.isTopEntity()) {
			return TopRole.getInstance();
			
		} else if (role.isBottomEntity()) {
			return BottomRole.getInstance();
			
		} else if (role instanceof OWLObjectProperty) {
			OWLObjectProperty owlOP = (OWLObjectProperty) role;
			return new AtomicRole(owlOP.getIRI().getShortForm());
			
		}

		return TopRole.getInstance();
	}
	
	private ConceptExpression IndividualConverter(OWLIndividual indi) {

		if (indi instanceof OWLNamedIndividual) {
			OWLNamedIndividual owlIndi = (OWLNamedIndividual) indi;
			return new Individual(owlIndi.getIRI().toString());
			
		}

		return TopConcept.getInstance();
	}
	
	private ConceptExpression IndividualConverter_ShortForm(OWLIndividual indi) {

		if (indi instanceof OWLNamedIndividual) {
			OWLNamedIndividual owlIndi = (OWLNamedIndividual) indi;
			return new Individual(owlIndi.getIRI().getShortForm());
			
		}

		return TopConcept.getInstance();
	}

	public static int getI() {
		return i;
	}

	public void setI(int i) {
		Converter.i = i;
	}

	public static int getJ() {
		return j;
	}

	public void setJ(int j) {
		Converter.j = j;
	}

	public static int getL() {
		return l;
	}

	public void setL(int l) {
		Converter.l = l;
	}

	public static int getM() {
		return m;
	}

	public void setM(int m) {
		Converter.m = m;
	}

	public static int getK() {
		return k;
	}

	public void setK(int k) {
		Converter.k = k;
	}

	public static int getN() {
		return n;
	}

	public void setN(int n) {
		Converter.n = n;
	}

	public static int getO() {
		return o;
	}

	public void setO(int o) {
		Converter.o = o;
	}

	public static int getP() {
		return p;
	}

	public void setP(int p) {
		Converter.p = p;
	}

	public static int getQ() {
		return q;
	}

	public void setQ(int q) {
		Converter.q = q;
	}

	public static int getR() {
		return r;
	}

	public void setR(int r) {
		Converter.r = r;
	}

	public static int getS() {
		return s;
	}

	public void setS(int s) {
		Converter.s = s;
	}

}
