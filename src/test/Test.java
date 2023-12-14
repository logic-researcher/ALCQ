package test;

import concepts.AtomicConcept;
import convertion.Converter;
import forgetting.Fame;
import forgetting.Forgetter;
import formula.Formula;
import org.apache.commons.collections4.ListUtils;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.model.*;
import roles.AtomicRole;
import Exception.CyclicCaseException;

import java.io.File;
import java.util.*;

public class Test {

    public static void main(String[] args) throws OWLOntologyCreationException, CyclicCaseException, CloneNotSupportedException {
        String onto_path = "/Users/wangsen/JavaProject/ALCQ/test.owl";
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        IRI iri = IRI.create(new File(onto_path));
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
                new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(false));
        Converter ct = new Converter();
        List<Formula> formulaList = ct.OntologyConverter_ShortForm(ontology);
        List<AtomicRole> roleList = new ArrayList<>();
        ct.getConceptsInSignature_ShortForm(ontology);
        List<AtomicConcept> conceptList = ct.getConceptsInSignature_ShortForm(ontology);
        conceptList = Collections.singletonList(new AtomicConcept("A"));
        Fame fame = new Fame();

        List<Formula> forgetting_result = fame.FameCR(new HashSet<>(conceptList), new HashSet<>(roleList), formulaList);

    }
}
