package evaluation;

import convertion.Converter;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.model.*;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;


import java.io.File;
import java.util.Set;

public class Anno {
    public static void main(String[] args) throws OWLOntologyCreationException {

        //String path = "/Users/yue_x/Desktop/dataset/Corpus_3";
        String path = "/Users/yue_x/Desktop/TestCase";
        File file = new File(path);


        File[] fs = file.listFiles();
        int i =1;
        for (File f : fs) {

            System.out.println(i++);
            if (!f.isDirectory() && f.getName().endsWith("owl")){
                OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

                IRI iri = IRI.create(f);
                OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
                        new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(true));
                Converter ct = new Converter();
                Set<OWLAxiom> owlAxiomSet = ontology.getAxioms();
                Set<OWLClass> owlClassSet = ontology.getClassesInSignature();
                Set<OWLObjectProperty> owlObjectPropertiesSet = ontology.getObjectPropertiesInSignature();

                for (OWLAxiom a : owlAxiomSet){
                    if ( a.isAnnotationAxiom() || a.isAnnotated()) {
                        System.out.println("1");
                        Set<OWLAnnotation> c = a.getAnnotations();
                    }
                }

                Set<OWLAnnotationAssertionAxiom> annoset;
                /*
                for (OWLObjectProperty a:owlObjectPropertiesSet){
                    annoset.addAll(a.getAnnotationAssertionAxioms());
                }*/

            }
        }
    }
    /*
    private static void extract_annotations(OWLOntology ont) throws IOException {
        List<String> ann_axioms = new ArrayList<>();

        for (OWLEntity e : ont.getSignature()) {
            for (OWLAnnotation a : EntitySearcher.getAnnotations(e, ont)) {
                OWLAnnotationProperty prop = a.getProperty();
                OWLAnnotationValue val = a.getValue();
                if (val instanceof OWLLiteral) {
                    OWLLiteral lit = (OWLLiteral) val;
                    if ((lit.hasLang() && lit.hasLang("en")) || !lit.hasLang()) {
                        String property_str = prop.getIRI().toString();
                        String e_str = e.getIRI().toString();
                        ann_axioms.add((e_str.replaceAll("\n", " ") + " " +
                                property_str.replaceAll("\n", " ") + " " +
                                ((OWLLiteral) val).getLiteral()).replaceAll("\n", " "));
                    }
                }
            }
        }
        save_annotations(ann_axioms);
    }*/
}
