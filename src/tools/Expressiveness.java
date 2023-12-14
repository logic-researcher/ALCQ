package tools;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.model.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Set;

public class Expressiveness {
    private static boolean isWithQ(Set<OWLLogicalAxiom> axioms) {
        for (OWLLogicalAxiom axiom : axioms) {
            if (isWithQ(axiom)) {
                return true;
            }
        }
        return false;
    }

    private static boolean isWithQ(OWLLogicalAxiom axiom) {
        if (axiom instanceof OWLSubClassOfAxiom) {
            OWLSubClassOfAxiom subClassOfAxiom = (OWLSubClassOfAxiom) axiom;
            OWLClassExpression subClass = subClassOfAxiom.getSubClass();
            OWLClassExpression superClass = subClassOfAxiom.getSuperClass();
            return isWithQ(subClass) || isWithQ(superClass);
        } else if (axiom instanceof OWLEquivalentClassesAxiom) {
            OWLEquivalentClassesAxiom equivalentClassesAxiom = (OWLEquivalentClassesAxiom) axiom;
            Set<OWLSubClassOfAxiom> subClassOfAxioms = equivalentClassesAxiom.asOWLSubClassOfAxioms();
            for (OWLSubClassOfAxiom subClassOfAxiom : subClassOfAxioms) {
                if (isWithQ(subClassOfAxiom)) {
                    return true;
                }
            }
            return false;
        } else if (axiom instanceof OWLDisjointClassesAxiom) {
            OWLDisjointClassesAxiom disjointClassesAxiom = (OWLDisjointClassesAxiom) axiom;
            Set<OWLSubClassOfAxiom> subClassOfAxioms = disjointClassesAxiom.asOWLSubClassOfAxioms();
            for (OWLSubClassOfAxiom subClassOfAxiom : subClassOfAxioms) {
                if (isWithQ(subClassOfAxiom)) {
                    return true;
                }
            }
            return false;
        } else if (axiom instanceof OWLDisjointUnionAxiom) {
            OWLDisjointUnionAxiom disjointUnionAxiom = (OWLDisjointUnionAxiom) axiom;
            Set<OWLClassExpression> classExpressions = disjointUnionAxiom.getClassExpressions();
            for (OWLClassExpression classExpression : classExpressions) {
                if (isWithQ(classExpression)) {
                    return true;
                }
            }
            return false;
        }
        return false;
    }

    private static boolean isWithQ(OWLClassExpression conceptExp) {
        if (conceptExp instanceof OWLClass) {
            return false;
        } else if (conceptExp instanceof OWLObjectComplementOf) {
            return isWithQ(((OWLObjectComplementOf) conceptExp).getOperand());
        } else if (conceptExp instanceof OWLObjectSomeValuesFrom) {
            return false;
        } else if (conceptExp instanceof OWLObjectAllValuesFrom) {
            return false;
        } else if (conceptExp instanceof OWLObjectIntersectionOf) {
            for (OWLClassExpression operand : ((OWLObjectIntersectionOf) conceptExp).getOperands()) {
                if (isWithQ(operand)) {
                    return true;
                }
            }
            return false;
        } else if (conceptExp instanceof OWLObjectUnionOf) {
            for (OWLClassExpression operand : ((OWLObjectUnionOf) conceptExp).getOperands()) {
                if (isWithQ(operand)) {
                    return true;
                }
            }
            return false;
        } else if (conceptExp instanceof OWLObjectMinCardinality) {
            OWLObjectMinCardinality minCardinality = (OWLObjectMinCardinality) conceptExp;
            if (minCardinality.getCardinality() == 1) {
                return false;
            } else {
                return true;
            }
        } else if (conceptExp instanceof OWLObjectMaxCardinality) {
            OWLObjectMaxCardinality maxCardinality = (OWLObjectMaxCardinality) conceptExp;
            if (maxCardinality.getCardinality() == 0) {
                return false;
            } else {
                return true;
            }
        } else return conceptExp instanceof OWLObjectExactCardinality;
    }

    private static boolean isWithQ(String filePath) throws OWLOntologyCreationException {
        OWLOntology ontology = loadOntology(filePath);
        Set<OWLLogicalAxiom> axioms = ontology.getLogicalAxioms();
        return isWithQ(axioms);
    }

    public static OWLOntology loadOntology(String filePath) throws OWLOntologyCreationException {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        IRI iri = IRI.create(new File(filePath));
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
                new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(false));
        return ontology;
    }

    public static void main(String[] args) throws OWLOntologyCreationException, IOException {
        String basePath = "/Users/wangsen/Downloads/test_forgetting/";
        String[] datasets = {"BioPortal", "Oxford-ISG"};
        for (String dataset : datasets) {
            int maxSize = 0;
            File directory = new File(basePath + dataset);
            File[] files = directory.listFiles();
            FileWriter fileWriter = new FileWriter(dataset + ".txt");
            BufferedWriter bufferedWriter = new BufferedWriter(fileWriter);
            for (File file : files) {
                if (!file.isDirectory()) { continue; }
                String filePath = file.getAbsolutePath();
                File directory2 = new File(filePath);
                File[] files2 = directory2.listFiles();
                for (File file2 : files2) {
                    String fileName = file2.getName();
                    if (fileName.endsWith(".xml") || fileName.endsWith(".owl")) {
//                        if (isWithQ(filePath + "/" +fileName)) {
//                            bufferedWriter.write(fileName + "\n");
//                        }
                        maxSize = Math.max(maxSize, getOntologySize(filePath + "/" +fileName));
                    }
                }
            }
            System.out.println(dataset + ": " + maxSize);
            bufferedWriter.close();
            fileWriter.close();

        }

    }

    public static int getOntologySize(String filePath) throws OWLOntologyCreationException {
        OWLOntology ontology = loadOntology(filePath);
        return ontology.getLogicalAxiomCount();
    }
}
