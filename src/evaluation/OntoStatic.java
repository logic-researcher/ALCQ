package evaluation;



import java.io.File;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import connectives.*;
import convertion.BackConverter;
import extraction.SubsetExtractor;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.model.*;


import concepts.AtomicConcept;
import convertion.Converter;
import inference.DefinerIntroducer;
import roles.AtomicRole;
import forgetting.Forgetter;

import forgetting.Fame;
import formula.Formula;

public class OntoStatic {

    public static void main(String[] args) throws OWLOntologyCreationException, InterruptedException, ExecutionException {
        //  指定log文件
        String logpath = "/Users/yue_x/Desktop/OntoStatic.txt";
        //  指定写入的属性
        String features = "OntologyName, AxiomSize, ConceptSize, RoleSize, depth\n";
        // 指定ontology的路径
        String ontologyPath = "/Users/yue_x/Desktop/科研/IJCAI2021/Data/NCBO BioPortal/owlxml";
        WriteFile.writeFile(logpath,features);

        File ontopath = new File(ontologyPath);
        File[] files = ontopath.listFiles();
        int i = 1;
        for (File file :files){
            System.out.println(i++);
            String filename = file.getName();
            if (!file.isDirectory() && filename.endsWith("xml")){
                System.out.println(filename);
                WriteFile.writeFile(logpath,analysisOnto(file));
            }
        }

    }


    public static String analysisOnto(File file) throws OWLOntologyCreationException, InterruptedException, ExecutionException{
        OWLOntologyManager manager=OWLManager.createOWLOntologyManager();
        IRI iri = IRI.create(file);
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
                new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(true));
        Converter ct=new Converter();
        List<AtomicRole> roleList = ct.getRolesInSignature_ShortForm(ontology);
        List<AtomicConcept> conceptList = ct.getConceptsInSignature_ShortForm(ontology);

        int LogicalAxiomSize=ontology.getLogicalAxiomCount();
        int ConceptSize=conceptList.size();
        int RoleSize=roleList.size();
        int success_num=0;
        int depth = 0;
        List<Formula> formula_list = ct.OntologyConverter_ShortForm(ontology);
        for(Formula formula : formula_list){
            depth += get_depth(formula);
        }
        String log = file.getName()+","+LogicalAxiomSize+","+ConceptSize+","+RoleSize+","+depth+"\n";
        return log;
    }

    public static int get_depth(Formula formula){
        int depth=0;
        if (formula instanceof Negation) {
            return get_depth(formula.getSubFormulas().get(0));

        } else if (formula instanceof Geq || formula instanceof Leq) {
            return 1 + get_depth(formula.getSubFormulas().get(1));

        } else if (formula instanceof Inclusion) {
            return get_depth(formula.getSubFormulas().get(0)) + get_depth(formula.getSubFormulas().get(1));

        } else if (formula instanceof And || formula instanceof Or) {
            List<Formula> operand_list = formula.getSubFormulas();
            for (Formula operand : operand_list) {
                depth += get_depth(operand);
            }
            return depth;
        }
        return 0;
    }

}

