package evaluation;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import convertion.BackConverter;
import extraction.SubsetExtractor;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.io.OWLXMLOntologyFormat;
import org.semanticweb.owlapi.model.*;

import uk.ac.man.cs.lethe.forgetting.IOWLForgetter;
import uk.ac.man.cs.lethe.forgetting.ShqTBoxForgetter;
import uk.ac.man.cs.lethe.interpolation.ShqTBoxInterpolator;

import concepts.AtomicConcept;
import convertion.Converter;
import inference.DefinerIntroducer;
import roles.AtomicRole;
import forgetting.Forgetter;

import forgetting.Fame;
import formula.Formula;


public class mainTest {
    public static long LETHERuntime=0;
    public static int LETHEisSuccess=0;
    public static int LETHECyclic=0;
    public static long MyRuntime=0;
    public static int MyisSuccess=0;
    public static int MyCyclic=0;
    public static int definernum=0;
    public static int percent = 0;

    public static void main(String args[]) throws OWLOntologyCreationException, InterruptedException, ExecutionException {
        //  Set the log file path. The experimental data will be saved in this file path.
        String logpath ="";

        // Set the save path of UI that computed by LETHE. The output of LETHE will be saved in this file path.
        String LETHEPATH = "";

        // Set the save path of UI that computed by our tool. The output of our tool will be saved in this file path.
        String MyPATH = "";

        // Set the path of test data.
        String ontologyPath = "";

        // Set the number of signatures the be eliminate.
        percent = 30;

        //  Metrics
        //String features = "OntologyName, MyisSuccess, MyCyclic, Myruntime, definernum, LETHEissuccess, LETHECyclic, LETHERuntime\n";

        //WriteFile.writeFile(logpath,features);

        File ontopath = new File(ontologyPath);
        File[] files = ontopath.listFiles();
        int i = 1;
        for (File file :files){

            String filename = file.getName();
            System.out.println(filename);
            if (!file.isDirectory() && (filename.endsWith("xml") || filename.endsWith("owl"))){
                MetricReset();
                evaluation(file,LETHEPATH+filename,MyPATH+filename);
            }
            String log = file.getName()+"," + MyisSuccess +", "+ MyCyclic + ", "+ MyRuntime +", " + definernum +", " + LETHEisSuccess +", " + LETHECyclic +", " + LETHERuntime + "\n";
            WriteFile.writeFile(logpath,log);
            file.delete();
        }


    }

    public static void evaluation(File file, String LETHEPATH, String MyPATH) throws OWLOntologyCreationException, InterruptedException, ExecutionException {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        RandomSelect rs = new RandomSelect();
        Converter ct = new Converter();
        IRI iri = IRI.create(file);
        OWLOntology inputontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
                new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(true));



        Set<OWLClass> names = inputontology.getClassesInSignature();
        Set<OWLClass> classes = rs.getrandomSet(names, percent);


        // My prototype forget
        Callable<Void> Prototypetask =new Callable<Void>() {
            public Void call() throws Exception{
                PrototypeForget(inputontology,classes,MyPATH);
                return null;
            }
        };
        ExecutorService PexecutorService=Executors.newSingleThreadScheduledExecutor();
        Future<Void> Prototypefuture=PexecutorService.submit(Prototypetask);
        try {
            Long MStartime = System.currentTimeMillis();
            Prototypefuture.get(300,TimeUnit.SECONDS);
            Long MEndTime = System.currentTimeMillis();
            MyisSuccess = 1;
            definernum = AtomicConcept.getTotal_index();
            MyRuntime = MEndTime - MStartime;
        } catch(TimeoutException e) {
            MyisSuccess = 0;
            definernum = AtomicConcept.getTotal_index();

        } catch(IllegalArgumentException e){
            MyisSuccess=0;
            MyRuntime=0;
        }
        //  LETHE forget
        Callable<Void> LETHEtask =new Callable<Void>() {
            public Void call() throws Exception{
                LETHEForget(inputontology,classes,LETHEPATH);
                return null;
            }
        };
        ExecutorService LexecutorService=Executors.newSingleThreadScheduledExecutor();
        Future<Void> LETHEfuture=LexecutorService.submit(LETHEtask);
        try {
            Long starttime = System.currentTimeMillis();
            LETHEfuture.get(300,TimeUnit.SECONDS);
            Long endTime = System.currentTimeMillis();
            LETHERuntime = endTime - starttime;
            LETHEisSuccess = 1;

        } catch(TimeoutException e) {
            LETHEisSuccess = 0;

        }





    }

    public static OWLOntology LETHEForget(OWLOntology onto, Set<OWLClass> pivotList, String save_path) throws OWLOntologyStorageException, FileNotFoundException {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        ShqTBoxForgetter forgetter = new ShqTBoxForgetter();
        Set<OWLEntity> pivotlist = new HashSet<>(pivotList);
        OWLOntology resultontology = forgetter.forget(onto, pivotlist);
        File out_file = new File(save_path);
        OutputStream os = new FileOutputStream(out_file);
        manager.saveOntology(resultontology, new OWLXMLOntologyFormat(), os);
        long EndTime = System.currentTimeMillis();
        Set<OWLClass> concepts = resultontology.getClassesInSignature();
        for (OWLClass concept : concepts) {
            if (concept.getIRI().getShortForm().startsWith("_D")){
                System.out.println(concept.getIRI().getShortForm());
                LETHECyclic = 1;
                break;
            }
        }
        return resultontology;
    }

    public  static OWLOntology PrototypeForget(OWLOntology onto, Set<OWLClass> pivotList, String save_path) throws OWLOntologyCreationException, CloneNotSupportedException, OWLOntologyStorageException, FileNotFoundException {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        Converter ct=new Converter();
        ct.CReset();

        List<AtomicRole> roleList = ct.getRolesInSignature(onto);
        List<AtomicConcept> concepts = ct.getConceptsInSignature(onto);
        BackConverter bc = new BackConverter();
        Fame fame=new Fame();
        Set<AtomicConcept> mypivotlist = new HashSet<>();
        for (OWLClass pivot: pivotList){
            mypivotlist.add(ct.getConceptfromClass(pivot));
        }
        List<Formula> formula_list = ct.OntologyConverter(onto);
        List<Formula> result_list = fame.FameCR(mypivotlist, new HashSet<>(), formula_list);
        OWLOntology o = bc.toOWLOntology(result_list);
        File out_file = new File(save_path);
        OutputStream os = new FileOutputStream(out_file);
        manager.saveOntology(o, new OWLXMLOntologyFormat(), os);
        return o;

    }

    public static void MetricReset(){
        LETHEisSuccess = 0;
        LETHERuntime = 0;
        LETHECyclic = 0;
        MyCyclic = 0;
        MyisSuccess = 0;
        MyRuntime = 0;
        definernum = 0;
        AtomicConcept.resetTotal_index();

    }


}
