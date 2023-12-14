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

import checkfrequency.FChecker;
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
import java.lang.Runtime;
import Exception.CyclicCaseException;

import forgetting.Fame;
import formula.Formula;
import roles.TopRole;

public class ForgetMine {
	public static String filename = "";
	public static int RoleSize = 0;
	public static int ConceptSize = 0;
	public static int LogicalAxiomSize = 0;
	public static int FConceptSize = 0;
	public static int FRoleSize = 0;
	public static int FLogicAxiomSize = 0;
	public static int isCyclic = 0;
	public static int runtime = 0;
	public static long memory = 0;
	public static double SuccessRate = 0;
	public static int OutofMem = 0;
	public static int CyclicCase = 0;
	public static int OutofTime = 0;
	public static int RoleRestrictionNum = 0;
	public static int DefinerNum = 0;
	public static int formula_size1 = 0;
	public static int formula_size2 = 0;
	public static int max_size = 0;
	public static int formula_size3 = 0;




	public ForgetMine() {
		
	}
	
	public static void Evaluation(File file,String logpath) throws OWLOntologyCreationException, InterruptedException, ExecutionException, CyclicCaseException {
		OWLOntologyManager manager=OWLManager.createOWLOntologyManager();
		IRI iri = IRI.create(file);
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
				new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(true));
		Converter ct=new Converter();
		ct.CReset();
		Fame fame=new Fame();
		RandomSelect rs=new RandomSelect();
		List<AtomicRole> roleList = ct.getRolesInSignature_ShortForm(ontology);
		List<AtomicConcept> conceptList = ct.getConceptsInSignature_ShortForm(ontology);
		LogicalAxiomSize=ontology.getLogicalAxiomCount();
		ConceptSize=conceptList.size();
		RoleSize=roleList.size();
		int success_num=0;
		OutofMem = 0;
		OutofTime = 0;
		runtime = 0;
		memory = 0;
		isCyclic = 0;
		CyclicCase = 0;
		FConceptSize = 0;
		FRoleSize = 0;
		FLogicAxiomSize = 0;
		RoleRestrictionNum = 0;
		DefinerNum = 0;
		max_size = LogicalAxiomSize;

		for (int i=1;i<=10;i++) {
			formula_size1 = 0;
			formula_size2 = 0;
			AtomicConcept.resetTotal_index();
			isCyclic = 0;
			System.out.println(i);
			Runtime r = Runtime.getRuntime();
			long mem1 = r.freeMemory();
			Callable<Void> task = () -> {
				ForgetOne(conceptList,roleList,ontology);
				return null;
			};
			ExecutorService executorService=Executors.newSingleThreadScheduledExecutor();
			Future<Void> future=executorService.submit(task);
			try {
				long startTime = System.currentTimeMillis();
				future.get(100,TimeUnit.SECONDS);
				long endTime = System.currentTimeMillis();
				if (isCyclic==1){
					CyclicCase++;
				} else {
					success_num++;
					long mem2 = r.freeMemory();
					memory += mem1- mem2;
					runtime += endTime - startTime;
				}
			} catch(TimeoutException e) {
				OutofTime++;
				System.gc();
				continue;
			} catch(OutOfMemoryError e) {
				OutofMem++;
				System.gc();
				continue;
			}


			
		}
		memory = memory/1024/1024;
		SuccessRate = success_num;
		runtime = runtime;
		String log = filename+","+LogicalAxiomSize+","+ConceptSize+","+RoleSize+","+SuccessRate+","+OutofMem+
				","+CyclicCase+","+OutofTime+","+runtime+","+memory+","+FLogicAxiomSize+","+FConceptSize+","+FRoleSize+","+RoleRestrictionNum+","+DefinerNum+","+max_size+"\n";
		WriteFile.writeFile(logpath,log);


	}
	
	public static void ForgetOne(List<AtomicConcept> conceptList,List<AtomicRole> roleList,OWLOntology ontology) throws OWLOntologyCreationException, CloneNotSupportedException, CyclicCaseException {

		RandomSelect rs=new RandomSelect();
		Converter ct=new Converter();
		BackConverter bc = new BackConverter();
		FChecker fc = new FChecker();
		SubsetExtractor se = new SubsetExtractor();
		Fame fame=new Fame();
		int c_percent = 10;   // Set the value of this variable to determine the ratio of concept names to be forgotten.
		int r_percent = 0;    // Set the value of this variable to determine the ratio of role names to be forgotten.
		Set<AtomicConcept> c_sig=rs.getrandomList(conceptList, c_percent);   
		Set<AtomicRole> r_sig=rs.getrandomList(roleList, r_percent);
		OWLOntology o = null;
		
		try {
			List<Formula> formula_list = ct.OntologyConverter_ShortForm(ontology);
			System.out.println(formula_list.size());
			List<Formula> result_list = fame.FameCR(c_sig, r_sig, formula_list);
			o = bc.toOWLOntology(result_list);
			if(isCyclic==0){
				FConceptSize += o.getClassesInSignature().size();
				FRoleSize += o.getObjectPropertiesInSignature().size();
				FLogicAxiomSize += o.getLogicalAxiomCount();
				DefinerNum += AtomicConcept.getTotal_index();
				RoleRestrictionNum = fc.getRestrictionNum(formula_list);
			}
			//System.out.println();		
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			//e.printStackTrace();
		}

	}

	public static void updateMax(){
		if (formula_size1+formula_size2+formula_size3>max_size){
			max_size = formula_size1+formula_size2+formula_size3;
		}
	}

	public static void main(String[] args) throws OWLOntologyCreationException, InterruptedException, ExecutionException, CyclicCaseException {
		String logpath = "/Users/yue_x/Desktop/ProtoLogForget_2.txt";
		String features = "OntologyName,AxiomSize,ConceptSize,RoleSize,SuccessRate,OutofMem,CyclicCase,OutofTime,Runtime,Memory,FAxiomSize,FConceptSize,FRoleSize,RoleRestrictionNum,DefinerNum,max_size\n";
		//WriteFile.writeFile(logpath,features);
		String ontologyPath = "/Users/yue_x/Desktop/TestData";
		File ontopath = new File(ontologyPath);
		File[] files = ontopath.listFiles();
		int i = 1;
		for (File file : files){
			System.out.println(i++);
			filename = file.getName();
			System.out.println(filename);
			if (!file.isDirectory() && filename.endsWith("xml")){
				Evaluation(file,logpath);
				if(SuccessRate!=10){
					File newFile = new File("/Users/yue_x/Desktop/FailCase/"+file.getName());
					file.renameTo(newFile);
				} else {
					file.delete();
				}
			}
		}

	}

}
