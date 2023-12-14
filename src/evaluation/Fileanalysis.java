package evaluation;

import convertion.Converter;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.util.Set;

public class Fileanalysis {
    public static void main(String[] args) throws OWLOntologyCreationException {

        //String path = "/Users/yue_x/Desktop/dataset/Corpus_3";
        String path = "/home/yue_x/Desktop/NCBO BioPortal/owlxml";
        String path1 = "/home/yue_x/Desktop/testOnto";
        File file = new File(path);


        File[] fs = file.listFiles();
        int i =1;
        for (File f : fs) {
            if (f.getName().startsWith("aura") || f.getName().startsWith("flopo")){
                continue;
            }
            try {
                System.out.println(f.getName());
                if (!f.isDirectory() && f.getName().endsWith("xml")) {
                    OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

                    IRI iri = IRI.create(f);
                    OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
                            new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(true));
                    OWLReasoner Dreasoner = new Reasoner.ReasonerFactory().createReasoner(ontology);
                    Converter ct = new Converter();
                    if (ontology.getLogicalAxiomCount() <= 100000) {
                        Set<OWLAxiom> owlAxiom_set = ontology.getAxioms();
                        int flag1 = 0;
                        int flag2 = 0;
                        for (OWLAxiom axiom : owlAxiom_set) {
                            if (axiom instanceof OWLTransitiveObjectPropertyAxiom) {

                                flag1 = 1;
                            }
                            if (axiom instanceof OWLObjectMaxCardinality || axiom instanceof OWLObjectMinCardinality) {
                                flag2 = 1;
                            }
                            //if (ontology.getObjectPropertiesInSignature().size() >= 100 && Dreasoner.isConsistent()) {
                            if (flag1 == 1 && Dreasoner.isConsistent()){
                                String srcpath = path + File.separator + f.getName();
                                String despath = path1 + File.separator + f.getName();
                                copy(srcpath, despath);
                                break;
                            }
                        }
                    }
                    f.delete();
                }
            } catch (Exception e){
                continue;
            }
        }
    }

    static void copy(String srcPathStr, String desPathStr)
    {


        try
        {
            FileInputStream fis = new FileInputStream(srcPathStr);//创建输入流对象
            FileOutputStream fos = new FileOutputStream(desPathStr); //创建输出流对象
            byte datas[] = new byte[1024*8];//创建搬运工具
            int len = 0;//创建长度
            while((len = fis.read(datas))!=-1)//循环读取数据
            {
                fos.write(datas,0,len);
            }
            fis.close();//释放资源
            fis.close();//释放资源
        }
        catch (Exception e)
        {
            e.printStackTrace();
        }
    }
}
