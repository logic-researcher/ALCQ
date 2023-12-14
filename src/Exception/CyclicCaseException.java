package Exception;
import formula.Formula;

public class CyclicCaseException extends Exception{
    public CyclicCaseException(){
    }

    public CyclicCaseException(Formula formula){
        super();
        System.out.println(formula);
    }
}
