package evaluation;
import formula.Formula;
import inference.Inferencer;

import roles.AtomicRole;
import concepts.AtomicConcept;
import connectives.Or;

import java.util.ArrayList;
import java.util.List;


public class test {
    public static void main(String[] args){
        List<Formula> inputlist = new ArrayList<>();
        inputlist.add(new AtomicRole("a"));
        inputlist.add(new AtomicRole("b"));
        inputlist.add(new AtomicRole("c"));
        inputlist.add(new AtomicRole("d"));
        Inferencer inf = new Inferencer();
        List<List<Formula>> out = inf.getCombinations(inputlist);
        int a =1;
    }
}
