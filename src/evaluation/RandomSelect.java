package evaluation;

import org.semanticweb.owlapi.model.OWLEntity;

import java.util.*;

public class RandomSelect {
	public RandomSelect() {
		
	}
	
	public <T> Set<T> getrandomList(List<T> inputlist,int percent){
		int num=inputlist.size()*percent/100;
		//int num=percent;
		Collections.shuffle(inputlist);
		Set<T> output=new HashSet<>();
		for(int i=0;i<num;i++) {
			output.add(inputlist.get(i));
		}
		return output;
	}

	/*
	public <T> Set<T> getrandomSet(Set<T> inputset,int percent){
		int num = inputset.size()*percent/100;
		@SuppressWarnings("unchecked")
		List<T> inputlist = (List<T>) inputset;
		Collections.shuffle(inputlist);
		Set<T> output=new HashSet<>();
		for(int i=0;i<num;i++) {
			output.add(inputlist.get(i));
		}
		return output;
	}*/

	public  <T> Set<T> getrandomSet(Set<T> inputset, int percent){
		int num = inputset.size()*percent/100;

		List<T> inputlist = new ArrayList<>() ;
		for (T aa : inputset) {
			inputlist.add(aa);
		}
		Collections.shuffle(inputlist);
		Set<T> output=new HashSet<>();
		for(int i=0;i<num;i++) {
			output.add(inputlist.get(i));
		}
		return output;
	}
}
