package concepts;

import org.apache.commons.lang3.builder.HashCodeBuilder;

/**
 * @author Yizheng
 */
public class AtomicConcept extends ConceptExpression implements Comparable<AtomicConcept> {
		
	private static int definer_index = 1;
	private static int cyclic_definer_index = 1;
	private static int total_index = 0;
		
	public AtomicConcept() {
		super();
	}

	public AtomicConcept(String str) {
		super(str);
	}

	@Override
	public String toString() {
		return this.getText();
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getText()).toHashCode();
	}

	@Override
	public int compareTo(AtomicConcept concept) {
		int i = this.getText().compareTo(concept.getText());
		return i;
	}

	public static int getDefiner_index() {
		return definer_index;
	}

	public static int getCyclic_definer_index() {
		return cyclic_definer_index;
	}

	public static void setDefiner_index(int definer_index) {
		AtomicConcept.definer_index = definer_index;
	}

	public static void setCyclic_definer_index(int definer_index) {
		AtomicConcept.cyclic_definer_index = definer_index;
	}

	public static int getTotal_index(){
		return total_index;
	}

	public static void resetTotal_index(){
		AtomicConcept.total_index = 0;
	}

	public static void update_total_index(){
		AtomicConcept.total_index += AtomicConcept.definer_index-1;
	}
}
