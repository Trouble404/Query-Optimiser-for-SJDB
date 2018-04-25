package sjdb;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class Estimator implements PlanVisitor {
	
	private int totalCost = 0;
	
	public Estimator() {
		// empty constructor
	}

	/* Scan
	 * Create output relation on Scan operator
	 *
	 * Example implementation of visit method for Scan operators.
	 */
	public void visit(Scan op) {
		Relation input = op.getRelation(); // the named relation to be scanned
		Relation output = new Relation(input.getTupleCount()); // the tuple count for this relation
		
		Iterator<Attribute> iter = input.getAttributes().iterator(); //only the name of the attribute is significant
		while (iter.hasNext()) { // True if the iteration has more elements
			Attribute attr = iter.next();
			output.addAttribute(new Attribute(attr)); // add attribute to local record
		}
		
		op.setOutput(output);
		totalCost += output.getTupleCount();
	}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	/* Projection
	 * T(πA(R)) = T(R)
	 *
	 * Assume that projection does not eliminate duplicate tuples
	 */
	public void visit(Project op) {
		
		// Obtain output relation from given input relation
		Relation input;
		Relation output;
		input = op.getInput().getOutput(); // Return the single child operator of this operator, Return the relation produced by this operator as output
		output = new Relation(input.getTupleCount()); // Return the tuple count for this relation

		// Add an attribute to this relation when the list of attributes contained in this relation is equal to the attributes projected by this operator
		for(Attribute attribute1 : op.getAttributes()){ // Return the list of attributes projected by this operator
			for (Attribute attribute2 : input.getAttributes()) { // Return the list of attributes contained in this relation
				if (attribute1.equals(attribute2)) { 
					output.addAttribute(new Attribute(attribute2.getName(), attribute2.getValueCount()));
				}
			}
		}
		
		// Set the relation produced by this operator as output.
		op.setOutput(output); 
		totalCost += output.getTupleCount();
	}
	
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	/* Selection
	 * For predicates of the form attr=val:
	 * T(σA=c(R)) = T(R)/V(R,A), V(σA=c(R), A) = 1
	 *
	 * For predicates of the form attr=attr:
	 * T(σA=B(R)) = T(R)/max(V(R,A),V(R,B)), V(σA=B(R), A) = V(σA=B(R), B) = min(V(R, A), V(R, B)
	 */
	public void visit(Select op) {
		
		Relation input;
		Relation output;
		Predicate predicate;
		Attribute left;
		Attribute right;
		int left_val;
		int right_val;
		int val_count;
		
		left = null;
		right = null;

		predicate = op.getPredicate();

		input = op.getInput().getOutput();
		left = input.getAttribute(predicate.getLeftAttribute());
		left_val = left.getValueCount();
		
		
		/*For predicates of the form attr=val:*/
		if(predicate.equalsValue()) {
			
			int Tr; 
			int Vr;
			Tr = input.getTupleCount();
			Vr = left_val;

			output = new Relation(Tr/Vr); // T(σA=c(R)) = T(R)/V(R,A)
			val_count = 1; // V(σA=c(R), A) = 1

		/* For predicates of the form attr=attr: */
		} else {
			right = input.getAttribute(predicate.getRightAttribute());
			right_val = right.getValueCount();

			// T(σA=B(R)) = T(R)/max(V(R,A),V(R,B)), V(σA=B(R), A) = V(σA=B(R), B) = min(V(R, A), V(R, B)
			int Tr;
			int Vr_max;
			int Vr_min;

			Tr = input.getTupleCount();
			Vr_max = Math.max(left_val, right_val);
			Vr_min = Math.min(left_val, right_val);

			output = new Relation(Tr/Vr_max); // T(σA=B(R)) = T(R)/max(V(R,A),V(R,B))
			val_count = Vr_min; // V(σA=B(R), A) = V(σA=B(R), B) = min(V(R, A), V(R, B)
		}
		
		Iterator<Attribute> iter = input.getAttributes().iterator();
		while (iter.hasNext()) {
			Attribute atr = iter.next();	
			// V(σA=B(R), A) = V(σA=B(R), B) = min(V(R, A), V(R, B)																																																			
			if (atr.equals(left)) {
				output.addAttribute(new Attribute(atr.getName(),val_count));
			}
			else if (atr.equals(right)){
				output.addAttribute(new Attribute(atr.getName(),val_count));	
			}
			else {
				output.addAttribute(new Attribute(atr));
			}	
		}
		
		op.setOutput(output);
		totalCost += output.getTupleCount();
	}

	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	/* 
	 * Product
     * T(R × S) = T(R)T(S)
	 */
	public void visit(Product op) {
		
		// obtain value from two subtrees
		Relation left_in;
		Relation right_in; 
		left_in = op.getLeft().getOutput();
		right_in = op.getRight().getOutput();
		
		// result of product
		Relation output;
		int left_p;
		int right_p;
		left_p = left_in.getTupleCount();
		right_p = right_in.getTupleCount();
		output = new Relation(left_p * right_p); // c tuple = left tuple * right tuple
		
		// Left part: adding attributes
		Iterator<Attribute> iter_left = left_in.getAttributes().iterator(); // Return the list of attributes contained in this relation
		while (iter_left.hasNext()) {
			output.addAttribute(new Attribute(iter_left.next())); //adding attributes
		}
        // Right part: adding attributes
		Iterator<Attribute> iter_right = right_in.getAttributes().iterator();
		while (iter_right.hasNext()){
			output.addAttribute(new Attribute(iter_right.next()));//adding attributes
		}
		
		op.setOutput(output);
		totalCost += output.getTupleCount();
	}
	
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	/* Join 
	 * T(R⨝A=BS) = T(R)T(S)/max(V(R,A),V(S,B)), V(R⨝A=BS, A) = V(R⨝A=BS, B) = min(V(R, A), V(S, B))
     * (assume that A is an attribute of R and B is an attribute of S)
	 * Note that, for an attribute C of R that is not a join attribute, V(R⨝A=BS, C) = V(R, C)
	 * (similarly for an attribute of S that is not a join attribute)
	 */
	public void visit(Join op) {
		
		// obtain value from two subtrees
		Relation left_in;
		Relation right_in;
		Predicate predicate;
		Attribute attribute_left;
		Attribute attribute_right;

		left_in = op.getLeft().getOutput();
		right_in = op.getRight().getOutput();
		predicate = op.getPredicate(); 
		attribute_left = new Attribute(predicate.getLeftAttribute().getName()); // left attr != null
		attribute_right = new Attribute(predicate.getRightAttribute().getName()); // right attr != null
		
		// obtain attributes' correct value
		List<Attribute> att_all = new ArrayList<>();
		att_all.addAll(left_in.getAttributes()); // Appends all of the elements in the specified collection to the end of this list
		att_all.addAll(right_in.getAttributes());

		for(Attribute att1 : att_all){
			if (att1.equals(attribute_left)) {
				String att1_name;
				int att1_count;
				att1_name = att1.getName();
				att1_count = att1.getValueCount();
				attribute_left = new Attribute(att1_name, att1_count);
			} 
			if (att1.equals(attribute_right)){
				String att1_name;
				int att1_count;
				att1_name = att1.getName();
				att1_count = att1.getValueCount();
				attribute_right = new Attribute(att1_name, att1_count);
			} 
		}
		
		// output of T(R⨝A=BS) = T(R)T(S)/max(V(R,A),V(S,B))
		Relation output;
		int Tr;
		int Ts;
		int Vr;
		int Vs;

		Tr = left_in.getTupleCount(); // T(R)
		Ts = right_in.getTupleCount();// T(S)
		Vr = attribute_left.getValueCount(); // V(R,A)
		Vs = attribute_right.getValueCount(); // V(S,B)

		output = new Relation(Tr * Ts / Math.max(Vr, Vs));
		
		// Note that, for an attribute C of R that is not a join attribute, V(R_jo,A) = V(R_jo, A) = min(V(R,A), V(S,B))
		int size1;
		int output_count;
		Attribute att_left_jo;
		Attribute att_right_jo;

		output_count = output.getTupleCount();
		size1 = Math.min(Math.min(Vr, Vs), output_count);
		att_left_jo = new Attribute(attribute_left.getName(), size1);
		att_right_jo = new Attribute(attribute_right.getName(), size1);
		
		// Left part: adding attributes
		Iterator<Attribute> iter1 = left_in.getAttributes().iterator();
		while (iter1.hasNext()) {
			Attribute att = iter1.next();
			if(!att.equals(attribute_left)) {
				output.addAttribute(new Attribute(att));
			} 
			else {
				output.addAttribute(att_left_jo);
			}
		}
		
		// Right part: Adding attributes
		Iterator<Attribute> iter2 = right_in.getAttributes().iterator();
		while (iter2.hasNext()) {
			Attribute att = iter2.next();
			if(!att.equals(attribute_right)){
				output.addAttribute(new Attribute(att));
			} 
			else {
				output.addAttribute(att_right_jo);
			}
		}
		
		op.setOutput(output);
		totalCost += output.getTupleCount();
	}
	
	public int getCost(Operator plan) {
		this.totalCost = 0;
		plan.accept(this);		
		return this.totalCost;
	}
}
