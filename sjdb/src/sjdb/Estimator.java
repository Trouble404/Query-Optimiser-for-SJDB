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
			output.addAttribute(new Attribute(iter_right.next()));
		}
		
		op.setOutput(output);
		totalCost += output.getTupleCount();
	}
	
	public void visit(Join op) {
		
		// get output from two subtrees
		Relation left_rel = op.getLeft().getOutput();
		Relation right_rel = op.getRight().getOutput();
		
		Predicate p = op.getPredicate(); // the predicate
		Attribute attr_left = new Attribute(p.getLeftAttribute().getName()); // left attr != null
		Attribute attr_right = new Attribute(p.getRightAttribute().getName()); // right attr != null
		
		// get the correct valuecounts for the attributes
		List<Attribute> all_attrs = new ArrayList<>();
		all_attrs.addAll(left_rel.getAttributes());
		all_attrs.addAll(right_rel.getAttributes());
		for(Attribute attr_found : all_attrs){
			if (attr_found.equals(attr_left)) attr_left = new Attribute(attr_found.getName(), attr_found.getValueCount());
			if (attr_found.equals(attr_right)) attr_right = new Attribute(attr_found.getName(), attr_found.getValueCount());
		}
		
		// output of the join.c_tuple = T(R) * T(S) / max ( V(R,A) , V(S,B) )
		Relation output = new Relation(left_rel.getTupleCount() * right_rel.getTupleCount() / Math.max(attr_left.getValueCount(), attr_right.getValueCount()));
		
		// V(R_join, A) = V(R_join, A) = min ( V(R,A) , V(S,B) )
		int uniq_size = Math.min(Math.min(attr_left.getValueCount(), attr_right.getValueCount()), output.getTupleCount());
		Attribute join_attr_left = new Attribute(attr_left.getName(), uniq_size);
		Attribute join_attr_right = new Attribute(attr_right.getName(), uniq_size);
		
		// add the attributes from left relation
		Iterator<Attribute> liter = left_rel.getAttributes().iterator();
		while (liter.hasNext()) {
			Attribute attr = liter.next();
			if(!attr.equals(attr_left)) output.addAttribute(new Attribute(attr));
			else output.addAttribute(join_attr_left);
		}
		
		// add the attributes from the right relation
		Iterator<Attribute> riter = right_rel.getAttributes().iterator();
		while (riter.hasNext()) {
			Attribute attr = riter.next();
			if(!attr.equals(attr_right)) output.addAttribute(new Attribute(attr));
			else output.addAttribute(join_attr_right);
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
