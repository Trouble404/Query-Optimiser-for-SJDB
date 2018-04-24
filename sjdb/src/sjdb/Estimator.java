package sjdb;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class Estimator implements PlanVisitor {
	
	private int totalCost = 0;
	
	public Estimator() {
		// empty constructor
	}

	/* 
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

	/* 
	 * T(πA(R)) = T(R)
	 *
	 * Assume that projection does not eliminate duplicate tuples
	 */
	public void visit(Project op) {
		
		// Obtain output relation from given input relation
		Relation input = op.getInput().getOutput(); // Return the single child operator of this operator, Return the relation produced by this operator as output
		Relation output = new Relation(input.getTupleCount()); // Return the tuple count for this relation
		
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
	
	public void visit(Select op) {
		
		Predicate p = op.getPredicate(); // the predicate
		Attribute attr_left = new Attribute(p.getLeftAttribute().getName()); // left attr != null
		
		// the new attributes from select predicate with new value counts
		Attribute output_left_attr = null;
		
		// get the input relation, which is the output of the input operator tree
		Relation input = op.getInput().getOutput();
		Relation output;
		
		// find and fill in the right left attribute value count
		for(Attribute attr_found : input.getAttributes()){
			if (attr_found.equals(attr_left)) attr_left = new Attribute(attr_found.getName(), attr_found.getValueCount());
		}
		
		if(p.equalsValue()) {
			// attr = val
			output = new Relation(input.getTupleCount()/attr_left.getValueCount());
			output_left_attr = new Attribute(attr_left.getName(), Math.min(1, output.getTupleCount()));
		
			for (Attribute attr : input.getAttributes()){
				if (!attr.equals(attr_left)) {
					output.addAttribute(new Attribute(attr));
				}
			}
			
			// add left attr always
			output.addAttribute(output_left_attr);
		} else {
			// attr = attr
			Attribute attr_right = new Attribute(p.getRightAttribute().getName()); // right != null
			output = new Relation(input.getTupleCount()/Math.max(attr_left.getValueCount(), attr_right.getValueCount()));
			
			for(Attribute attr_found : input.getAttributes()){
				if (attr_found.equals(attr_right)) attr_right = new Attribute(attr_found.getName(), attr_found.getValueCount());
			}
			
			int size = Math.min(Math.min(attr_left.getValueCount(), attr_right.getValueCount()), output.getTupleCount());
			output_left_attr = new Attribute(attr_left.getName(), size);
			Attribute output_right_attr = new Attribute(attr_right.getName(), size);
			
			// add the attributes from the original relation except the selection attrs, A			
			for (Attribute attr : input.getAttributes()){
				if (!attr.equals(attr_left) && !attr.equals(attr_right)) output.addAttribute(new Attribute(attr));
			}
			
			// add both attrs
			output.addAttribute(output_left_attr);
			output.addAttribute(output_right_attr);
		}
		
		//System.out.println("SELECT " + output.render());
		
		// set the output to select
		op.setOutput(output);
		totalCost += output.getTupleCount();
	}
	
	public void visit(Product op) {
		
		// get output from two subtrees
		Relation left = op.getLeft().getOutput();
		Relation right = op.getRight().getOutput();
		
		// output of the product.c_tuple = left.c_tuple * right.c_tuple
		Relation output = new Relation(left.getTupleCount() * right.getTupleCount());
		
		// add attributes from left
		left.getAttributes().forEach(attr -> output.addAttribute(new Attribute(attr.getName(), attr.getValueCount())));
		
		// add attributes from right
		right.getAttributes().forEach(attr -> output.addAttribute(new Attribute(attr.getName(), attr.getValueCount())));
		
		//System.out.println("PRODUCT " + output.render());
		
		// set the output of the product
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
