/**
 * 
 */
package sjdb;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.Iterator;
import java.util.List;


/**
 * This Optimiser class represents an Optimiser for planning
 * 
 * @author Junming Zhang
 *
 */
public class Optimiser implements PlanVisitor {
	
	private static Estimator EST = new Estimator(); // Apply Estimator

	public Optimiser(Catalogue cat) {
	}

	private Set<Attribute> allAttributes = new HashSet<>();
	private Set<Predicate> allPredicates = new HashSet<>();
	private Set<Scan> allScans = new HashSet<Scan>();
	
	public void visit(Scan op) { allScans.add(new Scan((NamedRelation)op.getRelation())); }
	public void visit(Project op) { allAttributes.addAll(op.getAttributes()); }
	public void visit(Product op) {}
	public void visit(Join op) {}
	public void visit(Select op) {
		allPredicates.add(op.getPredicate());
		allAttributes.add(op.getPredicate().getLeftAttribute());
		if(!op.getPredicate().equalsValue()) allAttributes.add(op.getPredicate().getRightAttribute());
	}

	public Operator optimise(Operator plan) {
		plan.accept(this);
		// in the canonical plan, the selects and projects will be push down
		List<Operator> operation_blocked;
		operation_blocked = ObtainBlockedOptForScans(allScans, allAttributes, allPredicates, plan); // Obtain blocked operator in each scan

		Operator Plan_optimised;
		Plan_optimised = findCheapsetPlan(allPredicates, operation_blocked, plan); // Find the cheapest plan and calculate the cheapset cost
		
		return Plan_optimised;
	}
	
	/**
	 * Find the cheapest plan and calculate the cheapset cost
	 */
	private static Operator findCheapsetPlan(Set<Predicate> oriPre, List<Operator> op1, Operator root){
		
		List newlist;
		List<Predicate> pre1;
		newlist = new ArrayList<>();
		pre1 = newlist;
		pre1.addAll(oriPre);
		
		// predicate sorted
		List<List<Predicate>> sortedPre;
		sortedPre = ProducePer(pre1); //Produce permutated list of possible predicates
		
		// calculate cheapest cost
		Operator Plan_cheapset;
		int Cost_cheapset;
		Plan_cheapset = null; // initialization
		Cost_cheapset = Integer.MAX_VALUE;
		
		// in each permutation
		for (List<Predicate> loop : sortedPre) {
			
			// set operator
			List<Operator> op2;
			List newlist1;
			newlist1 = new ArrayList<>();
			op2 = newlist1;
			op2.addAll(op1);
			
			// produce the tree
			Operator Plan1;
			Plan1 = OperatorControl(op2, loop, root); //Find the only one or pair of left operator 
			int temp;
			temp = EST.getCost(Plan1);
			System.out.println("Found plan with cost: " + temp);///////////////debug
			
			// create the cheapset plan
			Plan_cheapset = (temp < Cost_cheapset) ? Plan1 : Plan_cheapset;
			Cost_cheapset = (temp < Cost_cheapset) ? temp : Cost_cheapset;
		}
		
		return Plan_cheapset;
	}
	
	/**
	 * Obtain blocked operator in each scan
	 */
	private static List<Operator> ObtainBlockedOptForScans(Set<Scan> scans, Set<Attribute> attrs, Set<Predicate> predicates, Operator root) {
		
		// the blocked operators in all scans
		List<Operator> BlockedOperator;
		List newlist;
		newlist = new ArrayList<>(scans.size());
		BlockedOperator = newlist;
		
		for (Scan loop: scans){
			Operator processedSelect;
			processedSelect = RemoveRedundantSelect(loop, predicates);
			List<Predicate> ele1; 
			List newlist1;
			newlist1 = new ArrayList<>(scans.size());
			ele1 = newlist1;
			ele1.addAll(predicates);
			ObtainReqAtt(ele1, root);
            // (Choose and project requied attributes) + (Obtain reqired attributes from the predicate and opreator)S
			BlockedOperator.add(ProjectReqAtt(processedSelect, ObtainReqAtt(ele1, root)));
		}
		return BlockedOperator;
	}
	
	/**
	 * Remove redundant select operator
	 */
	private static Operator RemoveRedundantSelect(Operator op, Set<Predicate> preds){
		
		// The result
		Operator result;
		result = op;

		// attributes here contains unremoved attributes
		List<Attribute> usedAttrs;
		Relation result_out;
		result_out = result.getOutput();
		usedAttrs = result_out.getAttributes();
			
		// loop to find applicable in the operator of the list
		Iterator<Predicate> loop = preds.iterator();
		while(loop.hasNext()){
	
			Predicate Pre1; // current predict
			Pre1 = loop.next();
			
			// set output if the operator is unset
			if(result.getOutput() == null) {
				result.accept(EST);
			}
			
			// attr = val and contains left relation of output
			if ((Pre1.equalsValue() && usedAttrs.contains(Pre1.getLeftAttribute()))) {
				// add select operator in output
				result = new Select(result, Pre1);
				// remove used predict
				loop.remove();
			}
			// attr != val and contains relation of output
			if ((!Pre1.equalsValue()) && (usedAttrs.contains(Pre1.getLeftAttribute()) && usedAttrs.contains(Pre1.getRightAttribute()))) {
				result = new Select(result, Pre1);
				loop.remove();
			}
		}
		return result;
	}
	
	/**
	 * Choose and project requied attributes
	 */
	private static Operator ProjectReqAtt(Operator op, Set<Attribute> attrs){

		// fill up output
		if(op.getOutput() == null) op.accept(EST);
		
		// choose attributes to project
		List newlist;
		newlist = new ArrayList<>(attrs);
		List<Attribute> ToProjectatt;
		ToProjectatt = newlist;
		// Retains only the elements in this list that are contained in the specified collection
		List op1;
		op1 = op.getOutput().getAttributes();
		ToProjectatt.retainAll(op1); 
		
		// return required attributes
		if (ToProjectatt.size() > 0) {
			Operator op1_1 = new Project(op, ToProjectatt);
			op1_1.accept(EST);
			return op1_1;
		} else {
			return op;
		}
	}
	/**
	 * Find the only one or pair of left operator
	 * 
	 * no operator in predicate then go product
	 * one operator in predicate then go select
	 * two operatots in predicate then go join
	 * using project for unrequried attribute
	 */
	private static Operator OperatorControl(List<Operator> op1, List<Predicate> pre1, Operator root){
		
		Operator out1;
		out1 = null;
		int con1;
		con1 = 1;
		if (op1.size() == con1){
			out1 = op1.get(0); //first element
			if (out1.getOutput() == null){
				out1.accept(EST);//fix emputy
			} 
			return out1;
		}
		
		// find joins or selects
		Iterator<Predicate> loop = pre1.iterator();
		while(loop.hasNext()){
			
			Predicate Pre2;//current predicate
			Pre2 = loop.next();

			Operator zuo;
			Operator you;
			zuo = takeOptFormAtt(op1, Pre2.getLeftAttribute());// The potential Operator in left attributes
			you = takeOptFormAtt(op1, Pre2.getRightAttribute());// The potential Operator in right attributes
			
			// Create select when only 1 operator in predicate
			if((zuo == null && you != null)){
				out1 = new Select(zuo != null? zuo : you, Pre2);
				loop.remove();
			} 
			if (zuo != null && you == null){
				out1 = new Select(zuo != null? zuo : you, Pre2);
				loop.remove();
			}
			
			// create join when both opreator in predicate
			if(zuo != null && you != null){
				out1 = new Join(zuo, you, Pre2);
				loop.remove();
			}
			
			// sort the output relation
			if (out1.getOutput() == null){
				out1.accept(EST);
			} 
			
			// obtain reqired atrrbuties
			Set reqiredAtt;
			reqiredAtt = ObtainReqAtt(pre1, root);
			Set<Attribute> ReqAtt;
			ReqAtt = reqiredAtt;
			
			// project output when not all attributes are requried
			List avaAtt;
			avaAtt = out1.getOutput().getAttributes();
			List<Attribute> Att_avalibe; // available attributes
			Att_avalibe = avaAtt;
			
			// when there are no att can left out
			if (ReqAtt.size() == Att_avalibe.size() && Att_avalibe.containsAll(ReqAtt)){
				op1.add(out1);
			}
			else{
				// keep the attribute
				List<Attribute> remainAtt;
				remainAtt = Att_avalibe.stream().filter(attr -> ReqAtt.contains(attr)).collect(Collectors.toList());
				int check1;
				check1 = 0;
				if (remainAtt.size() == check1) {
					op1.add(out1); 
				} else {
					Project temp;
					Project temp1;
					temp = new Project(out1, remainAtt);
					temp1 = temp;
					temp1.accept(EST); 
					op1.add(temp1);
				}
			}
		}
		
		// if no predicate left, change operators to products
		while(op1.size() > 1) {
			// first and second elements
			Operator f1;
			Operator f2;
			Operator product;
			f1 = op1.get(0);
			f2 = op1.get(1);
			product = new Product(f1, f2);
			product.accept(EST);
			
			// remove the first two and add the new one
			// adding new elements to replace f1,f2
			op1.remove(f1);
			op1.remove(f2);
			op1.add(product);
		}

		out1 = op1.get(0); // obtain the left one
		return out1;
	}
	
	/**
	 * judge and take if operators contain attribute in relation
	 */
	private static Operator takeOptFormAtt(List<Operator> listOpt, Attribute attr){
	
		Iterator<Operator> loop = listOpt.iterator();
		while(loop.hasNext()){
			
			Operator op1; //current opreator
			op1 = loop.next();

			// return when there are relation contained in the operator
			Boolean check;
			check = op1.getOutput().getAttributes().contains(attr);
			if (check){
				loop.remove();
				return op1;
			}
		}
		return null;
	}
	
	/**
	 * Obtain reqired attributes from the predicate and opreator
	 */
	private static Set<Attribute> ObtainReqAtt(List<Predicate> predicates, Operator root){
		
		// required set of attributes
		Set hashset;
		hashset = new HashSet<>();
		Set<Attribute> att_required = hashset;
		
		Iterator<Predicate> loop = predicates.iterator();
		while(loop.hasNext()){
			
			// adding attributes to the predicate
			Predicate Pre2; // current predicate
			Attribute lef;
			Attribute rig;

			Pre2 = loop.next();
			lef = Pre2.getLeftAttribute();
			rig = Pre2.getRightAttribute();
			
			att_required.add(lef);
			if (rig != null) {
				att_required.add(rig);
			}
		}
		
		// add attribute when root is project
		if (root instanceof Project) {
			att_required.addAll(((Project) root).getAttributes());
		}
		
		return att_required;
	}
	
	/**
	 * Produce permutated list of possible predicates
	 */
	private static List<List<Predicate>> ProducePer(List<Predicate> attrs) {
		
		// 1 element condition
		if (attrs.size() == 0) { 
			List newlist;
			newlist = new ArrayList<List<Predicate>>();
			List<List<Predicate>> output1;
			output1 = newlist;
			List newlist1;
			newlist1 = new ArrayList<List<Predicate>>();
		    output1.add(newlist1);
		    return output1;
		}
		
		// multiple elements condition, the first element will be removed
		Predicate pre1;
		pre1 = attrs.remove(0); // remove first element
		List<List<Predicate>> val1; // processed value
		List newlist2;
		newlist2 = new ArrayList<List<Predicate>>();
		val1 = newlist2;

		// recursion
		List<List<Predicate>> temp1; // permutations
		temp1 = ProducePer(attrs);
		

		for (List<Predicate> smalletemp1 : temp1) {
		    for (int temp2=0; temp2 <= smalletemp1.size(); temp2++) {
				List smalllist;
		        smalllist = new ArrayList<Predicate>(smalletemp1);
		    	List<Predicate> temp = smalllist;
		    	temp.add(temp2, pre1);
		    	val1.add(temp);
		    }
		}	
		return val1;
	}
}
