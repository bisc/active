/** <copyright>
 * Copyright (c) 2014 Carnegie Mellon University. All Rights Reserved.

 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:

 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following acknowledgments
 * and disclaimers.

 * 2. Redistributions in binary form must reproduce the above
 * copyright notice, this list of conditions and the following
 * disclaimer in the documentation and/or other materials provided
 * with the distribution.

 * 3. The names "Carnegie Mellon University," "SEI" and/or "Software
 * Engineering Institute" shall not be used to endorse or promote
 * products derived from this software without prior written
 * permission. For written permission, please contact
 * permission@sei.cmu.edu.

 * 4. Products derived from this software may not be called "SEI" nor
 * may "SEI" appear in their names without prior written permission of
 * permission@sei.cmu.edu.

 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:

 * This material is based upon work funded and supported by the
 * Department of Defense under Contract No. FA8721-05-C-0003 with
 * Carnegie Mellon University for the operation of the Software
 * Engineering Institute, a federally funded research and development
 * center.

 * Any opinions, findings and conclusions or recommendations expressed
 * in this material are those of the author(s) and do not necessarily
 * reflect the views of the United States Department of Defense.

 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE
 * ENGINEERING INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS"
 * BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO WARRANTIES OF ANY KIND,
 * EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT
 * LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR MERCHANTABILITY,
 * EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL. CARNEGIE
 * MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.

 * This material has been approved for public release and unlimited
 * distribution.

 * DM-0001534

 </copyright> **/

package org.osate.aadl2.active.verificationengine.smt;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.emf.common.util.EList;
import org.osate.aadl2.active.common.ContractUtils;
import org.osate.xtext.aadl2.contracts.Contract.Addition;
import org.osate.xtext.aadl2.contracts.Contract.AnalysisContract;
import org.osate.xtext.aadl2.contracts.Contract.AndOrExpression;
import org.osate.xtext.aadl2.contracts.Contract.ArithmeticSigned;
import org.osate.xtext.aadl2.contracts.Contract.BoolBinOp;
import org.osate.xtext.aadl2.contracts.Contract.BooleanLiteral;
import org.osate.xtext.aadl2.contracts.Contract.BooleanNegation;
import org.osate.xtext.aadl2.contracts.Contract.CompOp;
import org.osate.xtext.aadl2.contracts.Contract.ComparisonExpression;
import org.osate.xtext.aadl2.contracts.Contract.ContractClause;
import org.osate.xtext.aadl2.contracts.Contract.Expression;
import org.osate.xtext.aadl2.contracts.Contract.FloatLiteral;
import org.osate.xtext.aadl2.contracts.Contract.FunctionalExpression;
import org.osate.xtext.aadl2.contracts.Contract.IntLiteral;
import org.osate.xtext.aadl2.contracts.Contract.ListExpression;
import org.osate.xtext.aadl2.contracts.Contract.ListInOp;
import org.osate.xtext.aadl2.contracts.Contract.ListLiteral;
import org.osate.xtext.aadl2.contracts.Contract.Multiplication;
import org.osate.xtext.aadl2.contracts.Contract.QFGTMREF;
import org.osate.xtext.aadl2.contracts.Contract.QuantClause;
import org.osate.xtext.aadl2.contracts.Contract.QuantifierType;
import org.osate.xtext.aadl2.contracts.Contract.StringLiteral;

public class ContractToSmtGenerator {

	// store components and properties that
	// will be used in smt
	private Map<String, Set<String>> compToProp;
	// store associations between variables and types in FORALL
	// useful to reconstruct type of variables when recording properties used in expression
	private Map<String, String> varToType;
	// store correspondence between string literals/refs and integers
	private Map<String, Integer> stringToIntDict;
	// generate smt for properties
	private DefAndFactSmtGenerator psg;

	public ContractToSmtGenerator() {
		compToProp = new HashMap<String, Set<String>>();
		varToType = new HashMap<String, String>();
		stringToIntDict = new HashMap<String, Integer>();
		psg = new DefAndFactSmtGenerator();

		clearData();
	}

	private void clearData() {
		compToProp.clear();
		varToType.clear();
		stringToIntDict.clear();
		psg.clearData();
	}

	/**
	 * Generate an SMT2 model for a given AnalysisContract. The main interface
	 * of this class.
	 * 
	 * @param ac
	 *            the AnalysisContract to generate for
	 * @param forAssumptions
	 *            indicates whether the AnalysisContract is an assumption
	 *            (slight differences in processing)
	 * @return
	 */
	public String generateSmtForClause(AnalysisContract ac, ContractClause cc, boolean verifyOrFind) {

		// prepare for a new iteration, clean the state
		clearData();

		// handle contract clause itself first (implicitly includes traversing unknown types and properties)
		String clauseOutput = ""; 
		if (verifyOrFind)
			clauseOutput += generateSmtContractClauseVerify(cc);
		else 
			clauseOutput += generateSmtContractClauseFind(cc);    

		// process input and output to collect info about components and
		// properties
		traverseInputOutput(ac);

		// create definitions and facts
		// also populate string2int dictionary as a side effect
		String defFactOutput = psg.generateDefinitionsAndFacts(compToProp, ac, stringToIntDict);

		// apply dictionary transform to clause output
		// FIXME collisions with other names possible
		for (String str: stringToIntDict.keySet()) { 
			clauseOutput = clauseOutput.replace('$' + str + '$', String.valueOf(stringToIntDict.get(str)));
		}

		// defs and facts come come first
		return defFactOutput + clauseOutput;
	}

	// traverses input and output for component and property names to include into smt program
	private void traverseInputOutput(AnalysisContract ac) {
		// handle the input and output clauses
		traverseQFGTMREFs(ac.getInput().getNames());
		traverseQFGTMREFs(ac.getOutput().getNames());
	}

	// handles a list of identifiers for inputs and outputs
	private void traverseQFGTMREFs(EList<QFGTMREF> reflist) {
		Iterator<QFGTMREF> refIt = reflist.iterator();
		while (refIt.hasNext()) {
			QFGTMREF ref = refIt.next();
			EList<String> ids = ref.getIds();
			String compType = ids.get(0);

			int size = ids.size();
			// dealing only with size 1 and  2 now
			if (size == 1) { 
				recordComponentType(compType);
				System.out.println("component for smt:" + compType);
			} else if (size == 2) {
				recordProperty(compType, ids.get(1));
				System.out.println("property for smt:" + ids.get(1) + " of component " + compType);
			} else {
				throw new UnsupportedOperationException("Cannot handle QFTMGREFs not of size 1 or 2");
			}
		}
	}

	// records that a component type was used in contract 
	private void recordComponentType(String compType) { 
		//	System.out.println("recording component type " + compType);
		// record the component if haven't yet
		if(!compToProp.containsKey(compType)) {
			compToProp.put(compType, new HashSet<String>());
		}
	}

	// records that a property with a certain component type was used in contract 
	private void recordProperty(String compType, String propName) { 
		//	System.out.println("recording property " + propName + " for " + compType);
		// add, avoiding duplicates
		recordComponentType(compType); 
		Set<String> propSet = compToProp.get(compType);
		propSet.add(propName);
	}

	// generates a contract clause smt for verification
	private String generateSmtContractClauseVerify(ContractClause cc) {

		// prep strings 
		String preAssertOutput = "";
		String smtContractOutput = "(assert (not "; // negate claim right away
		String tailOutput = "\n)\n)";

		// generate for the quantified variables clause
		QuantClause qc = cc.getVarQuant();
		if (qc != null) {
			String variableIdRestrictions = "";
			Iterator<String> variableIt = qc.getIds().iterator();
			Iterator<String> typeIt = qc.getTypes().iterator();

			// determine the quantifier and binding operation between suchthat and holds
			String bindingOp = "";
			if (qc.getQuant().equals(QuantifierType.FORALL)){ 
				smtContractOutput += "\n\t(forall ("; 
				bindingOp = "=>";
			} else if (qc.getQuant().equals(QuantifierType.EXISTS)) {
				smtContractOutput += "\n\t(exists (";
				bindingOp = "and";
			} else 
				throw new UnsupportedOperationException("Unknown quantifier " + qc.getQuant());

			tailOutput += "))\n";

			// implication, and for listing IDs
			variableIdRestrictions += "\t(" + bindingOp + " \n\t( and ";

			while (variableIt.hasNext()) {
				String varName = variableIt.next();
				String varType = typeIt.next();
				//		System.out.println("Captures variable " + varName + " of type " + varType);
				varToType.put(varName, varType);

				// TODO do a better job of type conversion here
				smtContractOutput += "(" + varName + " " + varType + ") ";
				variableIdRestrictions += psg.generateComponentIDRestrictions(varName, varType);
				// TODO check that component types used for variables are
				// present in the components set
				// will have to pass smth into this function or out
			}

			smtContractOutput += ")\n\t" + variableIdRestrictions + "\n\t" ;
		}

		// handle SUCH THAT
		// has to be done after qc because types of vars need to be known to resolve properties
		Expression st = cc.getSuchThat();
		String suchThatOut;
		if(st != null){
			if (ContractUtils.isLtl(st))
				throw new UnsupportedOperationException("Cannot use LTL in such that clauses");

			System.out.println("SUCH THAT formula present");
			suchThatOut = generateSmtExpression(st);
		} else 
			suchThatOut = "true";

		// returning to qc because it affects how suchThat gets appended
		if (qc != null) { 
			smtContractOutput += suchThatOut + "\n)\n";
		} else { 
			// if there are no quantified variables, suchthat still needs to be appended
			preAssertOutput += "\n(assert " + suchThatOut + ")\n"; 
		}

		// for verification, generate for HOLDS
		Expression h = cc.getHolds();
		if (h == null)
			throw new UnsupportedOperationException("Cannot verify a non-existed formula");

		System.out.println("HOLDS formula present");

		if (ContractUtils.isLtl(st))
			throw new UnsupportedOperationException("Cannot use SMT for LTL formulas");

		smtContractOutput += "\n" + generateSmtExpression(h);

		return preAssertOutput + smtContractOutput + tailOutput;
	}


	// generates a contract clause smt for model finding
	private String generateSmtContractClauseFind(ContractClause cc) {

		// prep strings
		String preAssertOutput = "";
		String smtContractOutput = "(assert ";
		String tailOutput = "\n)\n";

		// generate for the quantified variables clause
		QuantClause qc = cc.getVarQuant();
		if (qc != null) {
			String variableIdRestrictions = "";
			Iterator<String> variableIt = qc.getIds().iterator();
			Iterator<String> typeIt = qc.getTypes().iterator();

			// we disregard the quantifier here: just need to generate models for suchthat
			variableIdRestrictions += "(assert ( and ";

			while (variableIt.hasNext()) {
				String varName = variableIt.next();
				String varType = typeIt.next();
				varToType.put(varName, varType);
				System.out.println("Captures variable " + varName + " of type " + varType);

				preAssertOutput += "( declare-const " + varName + " " + varType + " )\n";

				variableIdRestrictions += psg.generateComponentIDRestrictions(varName, varType);
				// TODO check that component types used for variables are
				// present in the components set
				// will have to pass smth into this function or out
			}

			preAssertOutput += variableIdRestrictions + "\n\t)\n)\n";
		}

		// generate for SUCH THAT
		// this feeds into an existing assert
		Expression st = cc.getSuchThat();
		if(st != null){
			if (ContractUtils.isLtl(st))
				throw new UnsupportedOperationException("Cannot use LTL in such that clauses");
			System.out.println("SUCH THAT formula present");
			smtContractOutput += generateSmtExpression(st);
		} else 
			smtContractOutput += "true";

		return preAssertOutput + smtContractOutput + tailOutput;
	}

	// a helper method to generate smt for contract expressions
	private String generateSmtExpression(Expression e) {
		if (e instanceof AndOrExpression) {
			AndOrExpression ce = ((AndOrExpression) e);
			String op;
			if (ce.getOp().equals(BoolBinOp.OR)) // "||"
				op = "or";
			else if (ce.getOp().equals(BoolBinOp.AND)) // "&&"
				op = "and";
			else if (ce.getOp().equals(BoolBinOp.IMPLIES))
				op = "=>";
			else
				throw new UnsupportedOperationException("Cannot handle the operation " + ce.getOp());

			return "( " + op + " " + generateSmtExpression(ce.getLeft()) + " " + generateSmtExpression(ce.getRight())
					+ " )";
		} else if (e instanceof ListExpression) {
			ListExpression ce = ((ListExpression) e);
			// convert to smt array theory
			// example: x in a.Not_Colocated
			// convert to: (exists ((i Int)) (= (select Not_Colocated a i) x))
			List<String> ids = ce.getRight().getIds();
			if (ids.size() != 2)
				throw new UnsupportedOperationException("Invalid set reference " + ce);

			//	    String baseCase = "( exists ((i Int)) (= (select " + ids.get(1) + " " + ids.get(0) + 
			//			" i ) " + generateSmtExpression(ce.getLeft()) + "))"; 

			// using both the containment function and the array
			String baseCase = "\t( exists ((i Int)) (and (= (" + psg.arrayNameToContFuncName(ids.get(1)) + " " 
					+ ids.get(0) + " i) true)"
					+ " \n\t(= (select " + ids.get(1) + " " + ids.get(0)  
					+ " i ) " + generateSmtExpression(ce.getLeft()) + ")))";
			if(ce.getOp().equals(ListInOp.IN)) 
				return "\n" + baseCase;
			else if(ce.getOp().equals(ListInOp.NOTIN))
				return "\n( not " + baseCase + ")";
			else 
				throw new UnsupportedOperationException("Cannot handle the operation " + ce.getOp());
		} else if (e instanceof ComparisonExpression) {
			ComparisonExpression ce = ((ComparisonExpression) e);
			if (ce.getOp() != CompOp.NOTEQUALS) // most comparison operators coincide
				return "( " + ce.getOp() + " " + generateSmtExpression(ce.getLeft()) + " "
				+ generateSmtExpression(ce.getRight()) + " )";
			else 
				return "( not ( " + "= " + generateSmtExpression(ce.getLeft()) + " "
				+ generateSmtExpression(ce.getRight()) + " ) )";
		} else if (e instanceof BooleanNegation) { 
			BooleanNegation ce = ((BooleanNegation) e);
			return "( not " + generateSmtExpression(ce.getExpression()) + " )";
		} else if (e instanceof ArithmeticSigned) { 
			ArithmeticSigned ce = ((ArithmeticSigned) e);
			return "-" + generateSmtExpression(ce.getExpression());
		} else if (e instanceof Addition) {
			Addition ce = ((Addition) e);
			return "( " + ce.getOp() + " " + generateSmtExpression(ce.getLeft()) + " "
			+ generateSmtExpression(ce.getRight()) + " )";
		} else if (e instanceof Multiplication) {
			Multiplication ce = ((Multiplication) e);
			return "( " + ce.getOp() + " " + generateSmtExpression(ce.getLeft()) + " "
			+ generateSmtExpression(ce.getRight()) + " )";
		} else if (e instanceof IntLiteral) {
			IntLiteral ce = ((IntLiteral) e);
			return String.valueOf(ce.getValue());
		} else if (e instanceof FloatLiteral) {
			FloatLiteral ce = ((FloatLiteral) e);
			return String.valueOf(ce.getValue());
		} else if (e instanceof BooleanLiteral) {
			BooleanLiteral ce = ((BooleanLiteral) e);
			return String.valueOf(ce.getValue());
		} else if (e instanceof StringLiteral) {
			StringLiteral ce = ((StringLiteral) e);
			// mark string literals to replace them later
			return '$' + ce.getValue() + '$';
		} else if (e instanceof ListLiteral) {
			// example: x.Not_Colocated[1]
			// convert to (select Not_Colocated x 1) 
			ListLiteral ce = ((ListLiteral) e);
			List<String> ids = ce.getList().getIds(); 
			if (ids.size() != 2)
				throw new UnsupportedOperationException("Unknown type of list property " + ce);

			return "(select " + ids.get(1) + " " + ids.get(0) + " " + 
			generateSmtExpression(ce.getIndex()) + ")";
		} else if (e instanceof FunctionalExpression) {
			// functions of one argument f(A): A->B are transformed into
			// two-argument
			// smt functions (A B) -> Bool
			// example: x1.f(x2) -> (f x1 x2)
			FunctionalExpression fe = ((FunctionalExpression) e);
			EList<String> funcIds = fe.getFunc().getIds();

			if (funcIds.size() != 2)
				throw new UnsupportedOperationException("Cannot handle the QFGTMREF as a func  " + funcIds);

			String varName = funcIds.get(0); 
			String funName = funcIds.get(1); 

			// first off, record the property, determining component type by variable name
			// need to determine component type first
			recordProperty(varToType.get(varName), funName);

			// handle smt function call generation
			EList<Expression> args = fe.getArgs();
			if (args.size() != 1)
				throw new UnsupportedOperationException("Cannot handle any other than 1 func arg " + args);

			String exp = generateSmtExpression(args.get(0));
			//	    EList<String> argIds = args.get(0).getIds();

			// TODO handle larger dimensions
			//	    if (argIds.size() != 1)
			//		throw new UnsupportedOperationException("Cannot handle the QFGTMREF as a func arg " + argIds);

			return "( " + funcIds.get(1) + " " + funcIds.get(0) + " " + exp + " )";

		} else if (e instanceof QFGTMREF) {
			EList<String> ids = ((QFGTMREF) e).getIds();
			int size = ids.size();
			if (size == 1)
				// then it's just a variable name - generate
				return ids.get(0);
			else if (size == 2) {
				// then it's a property, which should be recorded and 
				// converted to an smt function
				// like x1.period -> (period x1) 
				recordProperty(varToType.get(ids.get(0)), ids.get(1));
				return "(" + ids.get(1) + " " + ids.get(0) + ")";
			} else
				throw new UnsupportedOperationException("Cannot handle the QFGTMREF " + ids);

			//	    return ContractUtils.appendAgregateStringList(ids);
		}
		return "";
	}
}
