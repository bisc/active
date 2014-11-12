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

package org.osate.aadl2.active.contracts;

import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.emf.common.util.EList;
import org.osate.aadl2.active.common.ContractUtils;
import org.osate.aadl2.active.common.VariableAssignmentHashMap;
import org.osate.aadl2.active.interfaces.LtlEngine;
import org.osate.aadl2.active.interfaces.SmtEngine;
import org.osate.aadl2.active.interfaces.VariableAssignment;
import org.osate.aadl2.active.verificationengine.battery.BatterySpinEngine;
import org.osate.aadl2.active.verificationengine.sched.SchedSpinEngine;
import org.osate.aadl2.active.verificationengine.smt.Z3Engine;
import org.osate.xtext.aadl2.contracts.Contract.Addition;
import org.osate.xtext.aadl2.contracts.Contract.AnalysisContract;
import org.osate.xtext.aadl2.contracts.Contract.AndOrExpression;
import org.osate.xtext.aadl2.contracts.Contract.ArithmeticSigned;
import org.osate.xtext.aadl2.contracts.Contract.BooleanLiteral;
import org.osate.xtext.aadl2.contracts.Contract.BooleanNegation;
import org.osate.xtext.aadl2.contracts.Contract.ComparisonExpression;
import org.osate.xtext.aadl2.contracts.Contract.ContractClause;
import org.osate.xtext.aadl2.contracts.Contract.Expression;
import org.osate.xtext.aadl2.contracts.Contract.FloatLiteral;
import org.osate.xtext.aadl2.contracts.Contract.FunctionalExpression;
import org.osate.xtext.aadl2.contracts.Contract.IntLiteral;
import org.osate.xtext.aadl2.contracts.Contract.LTLExpression;
import org.osate.xtext.aadl2.contracts.Contract.Multiplication;
import org.osate.xtext.aadl2.contracts.Contract.QFGTMREF;
import org.osate.xtext.aadl2.contracts.Contract.QuantifierType;

public class ActiveVerifier {

	SmtEngine smt = new Z3Engine();
	Set<LtlEngine> ltlEngines = new HashSet<LtlEngine>(); 

	public ActiveVerifier() { 
		// TODO decouple this controller from the creation of specific engines
		ltlEngines.add(new SchedSpinEngine());
		ltlEngines.add(new BatterySpinEngine());
	}

	// verify all assumptions of ac
	public boolean verifyAssumptions(AnalysisContract ac, IProgressMonitor pm) throws InterruptedException {
		pm.beginTask("Verifying assumptions of " + ac.getName(), ac.getAssumptions().size());
		for (ContractClause cc : ac.getAssumptions()) {
			System.out.println("Verifying assumption: " + cc);
			if (!verifyContract(ac, cc, new SubProgressMonitor(pm, 1)))
				return false;
		}
		return true;
	}

	// verify all guarantees of ac
	public boolean verifyGuarantees(AnalysisContract ac, IProgressMonitor pm) throws InterruptedException {
		pm.beginTask("Verifying guarantees of " + ac.getName(), ac.getGuarantees().size());
		for (ContractClause cc : ac.getGuarantees()) {
			System.out.println("Verifying guarantee: " + cc);
			if (!verifyContract(ac, cc, new SubProgressMonitor(pm, 1)))
				return false;
		}
		return true;
	}

	// verifies a single contract cc versus the current system model
	private boolean verifyContract(AnalysisContract ac, ContractClause cc, IProgressMonitor pm) throws InterruptedException { 
		// check if we are dealing with an LTL formula or not
		boolean isLtl = ContractUtils.isLtl(cc.getHolds()), 
				result;
		DateFormat df = new SimpleDateFormat("HH-mm-ss-SS");
		String filename; 

		if(isLtl) {
			// determine what spin model to use
			LtlEngine ltlEng = matchLtlEngine(cc); 

			if (cc.getVarQuant() != null) { 
				boolean isForall = cc.getVarQuant().getQuant().equals(QuantifierType.FORALL);
				result = isForall; // assume true if forall, and assume false if exists

				// generate models for suchThat
				List<VariableAssignment> models = smt.findModelsForSuchThat(ac, cc,
						"smt-findmodels-" + df.format(new Date()) + ".smt");
				pm.beginTask("Running spin " + ltlEng.getName(), models.size());

				// verify for each
				for (VariableAssignment va : models) {
					if (pm.isCanceled()) 
						throw new InterruptedException("Contract verification was cancelled");


					System.out.println("Running spin for variable assignment " + va);
					boolean shortcircuitExit = false;
					filename = ltlEng.getName() + "-" + df.format(new Date()) + ".pml";	    
					if (isForall) {
						// has to be true for all models
						result = result && ltlEng.verify(ac, cc, va, filename);
						// shortcircuited evaluation
						if (!result)
							shortcircuitExit = true; 
					} else {
						// has to be true for at least one model
						result = result || ltlEng.verify(ac, cc, va, filename);
						// shortcircuited evaluation
						if (result)
							shortcircuitExit = true; 
					}
					pm.worked(1);

					if(shortcircuitExit) { 
						pm.done();
						return result;
					}
				}
			} else { 
				pm.beginTask("Running spin " + ltlEng.getName(), IProgressMonitor.UNKNOWN);
				// run a single spin on an empty variable assignment since there is no free variables
				System.out.println("Running spin for an empty variable assignment");
				VariableAssignment va = new VariableAssignmentHashMap(); 
				filename = ltlEng.getName() + "-" + df.format(new Date()) + ".pml";
				result = ltlEng.verify(ac, cc, va, filename);
			}
		} else {
			pm.beginTask("Running Z3 ", IProgressMonitor.UNKNOWN);
			// holds is not ltl, can defer all checking to a single run of SMT
			System.out.println("Running smt for the full contract -- no LTL detected");
			filename = "smt-verify-" + df.format(new Date()) + ".smt";
			result = smt.verify(ac, cc, filename);
		}

		pm.done();
		return result;
	}

	/**
	 * Find a matching ltl engine to verify a contract clause. 
	 * @param cc clause to be verified
	 * @return the matching ltl engine
	 */

	private LtlEngine matchLtlEngine(ContractClause cc) { 
		// find all ids
		Set<String> expIds = findIdsInExpression(cc.getHolds());
		Set<String> expIdsMod = new HashSet<String>(expIds);

		// replace variables with their types
		List<String> varIds = cc.getVarQuant().getIds();
		List<String> varTypes = cc.getVarQuant().getTypes();

		for (String id: expIds) { 
			int index = varIds.indexOf(id); 
			if (index != -1) { 
				expIdsMod.remove(id);  
				expIdsMod.add(varTypes.get(index)); 
			}
		}

		// select ltl engines that declare all of the expression's atoms
		Set<LtlEngine> acceptableEngines = new HashSet<LtlEngine>(ltlEngines); 
		for (LtlEngine eng: ltlEngines) { 
			if (!eng.declaresAtoms().containsAll(expIdsMod)) { 
				acceptableEngines.remove(eng); 
			}
		}

		if (acceptableEngines.size() > 1) 
			throw new UnsupportedOperationException("Ambiguous ltl engine, stopping verification");

		if (acceptableEngines.size() < 1) 
			throw new UnsupportedOperationException("Appropriate ltl engine not found, stopping verification");

		return (LtlEngine) acceptableEngines.toArray()[0];
	}

	/**
	 * Find variable and function IDs in an expression. 
	 * @param e expression
	 * @return set of IDs
	 */
	private Set<String> findIdsInExpression (Expression e) { 
		if (e instanceof AndOrExpression) {
			AndOrExpression ce = ((AndOrExpression) e);
			Set<String> left = findIdsInExpression(ce.getLeft());
			left.addAll( findIdsInExpression(ce.getRight()));
			return left;
		} else if (e instanceof LTLExpression) { 
			LTLExpression ce = ((LTLExpression) e);
			if (ce.getUnop() != null) { 
				return findIdsInExpression(ce.getExpression());
			} else if (ce.getBinop() != null) { 
				Set<String> left = findIdsInExpression(ce.getLeft());
				left.addAll(findIdsInExpression(ce.getRight()));
				return left;
			} else 
				throw new UnsupportedOperationException("LTL expression doesn't have an operation: " + ce);

		} else if (e instanceof ComparisonExpression) {
			ComparisonExpression ce = ((ComparisonExpression) e);
			Set<String> left = findIdsInExpression(ce.getLeft());
			left.addAll(findIdsInExpression(ce.getRight()));
			return left;
		} else if (e instanceof BooleanNegation) {
			return findIdsInExpression(((BooleanNegation)e).getExpression());
		} else if (e instanceof ArithmeticSigned) { 
			return findIdsInExpression(((ArithmeticSigned)e).getExpression()); 
		} else if (e instanceof Addition) {
			Addition ce = ((Addition) e);
			Set<String> left = findIdsInExpression(ce.getLeft());
			left.addAll(findIdsInExpression(ce.getRight()));
			return left;
		} else if (e instanceof Multiplication) {
			Multiplication ce = ((Multiplication) e);
			Set<String> left = findIdsInExpression(ce.getLeft());
			left.addAll(findIdsInExpression(ce.getRight()));
			return left;
		} else if (e instanceof IntLiteral) {
			return new HashSet<String>();
		} else if (e instanceof FloatLiteral) {
			return new HashSet<String>();
		} else if (e instanceof BooleanLiteral) {
			return new HashSet<String>();
		} else if (e instanceof QFGTMREF) { 
			QFGTMREF ce = (QFGTMREF) e; 
			EList<String> ids = ce.getIds();
			Set<String> set = new HashSet<String>();
			switch(ids.size()) { 
			case 1: 
				// a variable identifier
				set.add(ids.get(0));
				break; 
			case 2: 
				// a variable and a property
				set.add(ids.get(0));
				set.add(ids.get(1));
				break;
			default: 
				throw new UnsupportedOperationException("LTL engine search handles QFGTMREFs with only 1 or 2 parts, not " + ids.size());
			}
			return set;
		} else if (e instanceof FunctionalExpression) {
			Set<String> set = new HashSet<String>();

			FunctionalExpression ce = ((FunctionalExpression) e);
			List<String >funcIds = ce.getFunc().getIds(); 
			if (funcIds.size() == 1) { 
				set.add(funcIds.get(0));
			} else if (funcIds.size() == 2) {
				set.add(funcIds.get(0));
				set.add(funcIds.get(1));
			} else 
				throw new UnsupportedOperationException("LTL engine search handles functions with QFGTMREF of 1 or 2 parts, not " + funcIds.size());

			for (Expression ex: ce.getArgs()) { 
				set.addAll(findIdsInExpression(ex));
			}

			return set; 
		}
		return new HashSet<String>();
	}
}
