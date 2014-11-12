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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.ResourcesPlugin;
import org.osate.aadl2.active.common.ContractUtils;
import org.osate.aadl2.active.common.VariableAssignmentHashMap;
import org.osate.aadl2.active.interfaces.SmtEngine;
import org.osate.aadl2.active.interfaces.VariableAssignment;
import org.osate.xtext.aadl2.contracts.Contract.AnalysisContract;
import org.osate.xtext.aadl2.contracts.Contract.ContractClause;
import org.osate.xtext.aadl2.contracts.Contract.QuantClause;

public class Z3Engine implements SmtEngine {

	private String workingDir;
	private String pathToFile;

	public Z3Engine() {
		String homePath = ResourcesPlugin.getWorkspace().getRoot().getLocation().toString();//System.getProperty("user.home");
		new java.io.File(homePath, "contract-workdata").mkdirs();
		workingDir = homePath + "/contract-workdata/";// TODO make a temporary dir?
	}

	public boolean verify(AnalysisContract ac, ContractClause cc, String filename) {
		pathToFile = workingDir + filename;
		ContractUtils.writeToFile(pathToFile, generateSmtOutputForClause(ac, cc, true) + "\n(check-sat)\n", false);

		//	if (limits == null)
		//	    ContractUtils.writeToFile(pathToFile, generateSmtOutputForClause(ac, cc, true) + "(check-sat)\n");
		//	else 
		//	    throw new UnsupportedOperationException("Need to add limits to the smt formula");

		String verResult = ContractUtils.executeShellCommand("z3 -smt2 " + pathToFile, null);
		verResult = verResult.replaceAll("\\s+", ""); // remove whitespace

		if (verResult.equals("unsat")) {
			System.out.println("Verification result: contract fulfilled");
			return true;
		} else if (verResult.equals("sat")) {
			System.out.println("Verification result: contract not fulfilled");
			return false;
		} else if (verResult.startsWith("(error")) { 
			System.out.println("Verification result: error in smt program, contract not fulfilled " + verResult);
			return false;
		} else 
			throw new UnsupportedOperationException("SMT returned " + verResult + ", which is not an expected anwer");
	}

	public List<VariableAssignment> findModelsForSuchThat(AnalysisContract ac, ContractClause cc, String filename) {
		pathToFile = workingDir + filename;
		// need to tell generator to use suchThat -- not Holds
		String rawSmt = generateSmtOutputForClause(ac, cc, false);
		QuantClause qc = cc.getVarQuant();
		//	Expression suchThat = cc.getSuchThat();

		List<VariableAssignment> models = new ArrayList<VariableAssignment>();

		if (qc == null)
			throw new UnsupportedOperationException("Cannot find models for non-quantified formulas");

		// create valuation lines for quantified variables
		String evalsOutput = "";
		List<String> variableNames = new ArrayList<String>();
		Iterator<String> variableIt = qc.getIds().iterator();

		while (variableIt.hasNext()) {
			String varName = variableIt.next();
			String evalStr = "(eval " + varName + ")\n";
			evalsOutput += evalStr;
			variableNames.add(varName);
		}

		if (evalsOutput.length() == 0)
			throw new UnsupportedOperationException("Cannot find models for non-quantified formulas");

		// model search loop
		while (true) {
			ContractUtils.writeToFile(pathToFile, rawSmt + "(check-sat)\n" + evalsOutput, false);
			String[] outputLines = ContractUtils.executeShellCommand("z3 -smt2 " + pathToFile, null).split("\n");

			// process SMT output
			if (outputLines[0].equals("unsat")) {
				System.out.println("No more models, stopping search");
				break;
			} else if (outputLines[0].equals("sat")) {
				System.out.println("Model found, continuing search");
			} else if (outputLines[0].startsWith("(error")) { 
				throw new UnsupportedOperationException("Error in smt program: " + outputLines[0]);
			} else 
				throw new UnsupportedOperationException("Smt output unreadable: " + outputLines[0]);

			if (outputLines.length != variableNames.size() + 1)
				throw new UnsupportedOperationException("The number of free variables doesn't match SMT output");

			// add restrictions for previous models
			VariableAssignment model = new VariableAssignmentHashMap();
			String restrictions = "(assert (not (and ";
			for (int l = 1; l < outputLines.length; l++) {
				restrictions += "(= " + variableNames.get(l - 1) + " " + outputLines[l] + ") ";
				model.put(variableNames.get(l - 1), outputLines[l]);
			}
			models.add(model);
			restrictions += ")))\n";
			rawSmt += restrictions;
		}
		return models;
	}

	private String generateSmtOutputForClause(AnalysisContract ac, ContractClause cc, boolean verifyOrFind) {
		ContractToSmtGenerator contractToSmtGen = new ContractToSmtGenerator();
		System.out.println("Generating smt...");
		return contractToSmtGen.generateSmtForClause(ac, cc, verifyOrFind);
	}


}
