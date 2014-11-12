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

package org.osate.aadl2.active.verificationengine.sched;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
import org.osate.aadl2.active.Activator;
import org.osate.aadl2.active.common.ContractUtils;
import org.osate.aadl2.active.interfaces.LtlEngine;
import org.osate.aadl2.active.interfaces.UnnecessaryVerificationException;
import org.osate.aadl2.active.interfaces.VariableAssignment;
import org.osate.xtext.aadl2.contracts.Contract.AnalysisContract;
import org.osate.xtext.aadl2.contracts.Contract.ContractClause;

import com.google.common.io.Files;

public class SchedSpinEngine implements LtlEngine {

	private Set<String> atoms = new HashSet<String>();
	private SchedSpinGenerator gen; 
	private String workingDirPath, workingTemplateFilePath;

	final private String outputFilename = "sched-spin-verification-output.txt";

	public SchedSpinEngine() {
		atoms.add("CanPreempt");
		atoms.add("thread");
		atoms.add("Deadline");
		atoms.add("Period");
		atoms.add("Priority");
		atoms.add("Compute_Execution_Time");

		gen = new SchedSpinGenerator();

		String homePath = ResourcesPlugin.getWorkspace().getRoot().getLocation().toString();
		new java.io.File(homePath, "contract-workdata").mkdirs();
		workingDirPath = homePath + "/contract-workdata/";
	}

	@Override
	public String getName() {
		return "sched";
	}

	public boolean verify(AnalysisContract ac, ContractClause cc, VariableAssignment values, String filename) {

		if(!createNewTemplate(filename))
			return false;

		// generate the program and make the substitutions
		try { 
			ContractUtils.replaceStringsInFile(workingTemplateFilePath, 
					gen.generateProgramSubstitution(cc, values));
		} catch (UnnecessaryVerificationException e) { 
			System.out.println("Sched spin: " + e.getMessage());
			return true;
		}

		// prepare the program 
		File workingDir = new File(workingDirPath);
		String outputFilePath = workingDirPath + outputFilename;

		String prepareCommand = "spin -a " + filename;
		String prepareResult = ContractUtils.executeShellCommand(prepareCommand, workingDir);
		ContractUtils.writeToFile(outputFilePath, prepareResult, false); // create a new output file
		if (prepareResult.toLowerCase().contains("error")) { 
			System.out.println("Sched spin: error of sched spin generation, stopping verification: " + prepareResult);
			return false; 
		}

		// compile the program
		String compileCommand = "gcc -DCOLLAPSE -DMEMLIM=6000 pan.c";
		String compileResult = ContractUtils.executeShellCommand(compileCommand, workingDir);
		ContractUtils.writeToFile(outputFilePath, compileResult, true); 
		if (compileResult.toLowerCase().contains("error")) { 
			System.out.println("Sched spin: error of sched spin compilation, stopping verification: " + compileResult);
			return false; 
		}

		// call the verifier
		String verifyCommand = "./a.out -a -b -m10000000 -N";
		String verifyResult = ContractUtils.executeShellCommand(verifyCommand, workingDir);
		ContractUtils.writeToFile(outputFilePath, verifyResult, true);
		if (verifyResult.toLowerCase().contains("assertion violated")) { 
			System.out.println("Sched spin: assertion violated in spin verification: " + verifyResult);
			return false; 
		}

		System.out.println("Sched spin: Ltl contract holds");
		return true;
	}

	// create copies of template files for scheduling domain model
	private boolean createNewTemplate(String filename) {
		workingTemplateFilePath = workingDirPath + filename;
		String workingUtilFilePath = workingDirPath + "sched-util.pml";

		try {
			URL templateUrl = FileLocator.toFileURL(Platform.getBundle(Activator.PLUGIN_ID).
					getResource("res/sched/sched-model-template.pml"));
			URL utilUrl = FileLocator.toFileURL(Platform.getBundle(Activator.PLUGIN_ID).
					getResource("res/sched/sched-util.pml"));

			Files.copy(new File(templateUrl.getPath()), new File(workingTemplateFilePath));
			Files.copy(new File(utilUrl.getPath()), new File(workingUtilFilePath));
		} catch (IOException e) {
			System.out.println("Sched spin: couldn't create a working file");
			e.printStackTrace();
			return false;
		}

		return true;
	}

	@Override
	public Set<String> declaresAtoms() {
		return atoms;
	}

}
