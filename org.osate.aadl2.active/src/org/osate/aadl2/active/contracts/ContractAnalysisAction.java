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

import org.eclipse.core.runtime.IProgressMonitor;
import org.osate.aadl2.AadlPackage;
import org.osate.aadl2.Element;
import org.osate.aadl2.active.common.DBConnector;
import org.osate.aadl2.active.db.QueryConstructorProcessingSwitch;
import org.osate.aadl2.instance.SystemInstance;
import org.osate.aadl2.modelsupport.resources.OsateResourceUtil;
import org.osate.ui.actions.AaxlReadOnlyActionAsJob;
import org.osate.ui.dialogs.Dialog;

public class ContractAnalysisAction extends AaxlReadOnlyActionAsJob {

	ActiveExecuter executionCtrl = new ActiveExecuter();

	public ContractAnalysisAction() {
		super();
	}

	@Override
	protected String getActionName() {
		return "Carrying out contract analysis...";
	}

	@Override
	protected void doAaxlAction(IProgressMonitor monitor, Element obj) {
		monitor.beginTask("Preparing for contract analysis", 3);
		OsateResourceUtil.refreshResourceSet();
		System.out.println("\nStarting out contract analysis on " + obj);
		Element declRoot; // where to start traversal; has to be a declarative
							// model element

		try {
			if (obj instanceof SystemInstance) {
				// called on an instance model, need to generate a database
				SystemInstance si = (SystemInstance) obj;

				monitor.subTask("Collecting database information from AADL");
				QueryConstructorProcessingSwitch sw = new QueryConstructorProcessingSwitch();
				sw.processPreOrderAll(si);
				monitor.worked(1);
				if (monitor.isCanceled())
					throw new InterruptedException(
							"Contract preparation was cancelled");

				monitor.subTask("Cleaning database information");
				DBConnector db = new DBConnector();
				db.connect();
				db.cleanDB();
				monitor.worked(1);
				if (monitor.isCanceled())
					throw new InterruptedException(
							"Contract preparation was cancelled");

				monitor.subTask("Creating an AADL database");
				//System.out.println("query = " + sw.getInstanceQuery());
				int result = db.executeUpdateQueries(sw.getInstanceQuery());

				if (result != 0) {
					Dialog.showInfo("DB Generation",
							"There was an issue generating the database, stopping.");
					return;
				}

				System.out.println("DB generated successfully");
				// Classifier cl =
				// si.getComponentClassifier().getAllAnnexSubclauses;
				declRoot = si.getComponentClassifier().getElementRoot();
				// this jumps to the declarative hierarchy and returns package ref
				// caution: the properties only at this level and below are
				// visible; top levels aren't integrated yet.
				// so only take property values from the instance model

			} else if (obj instanceof AadlPackage) {
				System.out.println("It's an aadl package of types");
				declRoot = obj;
			} else
				throw new UnsupportedOperationException(
						"Unknown object of action: " + obj);

			monitor.worked(1);
			if (monitor.isCanceled())
				throw new InterruptedException(
						"Contract preparation was cancelled");

			monitor.subTask("Collecting and displaying analyses");
			// traverse the model to search and display analyses
			ContractAnalysisProcessingSwitch contractSwitch = new ContractAnalysisProcessingSwitch();
			contractSwitch.defaultTraversal(declRoot);

			executionCtrl.displayAnalyses(contractSwitch.getFoundAnalyses());
			monitor.done();
		} catch (InterruptedException e) {
			System.out.println(e.getMessage());
		}
	}
}
