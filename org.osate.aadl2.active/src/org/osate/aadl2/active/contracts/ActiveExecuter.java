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

import java.io.Serializable;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.IProgressService;
import org.osate.aadl2.active.interfaces.AadlAnalysisWrapper;
import org.osate.aadl2.active.ui.ContractGraphWindow;
import org.osate.ui.dialogs.Dialog;
import org.osate.xtext.aadl2.contracts.Contract.AnalysisContract;

public class ActiveExecuter implements Serializable {

	private static final long serialVersionUID = 2513597299945228842L;
	private ActiveVerifier verificationCtrl = new ActiveVerifier();
	private boolean lastVerificationResult; // have to use a field to communicate between runnables
	private List<AnalysisContract> analysisList; // sequence of analyses under execution
	private AnalysisContract currentAnalysis; // analysis currently execution
	private List<IJobChangeListener> listeners = new ArrayList<IJobChangeListener>(); 
	private String dialogOutput; // analysis execution log to show user

	/**
	 * A job listener to track analysis executions.
	 * @author ivan
	 */
	class AnalysisJobChangeListener implements IJobChangeListener {

		private String jobName; 
		public AnalysisJobChangeListener(String jobName) { 
			this.jobName = jobName; 
		}

		@Override
		public void done(IJobChangeEvent event) {
			// TODO Auto-generated method stub
			if (event.getJob().getName().equals(jobName)) { 
				System.out.println("caught done " + event.getJob());

				dialogOutput += currentAnalysis.getName() + " executed, status: " 
						+ event.getResult().getMessage() +  ".\n";
				// need to switch to the UI thread to use progress service
				PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
					@Override
					public void run() {

						// verify guarantee
						boolean res = false; 
						try {
							res = verifyGuarantees(currentAnalysis); 
						} catch (InterruptedException e) {
							System.out.println("Interrupted: " + e.getMessage());
						}

						if(res) 
							executeNextAnalysis();
						else  
							reportResultAndCleanUp();
					}
				});
			}
		}
		
		@Override
		public void aboutToRun(IJobChangeEvent event) {}

		@Override
		public void awake(IJobChangeEvent event) { }

		@Override
		public void running(IJobChangeEvent event) {}

		@Override
		public void scheduled(IJobChangeEvent event) {}

		@Override
		public void sleeping(IJobChangeEvent event) {}
	}


	/**
	 * Show a window with an analysis graph. 
	 * @param analyses set of analyses to put into a graph
	 */
	public void displayAnalyses(final Set<AnalysisContract> analyses) {

		ContractGraphWindow window = new ContractGraphWindow() {
			public void analysisSequenceSelected(final List<AnalysisContract> lst) {
				executeAnalysesSequence(lst);
			}
		};
		window.displayAnalyses(analyses);
	}

	/**
	 * Verify and execute a sequence of analyses. Will be called from the UI thread. 
	 * @param analysesList sequence of analyses
	 */
	protected void executeAnalysesSequence(final List<AnalysisContract> analysesSelected/*, IProgressMonitor pm*/) {

		// prepare for execution
		analysisList = analysesSelected;
	
		dialogOutput = "Goal: execute " + analysisList.get(analysisList.size()-1).getName() + ".\n\n";
		executeNextAnalysis(); // this starts a sequence of executions
	}

	/*
	 * Continue with the execution of analysis sequence. Expects to be run from a UI thread. 
	 */
	private void executeNextAnalysis() { 
		if(analysisList.isEmpty()) {
			reportResultAndCleanUp();
			return; 
		}

		currentAnalysis = analysisList.remove(0);
		AadlAnalysisWrapper wrapper = createAnalysisWrapper(currentAnalysis);
		
		// alternative: add a cmd listener
		//		ICommandService cmdService = (ICommandService) PlatformUI.getWorkbench()
		//				.getService(ICommandService.class);
		//		cmdService.addExecutionListener(new AnalysisExecutionListener(
		//				body.getJobName()));

		// verify assumptions first
		boolean res = false; 
		try {
			res = verifyAssumptions(currentAnalysis); 
		} catch (InterruptedException e) {
			System.out.println("Interrupted: " + e.getMessage());
		}

		if (!res) { 
			reportResultAndCleanUp(); 
			return; 
		}

		// start listening to the job terminations, if this is analysis contains a job 
		if(wrapper.getJobName() != null) {
			IJobManager manager = Job.getJobManager(); 
			IJobChangeListener listener = new AnalysisJobChangeListener(wrapper.getJobName()); 
			listeners.add(listener);
			manager.addJobChangeListener(listener);
		}

		// execute analysis
		if (wrapper != null)
			wrapper.run();

		
		// after this, either the listener will pick up the job termination and verify guarantees
		// or we explicitly invoke the guarantees
		if(wrapper.getJobName() == null) {
			dialogOutput += currentAnalysis.getName() + " executed.\n";
			
			// verify guarantee
			res = false; 
			try {
				res = verifyGuarantees(currentAnalysis); 
			} catch (InterruptedException e) {
				System.out.println("Interrupted: " + e.getMessage());
			}

			if(res) 
				executeNextAnalysis();
			else  
				reportResultAndCleanUp();
		}
	}

	/*
	 * Verifies assumptions of a given analysis. Expects to be called from a UI thread.
	 */
	private boolean verifyAssumptions(final AnalysisContract ac) throws InterruptedException { 
		IWorkbench wb = PlatformUI.getWorkbench();
		IProgressService ps = wb.getProgressService();
		try {
			// launch a separate non-UI thread for analysis verification
			// alternatives:
			// ps.run(true, true, new IRunnableWithProgress() {
			// ps.runInUI(ps, new IRunnableWithProgress() {
			ps.busyCursorWhile(new IRunnableWithProgress() {
				@Override
				public void run(IProgressMonitor pm) throws InvocationTargetException, InterruptedException {

					String name = ac.getName();
					pm.subTask("Verifying assumptions of " + name);

					if(verificationCtrl.verifyAssumptions(ac, new SubProgressMonitor(pm, 1))) {
						System.out.println("Assumptions of " + name + " hold");
						dialogOutput += "* Assumptions of " + name + " hold.\n";
						lastVerificationResult = true;
					} else {
						System.out.println("Assumptions of " + name + " DO NOT hold, terminating");
						dialogOutput += "! Assumptions of " + name + " do not hold, execution stopped.";
						lastVerificationResult = false;
					}
				}
			});
		} catch (InvocationTargetException e) {
			e.printStackTrace(); // unwrap the cause of this exception 
			return false; 
		}

		return lastVerificationResult;
	}

	/*
	 * Verifies guarantees of a given analysis. Expects to be called from a UI thread.
	 */
	private boolean verifyGuarantees(final AnalysisContract ac) throws InterruptedException { 
		IWorkbench wb = PlatformUI.getWorkbench();
		IProgressService ps = wb.getProgressService();
		try {
			// launch a separate non-UI thread for analysis verification
			// alternatives:
			// ps.run(true, true, new IRunnableWithProgress() {
			// ps.runInUI(ps, new IRunnableWithProgress() {
			ps.busyCursorWhile(new IRunnableWithProgress() {
				@Override
				public void run(IProgressMonitor pm) throws InvocationTargetException, InterruptedException {

					String name = ac.getName();
					pm.subTask("Verifying guarantees of " + name);

					if(verificationCtrl.verifyGuarantees(ac, new SubProgressMonitor(pm, 1))) {
						System.out.println("Guarantees of " + name + " hold\n");
						dialogOutput += "* Guarantees of " + name + " hold.\n";
						lastVerificationResult = true;
					} else {
						System.out.println("Guarantees of " + name + " DO NOT hold, terminating");
						dialogOutput += "! Guarantees of " + name + " do not hold, execution stopped.";
						lastVerificationResult = false;
					}

				}
			});
		} catch (InvocationTargetException e) {
			e.printStackTrace(); // unwrap the cause of this exception 
			return false; 
		}

		return lastVerificationResult;
	}

	/* 
	 * Lookup and instantiate an analysis body for a contract
	 */
	private AadlAnalysisWrapper createAnalysisWrapper(AnalysisContract sc){
		// reflective load of a class
		AadlAnalysisWrapper b = null;
		try {
			Class analysisBodyClass = Class.forName("org.osate.aadl2.active.wrappers." + sc.getName/*getAnalysisName*/());
			b = (AadlAnalysisWrapper) analysisBodyClass.newInstance();
		} catch (InstantiationException e) {
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		}
		return b; 
	}

	/*
	 * Show a dialog and remove listeners.
	 */
	private void reportResultAndCleanUp() { 
		// clean up listeners that are no longer used
		IJobManager manager = Job.getJobManager(); 
		for (IJobChangeListener listener: listeners)  
			manager.removeJobChangeListener(listener);
		
		// report results to user
		Dialog.showInfo("Analysis Execution Log", dialogOutput);
	}

}