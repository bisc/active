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

package org.osate.aadl2.active.wrappers;

import org.eclipse.core.commands.Category;
import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.NotEnabledException;
import org.eclipse.core.commands.NotHandledException;
import org.eclipse.core.commands.common.NotDefinedException;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.osate.aadl2.active.interfaces.AadlAnalysisWrapper;

public class BinPackingAnalysis implements AadlAnalysisWrapper {

	final private String categoryId = "org.osate.analysis.resource.management.commands"; 
	final private String commandId = "org.osate.analysis.resource.management.commands.Binpack"; 
	final private String jobName = "Bind threads to processors"; 
	
	@Override
	public void run() {
		System.out.println("Inside binpacking analysis");

		Display.getDefault().asyncExec(new Runnable() {
			@Override
			public void run() {
				// call the analyze decl model from that.
				// also try calling the command
				ICommandService cmdService = (ICommandService) PlatformUI
						.getWorkbench().getService(ICommandService.class);
				Category binpackCategory = cmdService.getCategory(categoryId);
				
				if (!binpackCategory.isDefined()) 
					throw new UnsupportedOperationException("Cannot find command category org.osate.analysis.resource.management.commands");
				
				Command binpackCommand = cmdService.getCommand(commandId);
				
				if (!binpackCommand.isDefined()) 
					throw new UnsupportedOperationException("Cannot find command category org.osate.analysis.resource.management.commands");
				
				try {
					binpackCommand.executeWithChecks(new ExecutionEvent());
				} catch (ExecutionException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				} catch (NotDefinedException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				} catch (NotEnabledException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				} catch (NotHandledException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
			} 
			
		});
	}

	@Override
	public String getJobName() {
		return jobName;
	}

}
