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

package org.osate.xtext.aadl2.contracts.contract.parsing;

//import edu.cmu.sei.osate.sublanguageexamplejava
import org.osate.aadl2.AnnexLibrary;
import org.osate.aadl2.AnnexSubclause;
import org.osate.aadl2.modelsupport.errorreporting.ParseErrorReporter;
import org.osate.annexsupport.AnnexParseUtil;
import org.osate.annexsupport.AnnexParser;
import org.osate.core.OsateCorePlugin;
import org.osate.xtext.aadl2.contracts.parser.antlr.ContractParser;
import org.osate.xtext.aadl2.contracts.services.ContractGrammarAccess;
import org.osate.xtext.aadl2.contracts.ui.internal.ContractActivator;

import com.google.inject.Injector;

public class ContractAnnexParser implements AnnexParser { 
	// Need to get aadl resources for resolving components
	// For resolving package names etc
	
    protected Injector injector ;//= OsateCorePlugin.getDefault().getInjector("org.osate.xtext.aadl2.featuregroupmapping.FeatureGroupMapping");

	private ContractParser fgmParser ;
	
	protected Injector getInjector(){
		if (injector == null){
			// should be the same as MyDslActivator.ORG_OSATE_XTEXT_AADL2_MYDSL);
			injector = OsateCorePlugin.getDefault().getInjector(ContractActivator.ORG_OSATE_XTEXT_AADL2_CONTRACTS_CONTRACT);
		}
		return injector;
	}

	protected  ContractParser getParser() {
			if (fgmParser == null) {
				fgmParser = getInjector().getInstance(ContractParser.class);
			}
		return fgmParser;
	}

	protected  ContractGrammarAccess getGrammarAccess() {
		return getParser().getGrammarAccess();
	}
	
	public AnnexLibrary parseAnnexLibrary
			(
				String annexName, String source,
				String filename, int line, int column, ParseErrorReporter errReporter
			) {
		AnnexLibrary eal = (AnnexLibrary) AnnexParseUtil.parse(getParser(),source,getGrammarAccess().getAnalysisLibraryRule(),filename,line,column, errReporter);
		return eal;
	 }

	public AnnexSubclause parseAnnexSubclause
			(
				String annexName, String source, String filename, 
				int line, int column, ParseErrorReporter errReporter
			) {// put in my root rule  
		AnnexSubclause eas = (AnnexSubclause) AnnexParseUtil.parse(getParser(),source,getGrammarAccess().getAnalysisSubclauseRule(),filename,line,column, errReporter);
		 return eas;
	 }



}