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

package org.osate.xtext.aadl2.contracts.contract.linking;

import java.util.Collections;
import java.util.List;

import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.xtext.linking.impl.IllegalNodeException;
import org.eclipse.xtext.nodemodel.INode;
import org.osate.aadl2.Aadl2Package;
import org.osate.aadl2.AadlPackage;
import org.osate.aadl2.AnnexLibrary;
import org.osate.aadl2.DefaultAnnexLibrary;
import org.osate.aadl2.Element;
import org.osate.aadl2.PackageSection;
import org.osate.aadl2.modelsupport.util.AadlUtil;
import org.osate.aadl2.util.Aadl2Util;
import org.osate.xtext.aadl2.contracts.Contract.AnalysisContract;
import org.osate.xtext.aadl2.contracts.Contract.AnalysisLibrary;
import org.osate.xtext.aadl2.contracts.Contract.ContractPackage;
import org.osate.xtext.aadl2.properties.linking.PropertiesLinkingService;
import org.osate.xtext.aadl2.properties.util.EMFIndexRetrieval;

public class ContractLinkingService extends PropertiesLinkingService {

	public ContractLinkingService(){
		super();
	}

	@Override
	public List<EObject> getLinkedObjects(EObject context,
			EReference reference, INode node) throws IllegalNodeException {
		final EClass requiredType = reference.getEReferenceType();
		EObject searchResult = null;
		if (requiredType == null)
			return Collections.<EObject> emptyList();
		Element cxt = (Element) context;
		final String name = getCrossRefNodeAsString(node);

		if (ContractPackage.eINSTANCE.getAnalysisLibrary() == requiredType) {
			// first look it up in global index
			EObject gobj = getIndexedObject(context, reference, name);
			if (gobj != null ){
				if( gobj.eClass() == requiredType){
					return Collections.singletonList(gobj);
				} else {
					System.out.println("Global lookup of type did not match "+name);
				}
			}
			searchResult = findAnalysisLibrary(context, name);

			// alternative:
			//		String packName = Aadl2Util.getPackageName(name);
			//		String itemName = Aadl2Util.getItemNameWithoutQualification(name);
			//		AadlPackage ap = findAadlPackageReference(packName, AadlUtil.getContainingPackageSection(context));
			//		if (ap == null)
			//			return null;
			//		PackageSection ps = ap.getOwnedPublicSection();
			//		EList<AnnexLibrary>all=ps.getOwnedAnnexLibraries();
			//		for (AnnexLibrary al : all){
			//			if (al instanceof FGMLibrary){
			//				// find in FGMLibrary
			//				return (FeatureMappingset)AadlUtil.findNamedElementInList(((FGMLibrary)al).getFeaturemappingset(), itemName);
			//			}
			//		}
			//		return null;

		} else  if (ContractPackage.eINSTANCE.getAnalysisContract() == requiredType) {
			String packName = Aadl2Util.getPackageName(name);
			String itemName = Aadl2Util.getItemNameWithoutQualification(name);
			AadlPackage ap = findAadlPackageReference(packName, AadlUtil.getContainingPackageSection(context));
			if (ap == null)
				return Collections.<EObject> emptyList();
			PackageSection ps = ap.getOwnedPublicSection();
			EList<AnnexLibrary>all=ps.getOwnedAnnexLibraries();
			for (AnnexLibrary al : all){
				if (al instanceof DefaultAnnexLibrary){
					AnnexLibrary parsedLib = ((DefaultAnnexLibrary)al).getParsedAnnexLibrary();

					// find a library, convert to contract, see if name matches
					if (parsedLib instanceof AnalysisLibrary){
						for (AnalysisContract ac: ((AnalysisLibrary)parsedLib).getContracts()) {
							if (ac.getName().equals(itemName)) {
								searchResult = ac;
								break;
							}
						}
					}
				}
			}
		} else  if (ContractPackage.eINSTANCE.getAnalysisSubclause() == requiredType) {

		}

		if (searchResult != null) {
			return Collections.singletonList(searchResult);
		}

		return Collections.<EObject> emptyList();
	}

	public AnalysisLibrary findAnalysisLibrary(EObject context, String name){
		AnalysisLibrary eml = (AnalysisLibrary) EMFIndexRetrieval.getEObjectOfType(context, ContractPackage.eINSTANCE.getAnalysisLibrary(), name+"::contract");
		if (eml != null) 
			return eml;

		AadlPackage ap = findAadlPackageReference(name, AadlUtil.getContainingPackageSection(context));
		if (ap == null)
			return null;

		PackageSection ps = ap.getOwnedPublicSection();
		EList<AnnexLibrary>all=ps.getOwnedAnnexLibraries();
		for (AnnexLibrary al : all){
			if (al instanceof AnalysisLibrary){
				AnalysisLibrary anl = (AnalysisLibrary)al;
				if(anl.getName().equals(name))
					return anl;
			}
		}
		return null;
	}



}
