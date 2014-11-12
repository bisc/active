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

package org.osate.xtext.aadl2.contracts.ui.highlighting;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.Keyword;
import org.eclipse.xtext.RuleCall;
import org.eclipse.xtext.TerminalRule;
import org.eclipse.xtext.nodemodel.INode;
import org.eclipse.xtext.nodemodel.util.NodeModelUtils;
import org.osate.aadl2.AnnexLibrary;
import org.osate.aadl2.AnnexSubclause;
import org.osate.annexsupport.AnnexHighlighter;
import org.osate.annexsupport.AnnexHighlighterPositionAcceptor;
import org.osate.annexsupport.AnnexUtil;

public class ContractHighlighter implements AnnexHighlighter {

	@Override
	public void highlightAnnexLibrary(AnnexLibrary library,
			AnnexHighlighterPositionAcceptor acceptor) {
		doHighlighting(library, acceptor); 

	}

	@Override
	public void highlightAnnexSubclause(AnnexSubclause subclause,
			AnnexHighlighterPositionAcceptor acceptor) {
		// TODO exclude colons? 

		
		doHighlighting(subclause, acceptor); 
	}

	private void doHighlighting(EObject annexObject, AnnexHighlighterPositionAcceptor acceptor) { 
		// do highlighting much like in the normal case
		EObject parsedAnnexObject = AnnexUtil.getParsedAnnex(annexObject);
		if (parsedAnnexObject == null) return ;
		INode annexnode = NodeModelUtils.getNode(parsedAnnexObject);
		if (annexnode == null) {
			return;
		}
		INode root = annexnode.getRootNode();
		final int annexTextLength = AnnexUtil.getSourceText(annexObject).length();
		final int annexTextOffset = AnnexUtil.getAnnexOffset(annexObject);
		for (INode node : root.getAsTreeIterable()) {
			EObject ge = node.getGrammarElement();
			if (ge instanceof RuleCall) {
				ge = ((RuleCall) ge).getRule();
			}

			if (ge instanceof Keyword)
			{
				int offset = node.getOffset()-annexTextOffset;
				
				String keywordValue = ((Keyword) ge).getValue();
				if(annexObject instanceof AnnexSubclause && 
						keywordValue.equalsIgnoreCase("::"))
					continue;
				/*		if(offset < 0 && keywordValue.equalsIgnoreCase(ANNEXTEXTKEYWORD))
							continue;
						if(offset > annexTextLength && keywordValue.equalsIgnoreCase(SEMICOLONKEYWORD))
							continue;
				 */
				// adjust for added whitespace in front of annex text
				acceptor.addPosition(offset, node.getLength(), 
						AnnexHighlighterPositionAcceptor.KEYWORD_ID);
			} else if (ge instanceof TerminalRule) {
				// highlighting our special type of comment
				if (((TerminalRule)ge).getName().equalsIgnoreCase("AADL_SL_COMMENT")){
					// adjust for added whitespace in front of annex text
					acceptor.addPosition(node.getOffset()-annexTextOffset, node.getLength(), 
							AnnexHighlighterPositionAcceptor.COMMENT_ID);
				} else if (((TerminalRule)ge).getName().equalsIgnoreCase("STRING")){
					// adjust for added whitespace in front of annex text
					acceptor.addPosition(node.getOffset()-annexTextOffset, node.getLength(), 
							AnnexHighlighterPositionAcceptor.STRING_ID);
				}
			} 
		}		
	}

}
