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

package org.osate.aadl2.active.ui;

import java.awt.Color;
import java.awt.Font;
import java.awt.GraphicsEnvironment;
import java.awt.Rectangle;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.swt.SWT;
import org.eclipse.swt.awt.SWT_AWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.jgrapht.ext.JGraphXAdapter;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.ListenableDirectedGraph;
import org.jgrapht.traverse.BreadthFirstIterator;
import org.osate.aadl2.active.common.ContractUtils;
import org.osate.xtext.aadl2.contracts.Contract.AnalysisContract;
import org.osate.xtext.aadl2.contracts.Contract.QFGTMREF;

import com.mxgraph.layout.mxFastOrganicLayout;
import com.mxgraph.model.mxGeometry;
import com.mxgraph.model.mxICell;
import com.mxgraph.swing.mxGraphComponent;
import com.mxgraph.util.mxConstants;
import com.mxgraph.util.mxRectangle;
import com.mxgraph.view.mxStylesheet;

/**
 * Displays analyses and calls back a method when one was selected
 * 
 * @author ivan
 */
public abstract class ContractGraphWindow {

	private AnalysisContractGraph acGraph; // a graph of analyses

	//JGraphModelAdapter vs JGraphXAdapter
	private JGraphXAdapter<AnalysisContractNode, ContractDependencyEdge> jgxAdapter;
	// private JFrame graphView;
	private Shell shell;

	/**
	 * a convenience wrapper class for a graph of analyses
	 * 
	 * @author ivan
	 */
	public class AnalysisContractGraph
			extends
			ListenableDirectedGraph<AnalysisContractNode, ContractDependencyEdge> {
		private static final long serialVersionUID = -4595141737107824798L;

		public AnalysisContractGraph() {
			super(ContractDependencyEdge.class);
		}
	}

	public class ContractDependencyEdge extends DefaultEdge {
		private String label;

		public ContractDependencyEdge(String label) {
			this.label = label;
		}

		public String toString() {
			return label;
		}
	}

	/**
	 * a callback method to call when an analyses (and its dependencies) were
	 * selected
	 * 
	 * @param lst
	 *            sequence of analyses
	 */
	public abstract void analysisSequenceSelected(List<AnalysisContract> lst);

	/**
	 * Display a set of analyses in a frame
	 */
	public void displayAnalyses(Set<AnalysisContract> analyses) {
		// init the graph data structures
		acGraph = new AnalysisContractGraph();

		for (AnalysisContract ac : analyses) {
			// add to graph
			acGraph.addVertex(new AnalysisContractNode(ac, ac
					.getName/* getAnalysisName */()));
		}

		// check the dependency between each pair of nodes
		for (AnalysisContractNode sc1 : acGraph.vertexSet()) {
			for (AnalysisContractNode sc2 : acGraph.vertexSet()) {
				Set<String> dependencySet = dependentOnVars(sc1.getAnalysisContract(),
						sc2.getAnalysisContract());
				
				if (sc1 != sc2 && !dependencySet.isEmpty()) {
					// generate edge label
					String label = ""; 
					for (String s: dependencySet) 
						label += s + ", ";
					
					label = label.substring(0, label.length()-2);
					acGraph.addEdge(sc1, sc2, new ContractDependencyEdge(label));
				}
			}
		}

		// create the graph interface in the main/UI thread of eclipse
		// use SWT_AWT to bridge from eclipse's SWT to Swing/AWT supported by
		// jgraphx
		PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
			@Override
			public void run() {
				// get SWT display and window primitives
				Display d = PlatformUI.getWorkbench().getDisplay();
				shell = new Shell(d, SWT.TITLE  | SWT.CLOSE
						| SWT.BORDER | SWT.RESIZE);
				shell.setText("Double-click an analysis to run");
				
				shell.setLayout(new FillLayout());
				
				Composite composite = new Composite(shell, SWT.EMBEDDED);
//				composite.setLayout(new FillLayout(SWT.VERTICAL));
//				composite.setSize(shell.getSize().x, shell.getSize().y);
//				composite.setLayoutData(new RowData(shell.getSize().x, shell.getSize().y));
//				composite.setLayoutData(new RowData(400, 600));
				
				java.awt.Frame frame = SWT_AWT.new_Frame(composite);
//				frame.setLayout(new BoxLayout(frame, BoxLayout.PAGE_AXIS));
				
				jgxAdapter = new JGraphXAdapter<AnalysisContractNode, ContractDependencyEdge>(
						acGraph);
				// styling the graph
				jgxAdapter.setCellsEditable(false);
				jgxAdapter.setAllowDanglingEdges(false);
				jgxAdapter.setAutoSizeCells(true);
				jgxAdapter.setCellsCloneable(false);
				jgxAdapter.setCellsDeletable(false);
				jgxAdapter.setCellsDisconnectable(false);
				jgxAdapter.setConnectableEdges(false);
				
				mxStylesheet stylesheet = jgxAdapter.getStylesheet();// new mxStylesheet();
				
				Map<String, Object> vertexStyle = stylesheet.getDefaultVertexStyle();
				vertexStyle.put(mxConstants.STYLE_FONTSIZE, 20);
				vertexStyle.put(mxConstants.STYLE_FONTCOLOR, "#000000"); // black
				vertexStyle.put(mxConstants.STYLE_FILLCOLOR, "#FFFFFF"); // white
				vertexStyle.put(mxConstants.STYLE_STROKECOLOR, "#003366"); // navy blue
				vertexStyle.put(mxConstants.STYLE_STROKEWIDTH, 2);
//				vertexStyle.put(mxConstants.STYLE_SPACING, 20);
				vertexStyle.put(mxConstants.STYLE_VERTICAL_LABEL_POSITION, mxConstants.ALIGN_MIDDLE);
				vertexStyle.put(mxConstants.STYLE_VERTICAL_ALIGN, mxConstants.ALIGN_MIDDLE);
				
				Map<String, Object> edgeStyle = stylesheet.getDefaultEdgeStyle();//new HashMap<String, Object>();
//				edgeStyle.put(mxConstants.STYLE_SHAPE, mxConstants.SHAPE_CONNECTOR);
				edgeStyle.put(mxConstants.STYLE_ENDARROW, mxConstants.NONE);
				edgeStyle.put(mxConstants.STYLE_STARTARROW, mxConstants.ARROW_CLASSIC); // invert arrows
				edgeStyle.put(mxConstants.STYLE_STROKECOLOR, "#FFCC00");// yellow FFCC00
				edgeStyle.put(mxConstants.STYLE_STROKEWIDTH, 2); 
				edgeStyle.put(mxConstants.STYLE_FONTCOLOR, "#000000"); // black
				edgeStyle.put(mxConstants.STYLE_STARTSIZE, 14); 
				
//				edgeStyle.put(mxConstants.STYLE_INDICATOR_COLOR, "#FF0000");
//				edgeStyle.put(mxConstants.STYLE_LABEL_BACKGROUNDCOLOR, "#EEEEEE"); // standard gray color
				edgeStyle.put(mxConstants.STYLE_LABEL_BACKGROUNDCOLOR, "none"); // make transparent
				edgeStyle.put(mxConstants.STYLE_FONTSIZE, 16);

				stylesheet.setDefaultVertexStyle(vertexStyle);
				stylesheet.setDefaultEdgeStyle(edgeStyle);
				jgxAdapter.setStylesheet(stylesheet);
				
				// adjust cell sizes for a larger font
				jgxAdapter.getModel().beginUpdate();
		        for (mxICell cell : jgxAdapter.getVertexToCellMap().values()) {
		        	mxGeometry cg = (mxGeometry)cell.getGeometry().clone();
		        	cg.setHeight(cg.getHeight() * 1.75);
		        	cg.setWidth(cg.getWidth() * 2);
		        	jgxAdapter.getModel().setGeometry(cell, cg);
		        }
		        jgxAdapter.getModel().endUpdate();
				
				// create a graph that calls analysisSelected when one of
				// analyses is double-clicked
				final mxGraphComponent graphComponent = new mxGraphComponent(
						jgxAdapter) {
					@Override
					protected void installDoubleClickHandler() {
						graphControl.addMouseListener(new MouseAdapter() {
							@Override
							public void mouseReleased(MouseEvent e) {
								if (!e.isConsumed() && isEditEvent(e)) {
									Object cell = getCellAt(e.getX(), e.getY(),
											false);
									if (cell != null /*
													 * &&
													 * getGraph().isCellEditable
													 * (cell)
													 */) {
										analysisSelected(cell);
									}
								}
							}
						});
					}
				};
				graphComponent.setDoubleBuffered(true); // not paint dirty
														// updates on screen
				frame.add(graphComponent);
				
				// limit graph size
				Rectangle winBounds = GraphicsEnvironment.getLocalGraphicsEnvironment()
						.getMaximumWindowBounds();
				jgxAdapter.setMaximumGraphBounds(new mxRectangle(0, 0, 
						winBounds.getWidth()-1, winBounds.getHeight()-1));
				
				shell.pack();
				shell.open();
				shell.setMaximized(true);
				
				// positioning via graph items with jgraphx layouts
				// fast organic layout option
				mxFastOrganicLayout layout = new mxFastOrganicLayout(jgxAdapter);
				layout.setForceConstant(450);
				layout.setMinDistanceLimit(20);
				layout.setMaxDistanceLimit(500);
				
				// circle layout option
				/*mxCircleLayout layout = new mxCircleLayout(jgxAdapter, 5);
				layout.setUseBoundingBox(true);
				layout.setX0(0);
				layout.setY0(0);
				layout.setRadius(5);
				layout.setMoveCircle(true);*/

				// organic layout option
				/*mxOrganicLayout layout = new mxOrganicLayout(jgxAdapter, new Rectangle(1200, 700));
				layout.setNodeDistributionCostFactor(70000);
				layout.setMinDistanceLimit(100);
				layout.setMaxDistanceLimit(500);*/
				
				layout.execute(jgxAdapter.getDefaultParent());
				
				// can also try if event loops are messed up:
				/*
				 * while (!shell.isDisposed()) { if (!d.readAndDispatch())
				 * d.sleep(); }
				 */
			}
		});
	}

	/**
	 * Handle the selection of analysis in the graph view
	 * 
	 * @param cell
	 */
	private void analysisSelected(Object cell) {
		// determine selected node
		AnalysisContractNode sn = jgxAdapter.getCellToVertexMap().get(cell);

		// if clicked but not on a vertex, then ignore
		if (sn == null)
			return;

		System.out.println("Analysis selected " + sn.getLabel());

		// kill the frame in UI/main thread and continue here
		PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
			@Override
			public void run() {
				shell.setVisible(false);
				shell.dispose();
			}
		});

		// determine the sequenced reachability set
		// traverse the graph breadth-first and use a stack to sequence analyses
		BreadthFirstIterator<AnalysisContractNode, ContractDependencyEdge> it = new BreadthFirstIterator<AnalysisContractNode, ContractDependencyEdge>(
				acGraph, sn);

		final List<AnalysisContract> analysesList = new ArrayList<AnalysisContract>();
		while (it.hasNext()) {
			analysesList.add(0, it.next().getAnalysisContract());
		}

		System.out.println("Found analyses sequence: " + analysesList);

		// execute the analyses sequence in UI/main thread because it's expected
		// for use of ProgressService
		PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
			@Override
			public void run() {
				analysisSequenceSelected(analysesList);
			}
		});
	}

	/**
	 * A helper method. Determines the dependency between the input of sc1 and
	 * output of sc2.
	 * 
	 * @param sc1
	 *            first contract
	 * @param sc2
	 *            second contract
	 * @return true if two contracts are dependent
	 */
	private Set<String> dependentOnVars(AnalysisContract sc1,
			AnalysisContract sc2) {
		Set<String> inputSet = new HashSet<String>(), outputSet = new HashSet<String>();

		for (QFGTMREF name : sc1.getInput().getNames()) {
			// assuming only two-part names
			if (name.getIds().size() > 2)
				throw new UnsupportedOperationException(
						"Only support QFGTMREF with 2 parts");
			inputSet.addAll(ContractUtils.QFGTMREFtoSet(name));
		}
		// purge component types -- leave only properties.
		// we are assuming that components cannot be changed by analysis
		Set<String> toRemove = new HashSet<String>();
		for (String s : inputSet) {
			if (!s.contains("."))
				toRemove.add(s);
		}
		inputSet.removeAll(toRemove);

		for (QFGTMREF name : sc2.getOutput().getNames()) {
			// assuming only two-part names
			if (name.getIds().size() > 2)
				throw new UnsupportedOperationException(
						"Only support QFGTMREF with 2 parts");
			outputSet.addAll(ContractUtils.QFGTMREFtoSet(name));
		}
		toRemove = new HashSet<String>();
		for (String s : outputSet) {
			if (!s.contains("."))
				toRemove.add(s);
		}
		outputSet.removeAll(toRemove);

		inputSet.retainAll(outputSet);
		if (!inputSet.isEmpty())
			System.out.println("Dependent: " + sc1.getName/* getAnalysisName */()
					+ " " + sc2.getName/* getAnalysisName */());

		return inputSet;
	}

}