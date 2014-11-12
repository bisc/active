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

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.emf.common.util.EList;
import org.osate.aadl2.active.common.ContractUtils;
import org.osate.aadl2.active.common.DBConnector;
import org.osate.aadl2.active.interfaces.UnnecessaryVerificationException;
import org.osate.aadl2.active.interfaces.VariableAssignment;
import org.osate.xtext.aadl2.contracts.Contract.Addition;
import org.osate.xtext.aadl2.contracts.Contract.AndOrExpression;
import org.osate.xtext.aadl2.contracts.Contract.ArithmeticSigned;
import org.osate.xtext.aadl2.contracts.Contract.BoolBinOp;
import org.osate.xtext.aadl2.contracts.Contract.BooleanLiteral;
import org.osate.xtext.aadl2.contracts.Contract.BooleanNegation;
import org.osate.xtext.aadl2.contracts.Contract.ComparisonExpression;
import org.osate.xtext.aadl2.contracts.Contract.ContractClause;
import org.osate.xtext.aadl2.contracts.Contract.Expression;
import org.osate.xtext.aadl2.contracts.Contract.FloatLiteral;
import org.osate.xtext.aadl2.contracts.Contract.FunctionalExpression;
import org.osate.xtext.aadl2.contracts.Contract.IntLiteral;
import org.osate.xtext.aadl2.contracts.Contract.LTLBinOp;
import org.osate.xtext.aadl2.contracts.Contract.LTLExpression;
import org.osate.xtext.aadl2.contracts.Contract.LTLUnOp;
import org.osate.xtext.aadl2.contracts.Contract.ListExpression;
import org.osate.xtext.aadl2.contracts.Contract.ListLiteral;
import org.osate.xtext.aadl2.contracts.Contract.Multiplication;
import org.osate.xtext.aadl2.contracts.Contract.QFGTMREF;
import org.osate.xtext.aadl2.contracts.Contract.StringLiteral;

public class SchedSpinGenerator {
	// access the db
	private DBConnector dbc;
	private VariableAssignment values; // used in expression generation
	private Map<Integer, Integer> threadRenumbering; // from DB thread IDs to spin contiguous IDs 
	private Map<Integer, Integer> priorityRenumbering; // from DB priority numbers to spin contiguous IDs

	final String canPreempt = "CanPreempt";

	public SchedSpinGenerator() { 
		dbc = new DBConnector();
		dbc.connect();

		threadRenumbering = new HashMap<Integer, Integer>();
		priorityRenumbering = new HashMap<Integer, Integer>();
	}

	// generates a single spin program for a given variable substitution
	// it looks for and includes all threads that share processors
	// if they happen to belong to different processors, it throws an exception
	public Map<String, String> generateProgramSubstitution(ContractClause cc, VariableAssignment va) throws UnnecessaryVerificationException { 
		values = va;
		threadRenumbering.clear();
		priorityRenumbering.clear();

		Map<String, String> subst = new HashMap<String, String>();

		Set<String> threadsInModel = new HashSet<String>(); 
		Set<Integer> processorsInModel = new HashSet<Integer>();
		Set<String> protocolsInModel = new HashSet<String>();

		// check if database has necessary tables
		Set<String> requiredTables = new HashSet<String>();
		requiredTables.add("component");
		//	requiredTables.add("thread");
		//	requiredTables.add("processor");
		requiredTables.add("Period");
		//	requiredTables.add("Deadline");
		requiredTables.add("Actual_Processor_Binding");
		requiredTables.add("Scheduling_Protocol");
		requiredTables.add("Compute_Execution_Time");
		requiredTables.add("Priority");

		for(String t: requiredTables) 
			if (!dbc.tableExists(t))
				throw new UnsupportedOperationException("Cannot run Spin verification on database without " + t + " table.");

		try {
			// TODO be more precise about global or local scheduling -- introduce an aadl property

			// for now, assume local scheduling
			// first, select threads that are on the same processor with those that bound free vars
			// then compute the set of processors that need to be modeled in spin
			List<String> ids = cc.getVarQuant().getIds();
			List<String> types = cc.getVarQuant().getTypes();
			for (int i = 0; i < ids.size(); i++) {
				if (types.get(i).equals("thread")) { 
					threadsInModel.add(values.get(ids.get(i))); 
				}
			}
			System.out.println("Sched spin: threads in model: " + threadsInModel);

			// get all threads that share processors with those above
			String threadFindQuery = "SELECT DISTINCT a1.ownerId AS threadID, "
					+ "processor.componentID AS cpuID, "
					+ "Priority.value AS priority, "
					+ "Period.value AS period, " 
					+ "Compute_Execution_Time.valueMax AS wcet, "
					+ ( dbc.tableExists("Deadline") ? "Deadline.value AS deadline, " : "" ) 
					+ "Scheduling_Protocol.value AS cpuProtocol "
					+ "FROM "
					+ "Actual_Processor_Binding a1 "
					+ "JOIN Actual_Processor_Binding a2 ON a1.value = a2.value "
					+ "JOIN component processor ON a1.value = processor.componentName "
					+ "JOIN Scheduling_Protocol ON processor.componentId = Scheduling_Protocol.ownerId "
					+ "JOIN component thread ON thread.componentId = a1.ownerId "
					+ "JOIN Period ON thread.componentId = Period.ownerId "
					// some deadlines may be implicitly equal to periods
					+ ( dbc.tableExists("Deadline") ? 
							"JOIN Deadline ON thread.componentId = Deadline.ownerId " :	"" )
							+ "JOIN Compute_Execution_Time ON thread.componentId = Compute_Execution_Time.ownerId "
							+ "JOIN Priority ON Priority.ownerId = thread.componentId "
							+ "WHERE (0=1)"; // 0 = 1 for easier addition of disjunctions

			// generate the where clause: threads that are free var binds
			for (String id: threadsInModel) { 
				threadFindQuery += " OR a2.ownerID = " + id;
			}
			threadFindQuery += ";";
			ResultSet rs = dbc.executeSelectQuery(threadFindQuery);

			int threadNum = 0;
			String initValues = "";
			List<Integer> priorityList = new ArrayList<Integer>();

			while (rs.next()) {
				// assign a consecutive number to a thread
				threadRenumbering.put(Integer.valueOf(rs.getString("threadID")), threadNum);

				// put priorities in a list for further renumbering
				priorityList.add(Integer.valueOf(ContractUtils.toSpinNumber(rs.getString("priority"))));

				// record a processor and its protocol
				processorsInModel.add(Integer.valueOf(rs.getString("cpuID")));
				protocolsInModel.add(rs.getString("cpuProtocol"));

				// generate thread properties
				initValues += "period[" + threadNum + "] = " + ContractUtils.toSpinNumber(rs.getString("period")) + ";\n";
				initValues += "wcet[" + threadNum + "] = " + ContractUtils.toSpinNumber(rs.getString("wcet")) + ";\n";

				// deadlines implicitly equal to period if explicit deadline is missing
				if(dbc.tableExists("Deadline")) 
					initValues += "deadline[" + threadNum + "] = " + ContractUtils.toSpinNumber(rs.getString("deadline")) + ";\n";
				else 
					initValues += "deadline[" + threadNum + "] = " + ContractUtils.toSpinNumber(rs.getString("period")) + ";\n";
				//initValues += "prior[" + threadNum + "] = " + toSpinNumber(rs.getString("priority")) + ";\n";
				initValues += "\n";
				threadNum++;
			}

			// second pass, renumber and generate priorities now
			Collections.sort(priorityList);
			for (int i = 0; i < priorityList.size(); i++){
				priorityRenumbering.put(priorityList.get(i), i);
			}
			//	    System.out.println("Renumbering for priorities: " + priorityRenumbering);

			rs.beforeFirst();
			threadNum = 0; 
			while (rs.next()) { 
				int dbPriority = Integer.valueOf(ContractUtils.toSpinNumber(rs.getString("priority")));
				initValues += "prior[" + threadNum + "] = " + priorityRenumbering.get(dbPriority) + ";\n";
				threadNum++;
			}

			subst.put("$INITIALIZATION", initValues);
			System.out.println("Sched spin: number of threads = " + threadNum);
			subst.put("$THREADNUM", String.valueOf(threadNum));
		} catch (SQLException e) {
			e.printStackTrace();
		}

		// processors
		if (processorsInModel.size() == 0)
			throw new UnnecessaryVerificationException("No need to verify: found 0 processors");
		if (processorsInModel.size() > 1)
			throw new UnsupportedOperationException("Error: assuming 1 processor, but found " + processorsInModel.size());
		subst.put("$PROCESSORNUM", "1");

		// decide a scheduler 
		if (protocolsInModel.size() != 1)
			throw new UnsupportedOperationException("Assuming a single scheduling protocol, but found " + protocolsInModel.size());

		for (String s: protocolsInModel) { 
			if (s.contains("EDF")) { 
				subst.put("$ISEDF", "true");
				// TODO check if priorities are proportionate to deadlines, so that the initial moment is consistent
			} else if (s.contains("RMS")) { 
				subst.put("$ISEDF", "false");
				// TODO check if priorities are anti-proportionate to periods
			} else if (s.contains("DMS")) { 
				subst.put("$ISEDF", "false");
				// TODO check if priorities are anti-proportionate to deadlines
			}
		}	 

		// decide if the threads should have a synchronous start
		// TODO assuming it now, but need to check with the model
		subst.put("$STARTSYNC", "true");

		subst.put("$FIXEDPHASE", "true");

		//	if (!dbc.tableExists("processor"))
		//	    throw new UnsupportedOperationException("Cannot run Spin verification on a system with no processors.");
		//
		//	try {
		//	    ResultSet rs = dbc.executeSelectQuery("SELECT count(*) FROM processor");
		//	    rs.next();
		//	    int cpuNum = rs.getInt("count(*)");
		//	    if(cpuNum < 1) 
		//		throw new UnsupportedOperationException("Cannot run Spin verification on a system with no processors.");
		//	    
		//	    // for now assuming local scheduling, so only one processor in the model
		//	    //subst.put("$PROCESSORNUM", String.valueOf(cpuNum));
		//	    subst.put("$PROCESSORNUM", "1");
		//	    System.out.println("Sched spin: Number of cpus in model = 1, while total = " + cpuNum);
		//	} catch (SQLException e) {
		//	    e.printStackTrace();
		//	}

		// convert the property statement
		subst.put("$LTL", generateContractLtl(cc));

		return subst; 
	}

	// generate a spin ltl statement for a given contract expression
	private String generateContractLtl(ContractClause cc) { 
		// enclose an expression into an ltl block
		String ltlExpression = generateExpressionLtl(cc.getHolds()); 
		System.out.println("Sched spin: verifying " + ltlExpression);
		return "ltl p0 {\n" + ltlExpression + "\n}";
	}

	// recursively generates ltl for a contract expression
	private String generateExpressionLtl(Expression e) { 
		String op;
		if (e instanceof AndOrExpression) {
			AndOrExpression ce = ((AndOrExpression) e);
			if (ce.getOp().equals(BoolBinOp.OR)) // "||"
				op = "||";
			else if (ce.getOp().equals(BoolBinOp.AND)) // "&&"
				op = "&&";
			else if (ce.getOp().equals(BoolBinOp.IMPLIES))
				op = "->";
			else
				throw new UnsupportedOperationException("Cannot handle the operation " + ce.getOp());

			return "( "+ generateExpressionLtl(ce.getLeft()) + " " + op +
					" " + generateExpressionLtl(ce.getRight()) + " )";
		} else if (e instanceof LTLExpression) { 
			LTLExpression ce = ((LTLExpression) e);
			if (ce.getUnop() != null) { 
				if (ce.getUnop().equals(LTLUnOp.GLOBALLY))
					op = "[]";
				else if (ce.getUnop().equals(LTLUnOp.FUTURE))
					op = "<>";
				else 
					throw new UnsupportedOperationException("Unknown LTL unary operation: " + ce.getUnop());

				return op + " ("+ generateExpressionLtl(ce.getExpression()) + ")";

			} else if (ce.getBinop() != null) { 
				if (ce.equals(LTLBinOp.UNTIL))
					op = "U";
				else if (ce.equals(LTLBinOp.WEAKUNTIL))
					op = "W";
				else 
					throw new UnsupportedOperationException("Unknown LTL binary operation: " + ce.getBinop());

				return "("+ generateExpressionLtl(ce.getLeft()) + " " + op + " " + 
				generateExpressionLtl(ce.getRight()) + ")";

			} else 
				throw new UnsupportedOperationException("LTL expression doesn't have an operation: " + ce);
		} else if (e instanceof ListExpression) {
			ListExpression ce = ((ListExpression) e);
			// sched spin doesn't know how to interpret lists yet, so just take left part
			if(ce.getOp() != null) 
				throw new UnsupportedOperationException("Sched spin doesn't support list operations yet: " + ce);

			return generateExpressionLtl(ce.getLeft());
		} else if (e instanceof ComparisonExpression) {
			ComparisonExpression ce = ((ComparisonExpression) e);

			return "(" + generateExpressionLtl(ce.getLeft()) + " " + ce.getOp() +" "
			+ generateExpressionLtl(ce.getRight()) + ")";
		} else if (e instanceof BooleanNegation) {
			BooleanNegation ce = ((BooleanNegation) e);
			return "!(" + generateExpressionLtl(ce.getExpression()) + ")";
		} else if (e instanceof ArithmeticSigned) { 
			ArithmeticSigned ce = ((ArithmeticSigned) e);
			return "-" + generateExpressionLtl(ce.getExpression()); 
		} else if (e instanceof Addition) {
			Addition ce = ((Addition) e);
			return "(" + generateExpressionLtl(ce.getLeft()) + " " + ce.getOp() + " " 
			+ generateExpressionLtl(ce.getRight()) + ")";
		} else if (e instanceof Multiplication) {
			Multiplication ce = ((Multiplication) e);
			return "(" + generateExpressionLtl(ce.getLeft()) + " " + ce.getOp() + " "
			+ generateExpressionLtl(ce.getRight()) + ")";
		} else if (e instanceof IntLiteral) {
			IntLiteral ce = ((IntLiteral) e);
			return String.valueOf(ce.getValue());
		} else if (e instanceof FloatLiteral) {
			FloatLiteral ce = ((FloatLiteral) e);
			System.out.println("WARNING: using float in spin");
			return String.valueOf(ce.getValue());
		} else if (e instanceof BooleanLiteral) {
			BooleanLiteral ce = ((BooleanLiteral) e);
			return String.valueOf(ce.getValue());
		} else if (e instanceof StringLiteral) {
			StringLiteral ce = ((StringLiteral) e);
			throw new UnsupportedOperationException("Sched spin doesn't support string literals yet: " + ce);
		} else if (e instanceof ListLiteral) {
			ListLiteral ce = ((ListLiteral) e);
			throw new UnsupportedOperationException("Sched spin doesn't support list literals yet: " + ce);
		} else if (e instanceof QFGTMREF) { 
			QFGTMREF ce = (QFGTMREF) e; 
			EList<String> ids = ce.getIds();
			String id;
			switch(ids.size()) { 
			case 1: 
				// a variable identifier: substitute and return
				id = ids.get(0);
				if (values.containsKey(id)) 
					id = values.get(id); 
				else 
					throw new UnsupportedOperationException("Sched spin: unknown ID: " + id);

				// convert the value from DB numbering into spin numbering
				// TODO assuming that dealing with threads here, but not necessarily
				id = String.valueOf(threadRenumbering.get(Integer.valueOf(id)));

				return id; 
			case 2: 
				// a property of a variable -- hopefully one of those understood by sched spin

				// substitute id with its value
				id = ids.get(0);
				if (values.containsKey(id)) 
					id = values.get(id);
				else 
					throw new UnsupportedOperationException("Sched spin: unknown ID: " + id);

				// convert the value from DB numbering into spin numbering
				// TODO assuming that dealing with threads here, but not necessarily
				id = String.valueOf(threadRenumbering.get(Integer.valueOf(id)));

				// determine the property
				// TODO handle initial arrival property
				String prop = ids.get(1).toLowerCase();
				if (prop.equals("deadline")) { 
					return prop + "[" + id + "]"; 
				} else if (prop.equals("period")) { 
					return prop + "[" + id + "]"; 
				} else if (prop.equals("priority")) {
					return "prior[" + id + "]"; 
				} else if (prop.equals("compute_execution_time")) { 
					return "wcet[" + id + "]";
				} else 
					throw new UnsupportedOperationException("Sched spin doesn't handle property " + prop);

			default: 
				throw new UnsupportedOperationException("Sched spin handles QFGTMREFs with only 1 or 2 parts, not " + ids.size());
			}
		} else if (e instanceof FunctionalExpression) {
			FunctionalExpression ce = ((FunctionalExpression) e);
			if (ContractUtils.QFGTMREFtoString(ce.getFunc()).equals(canPreempt)) { 
				if(ce.getArgs().size() != 2)
					throw new UnsupportedOperationException(canPreempt + " can only have 2 arguments");

				String arg1 = generateExpressionLtl(ce.getArgs().get(0));
				String arg2 = generateExpressionLtl(ce.getArgs().get(1));

				// checks for substituting variable names are irrelevant here -- it is done in the QFTMGREF case

				return "(running["+arg1+"] && !running["+arg2+ 
						"] && queues[prior["+arg2+"]]?["+arg2+"] && !managerTurn)";
			} else 
				throw new UnsupportedOperationException("NEED TO HANDLE functional expressions in ltl");
		}
		return "";
	}
}
