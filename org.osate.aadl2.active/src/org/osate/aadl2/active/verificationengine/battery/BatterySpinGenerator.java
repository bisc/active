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

package org.osate.aadl2.active.verificationengine.battery;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
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

public class BatterySpinGenerator {
	private DBConnector dbc; // access the db
	private VariableAssignment values; // used in expression generation
	private String batteryVarName; 
	private String k0, k1, k2, k3; 

	public BatterySpinGenerator() { 
		dbc = new DBConnector();
		dbc.connect();
	}

	// generates a substitution for battery spin non-terminals given variable substitution and variable assignment
	public Map<String, String> generateConfigSubstitution(ContractClause cc, VariableAssignment va) throws UnnecessaryVerificationException { 
		values = va;

		Map<String, String> subst = new HashMap<String, String>();
		Set<String> batteries = new HashSet<String>(); 

		// check if database has necessary tables
		Set<String> requiredTables = new HashSet<String>();
		requiredTables.add("component");
		requiredTables.add("Is_Multicell_Battery");
		requiredTables.add("Bat_Scheduler");
		requiredTables.add("Cell_Rows");
		requiredTables.add("Cell_Cols");
		requiredTables.add("Serial_Req");
		requiredTables.add("Paral_Req");
		requiredTables.add("K0");
		requiredTables.add("K1");
		requiredTables.add("K2");
		requiredTables.add("K3");

		for(String t: requiredTables) 
			if (!dbc.tableExists(t))
				throw new UnsupportedOperationException("Cannot run Spin battery verification on database without " + t + " table.");

		// determine battery variable name 
		List<String> ids = cc.getVarQuant().getIds();
		List<String> types = cc.getVarQuant().getTypes();
		for (int i = 0; i < ids.size(); i++) {
			if (types.get(i).equals("device")) { 
				batteries.add(ids.get(i)); 
			}
		}

		if (batteries.size() != 1)
			throw new UnsupportedOperationException("Cannot verify for other than one battery at a time - not for " + batteries.size()); 

		batteryVarName = (String) batteries.toArray()[0];
		if (!va.containsKey(batteryVarName))
			throw new UnsupportedOperationException("Cannot find a valuation for battery variable " + batteryVarName);

		try {

			// assuming that devices with Is_Multicell_Battery = true are batteries
			String batteryPropertyQuery = "SELECT " +
					"Bat_Scheduler.value as scheduler, " +
					"Cell_Cols.value as cols, Cell_Rows.value as rows, " + 
					"Serial_Req.value as serialreq, Paral_Req.value as paralreq, " +
					"K0.value as k0, K1.value as k1, K2.value as k2, K3.value as k3 " +
					"FROM component device " +
					"INNER JOIN Bat_Scheduler ON device.componentID = Bat_Scheduler.ownerID " +
					"INNER JOIN Cell_Cols ON device.componentID = Cell_Cols.ownerID " + 
					"INNER JOIN Cell_Rows ON device.componentID = Cell_Rows.ownerID " + 
					"INNER JOIN Serial_Req ON device.componentID = Serial_Req.ownerID " +
					"INNER JOIN Paral_Req ON device.componentID = Paral_Req.ownerID " +
					"INNER JOIN K0 ON device.componentID = K0.ownerID " +
					"INNER JOIN K1 ON device.componentID = K1.ownerID " +
					"INNER JOIN K2 ON device.componentID = K2.ownerID " +
					"INNER JOIN K3 ON device.componentID = K3.ownerID " +
					"WHERE device.componentID = " + va.get(batteryVarName) + 
					" AND componentType='device'";

			ResultSet rs = dbc.executeSelectQuery(batteryPropertyQuery);

			// expecting only one row -- with the battery under consideration
			if (!rs.next())
				throw new UnnecessaryVerificationException("No battery found for verification, stopping"); 

			subst.put("$SCHEDULER", ContractUtils.toSpinNumber(rs.getString("scheduler")));
			subst.put("$ROWS", ContractUtils.toSpinNumber(rs.getString("rows"))); 
			subst.put("$COLS", ContractUtils.toSpinNumber(rs.getString("cols")));
			subst.put("$PARALREQ", ContractUtils.toSpinNumber(rs.getString("paralreq")));
			subst.put("$SERIALREQ", ContractUtils.toSpinNumber(rs.getString("serialreq")));

			k0 = ContractUtils.toSpinNumber(rs.getString("k0")); 
			k1 = ContractUtils.toSpinNumber(rs.getString("k1")); 
			k2 = ContractUtils.toSpinNumber(rs.getString("k2")); 
			k3 = ContractUtils.toSpinNumber(rs.getString("k3")); 

			String initValues = "";
			List<Integer> priorityList = new ArrayList<Integer>();

		} catch (SQLException e) {
			e.printStackTrace();
		}

		// convert the property statement
		subst.put("$LTL", generateContractLtl(cc));

		return subst; 
	}

	// generate a battery spin ltl statement for a given contract expression
	private String generateContractLtl(ContractClause cc) { 
		// enclose an expression into an ltl block
		String ltlExpression = generateExpressionLtl(cc.getHolds()); 
		System.out.println("Battery spin: verifying " + ltlExpression);
		String terminateExclusion = "((v0 == -1 && v1 == -1 && v2 == -1 && v3 == -1) || terminate)";
		return "ltl p0 {" + terminateExclusion + " || " + ltlExpression + "}"; // backslashes are so that spin macros use the whole multi-line string
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
			// battery spin doesn't know how to interpret lists yet, so just take left part
			if(ce.getOp() != null) 
				throw new UnsupportedOperationException("Battery spin doesn't support list operations yet: " + ce);

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
			throw new UnsupportedOperationException("Battery spin doesn't support string literals yet: " + ce);
		} else if (e instanceof ListLiteral) {
			ListLiteral ce = ((ListLiteral) e);
			throw new UnsupportedOperationException("Battery spin doesn't support list literals yet: " + ce);
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
					throw new UnsupportedOperationException("Battery spin: unknown ID: " + id);

				return id; 
			case 2: 
				// a property of a variable -- hopefully one of those understood by battery spin

				// substitute id with its value
				id = ids.get(0);

				// currently do not understand anything except a battery
				if(!id.equals(batteryVarName)) { 
					throw new UnsupportedOperationException("Battery spin: unknown ID: " + id);
				}

				// determine the property
				String prop = ids.get(1).toLowerCase();

				if (prop.equals("k0")) { 
					return k0; 
				} else if (prop.equals("k1")) {
					return k1; 
				} else if (prop.equals("k2")) {
					return k2; 
				} else if (prop.equals("k3")) {
					return k3; 
				} else 
					throw new UnsupportedOperationException("Battery spin doesn't handle property " + prop);

			default: 
				throw new UnsupportedOperationException("Battery spin handles QFGTMREFs with only 1 or 2 parts, not " + ids.size());
			}
		} else if (e instanceof FunctionalExpression) {
			FunctionalExpression ce = ((FunctionalExpression) e);
			// currently assuming it's only b.TN(x), otherwise aborting. 
			String varName = ce.getFunc().getIds().get(0);  
			String funcName = ce.getFunc().getIds().get(1);

			// some defenses
			if (!(varName.equals(batteryVarName) && funcName.equals("TN")))
				throw new UnsupportedOperationException("Battery spin doesn't handle variable " + varName + " or function "+ funcName);

			if (ce.getArgs().size() != 1)
				throw new UnsupportedOperationException("TN accepts only one argument");

			// generate an expression from arg and hope it's a number 
			int arg = Integer.valueOf(generateExpressionLtl(ce.getArgs().get(0))); 

			if (arg < 0 || arg > 3)
				throw new UnsupportedOperationException("Unacceptable TN argument value " + arg);

			return "v" + arg;
		}
		return "";
	}
}
