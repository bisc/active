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

package org.osate.aadl2.active.verificationengine.smt;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.osate.aadl2.AadlBoolean;
import org.osate.aadl2.AadlInteger;
import org.osate.aadl2.AadlReal;
import org.osate.aadl2.AadlString;
import org.osate.aadl2.ListType;
import org.osate.aadl2.Property;
import org.osate.aadl2.PropertyType;
import org.osate.aadl2.ReferenceType;
import org.osate.aadl2.active.common.DBConnector;
import org.osate.xtext.aadl2.contracts.Contract.AnalysisContract;
import org.osate.xtext.aadl2.properties.util.GetProperties;

public class DefAndFactSmtGenerator {

	private String smtBasicTypeOutput, smtFunctionOutput, smtFactOutput;

	// access the db
	private DBConnector dbc;

	public DefAndFactSmtGenerator() {
		dbc = new DBConnector();
		dbc.connect();

		clearData();
	}

	public void clearData() {
		smtBasicTypeOutput = "";
		smtFunctionOutput = "";
		smtFactOutput = "";
	}

	/**
	 * Returns a name for the complementary containment function (for list properties)
	 * @param arrayName name of the property (and also the array that represents it in SMT)
	 * @return a containment function name
	 */
	public String arrayNameToContFuncName(String arrayName) { 
		return arrayName + "_cont";
	}

	/**
	 * Generate SMTv2 definitions and facts given a set of components, properties, and a contract.
	 * Also populates ID dictionary, but doesn't apply it. 
	 * @param compsToProps component names and set of properties for each. 
	 * @param sc analysis contract
	 * @param stringToIntDict ref to ID dictionary to populate
	 * @return
	 */
	public String generateDefinitionsAndFacts(Map<String, Set<String>> compsToProps, AnalysisContract sc, Map<String, Integer> stringToIntDict) { 

		// these two functions work on a shared set of outputs
		generateComponentDefs(compsToProps.keySet());
		generatePropertyFacts(compsToProps, sc, stringToIntDict);

		// return the set of function declarations and facts
		return smtBasicTypeOutput + smtFunctionOutput + smtFactOutput;
	}


	/**
	 * Generates ID restrictions that apply to a particular component type
	 * @param variableName name of the variable to use in restrictions
	 * @param componentType name of the component type (and table)
	 * @return
	 */
	public String generateComponentIDRestrictions(String variableName, String componentType) {
		//	if (!dbc.getTableType(componentType).equals("component"))
		//	    throw new UnsupportedOperationException(componentType + " is not a component table but listed as a component");
		if (!dbc.tableExists("component"))
			throw new UnsupportedOperationException("Component table doesn't exist");

		String restrictions = "\n\t\t( or ";
		ResultSet rs = dbc.executeSelectQuery("SELECT componentID FROM component WHERE componentType = '" + componentType + "';");
		try {
			while (rs.next()) {
				restrictions += "\n\t\t( = " + variableName + " " + rs.getString("componentID") + ") ";
			}
		} catch (SQLException e) {
			e.printStackTrace();
		}
		restrictions += ")";
		return restrictions;
	}

	// generate smt sorts for components
	private void generateComponentDefs(Set<String> components) { 
		// generation for components
		Iterator<String> i = components.iterator();
		while (i.hasNext()) {
			String table = i.next();
			System.out.println("generating for table " + table);
			smtBasicTypeOutput += "(define-sort " + table + " () (Int))\n";

			// some defenses
			if (!dbc.tableExists(table))
				System.out.println("WARNING: No DB table for component " + table);
			else if (!dbc.getTableType(table).equals("component"))
				throw new UnsupportedOperationException(table + " is not a component table but listed as a component");
		}
	}

	// generate facts about concrete property values in db for smt
	private void generatePropertyFacts(Map<String, Set<String>> compsToProps, 
			AnalysisContract sc, Map<String, Integer> stringToIntDict) {
		// iterate over components
		Iterator<String> compIt = compsToProps.keySet().iterator();
		while(compIt.hasNext()) {
			String comp = compIt.next();
			Iterator<String> propIt = compsToProps.get(comp).iterator();
			// iterate over properties
			while(propIt.hasNext()) {
				String prop = propIt.next();

				// null key is used to store input components without properties
				if (prop == null)
					continue;
				System.out.println("generating for " + comp + "." + prop);

				boolean stringEncodingOn = false;
				// decide for each property: is it in DB, what is the meta, what does the aadl model say
				if(dbc.tableExists(prop)) {
					String tableType = dbc.getTableType(prop);
					if(!tableType.startsWith("list")) {
						// simple properties first, NOT lists
						String simpleType = "";

						if (tableType.equals("int")) 
							simpleType = "Int";
						else if (tableType.equals("real")) {
							simpleType = "Real";
						} else if (tableType.equals("bool")) {
							simpleType = "Bool";
						} else if (tableType.equals("string")) {
							simpleType = "Int";
							stringEncodingOn = true;
						} else if (tableType.equals("ref")) {
							// a reference maps to an ID, which is Int
							simpleType = "Int";
							stringEncodingOn = true;
							throw new UnsupportedOperationException("Encoding is not supported for refs now");
						} else 
							throw new UnsupportedOperationException("Unsupported type " + tableType + 
									" of property table " + prop);

						// example: (declare-fun Period (thread) Int)
						smtFunctionOutput += "(declare-fun " + prop + " (" + comp + ") " + simpleType
								+ ")\n";

						String valueIdColumn = "valueID";
						String valueColumn = "value";
						String ownerIdColumn = "ownerID";

						ResultSet rs = dbc.executeSelectQuery("SELECT " + valueColumn + ", " +
								ownerIdColumn + " FROM " + prop + ";");
						int encodingCounter = 0;
						try {
							while (rs.next()) {
								String value = rs.getString(valueColumn);

								// if dealing with string, encode using integers and store in dictionary
								// FIXME name collisions possible, ideally make sub-dictionaries
								if (stringEncodingOn) {
									if (stringToIntDict.containsKey(value))
										value = String.valueOf(stringToIntDict.get(value));
									else {
										stringToIntDict.put(value, encodingCounter);
										value = String.valueOf(encodingCounter);
										encodingCounter++;
									}
								}
								// TODO double-check with the owner table
								smtFactOutput += "(assert (= (" + prop + " " + rs.getString(ownerIdColumn) + ") " + value + " ))\n";

							}
						} catch (SQLException e) {
							e.printStackTrace();
						}

					} else if(tableType.startsWith("list")) {
						// now what about lists

						if (tableType.endsWith("int)")) {
							throw new UnsupportedOperationException("SMT generation for lists not supported yet");
						} else if (tableType.endsWith("real)")) {
							throw new UnsupportedOperationException("SMT generation for lists not supported yet");
						} else if (tableType.endsWith("bool)")) {
							throw new UnsupportedOperationException("SMT generation for lists not supported yet");
						} else if (tableType.endsWith("string)")) {
							throw new UnsupportedOperationException("SMT generation for lists not supported yet");
						} else if (tableType.endsWith("ref)")) {
							// Do not declare here: below for all supported types
						} else 
							throw new UnsupportedOperationException("Unsupported list type " + tableType + 
									" of property table " + prop); 

						// generate definition for list property function
						// using two-part approach for representing: 
						// * an unbounded array with concrete indices and values
						// * a boolean function to represent the bounds of array 
						// (true for existing indices, false for non-existing)

						String valueIdColumn = "valueID";
						String valueIndexColumn = "valueIndex";
						String valueColumn = "value";
						String ownerIdColumn = "ownerID";

						// arguments: owner component, index, value
						String arrayDef = "(declare-const "+ prop + " (Array " + comp + " Int Int))\n"; 
						String containmentFuncDef = "(define-fun " + arrayNameToContFuncName(prop) + " ((x1 " + comp + ") (x2 Int)) Bool\n";
						String postContainmentOutput = ")";

						ResultSet rs = dbc.executeSelectQuery("SELECT " + valueIndexColumn + ", " + valueColumn + ", "
								+ ownerIdColumn + " FROM " + prop + ";");
						try {
							// iterate over values
							while (rs.next()) {
								// inefficient: run query for every value
								int refId = dbc.getComponentIndexAcrossAllTables(rs.getString(valueColumn));

								if (refId == -1)
									throw new UnsupportedOperationException("Component name not found in any known component table");

								// array values:
								// example: (assert (= (select arrayname compID index) value )); 
								arrayDef += "(assert (= (select " + prop + " " + rs.getString(ownerIdColumn)
										+ " " + rs.getString(valueIndexColumn) + ") " + refId + "))\n";

								// containment function values: 	
								// example: (array-cont-func owning-component-id list-index) bool 
								//(define-fun Not_Colocated ((x!1 Int) (x!2 Int)) Bool
								//    (ite (and (= x!1 0) (= x!2 1)) true
								//    (ite (and (= x!1 0) (= x!2 2)) true
								//    (ite (and (= x!1 1) (= x!2 0)) true
								//    (ite (and (= x!1 2) (= x!2 0)) true
								//    (ite (and (= x!1 2) (= x!2 1)) true
								//      false)))))) 
								containmentFuncDef += "(ite (and (= x1 " + rs.getString(ownerIdColumn) + ")" +
										"(= x2 " + rs.getString(valueIndexColumn) + ")) true\n";
								postContainmentOutput += ")";

							}
						} catch (SQLException e) {
							e.printStackTrace();
						}
						smtFactOutput += arrayDef + "\n" + containmentFuncDef + "false " + postContainmentOutput + "\n\n";
					}

				} else { 
					// the property table doesn't exist and we need to figure 
					// the function declaration out from aadl
					System.out.println("looking for definition " + comp + "." + prop);
					// TODO do more robust property lookup for different propertysets
					// TODO resolve the containment issue -- subclauses no longer have any containers, need to lookup somewhere else
					Property p = GetProperties.lookupPropertyDefinition(sc,//sc.getContainingComponentImpl(),
							"mypropertyset", prop);
					if (p != null) {
						// TODO refactor transformations from aadl types to smt
						// types
						String unitName = "";
						System.out.println("Property def found " + p.getPropertyType());
						PropertyType type = p.getPropertyType();

						// deal with list-containing properties
						if (p.isList()) {
							ListType lt = (ListType) p.getPropertyType();
							PropertyType et = lt.getElementType();
							if (et instanceof AadlInteger || et instanceof AadlString || et instanceof AadlBoolean)
								unitName = "Int";
							else if (et instanceof AadlReal)
								unitName = "Real";
							else if (et instanceof ReferenceType) {
								ReferenceType refType = (ReferenceType) et;
								if (refType.getNamedElementReferences().size() != 1)
									throw new UnsupportedOperationException(
											"something strange going on with the refs list: "
													+ refType.getNamedElementReferences());

								String refClassName = refType.getNamedElementReferences().get(0).getMetaclass()
										.getName();
								// TODO can handle this better
								if (refClassName.equals("Thread"))
									unitName = "thread";
								else if (refClassName.equals("Process"))
									unitName = "process";
								else if (refClassName.equals("Processor"))
									unitName = "processor";
								else
									throw new UnsupportedOperationException(
											"something strange going on with the refs list: refclassname = "
													+ refClassName + " list = " + refType.getNamedElementReferences());

								// System.out.println("element refs = " +
								// refType.getNamedElementReferences());
							} else
								throw new UnsupportedOperationException("cannot handle other types yet: " + et);

							// create a composite function from two things to
							// bool
							smtFunctionOutput += "(declare-fun " + prop + " (" + comp + " " + unitName
									+ ") Bool)\n";
						} else {
							// case if the property is not a list
							// TODO try this code out
							if (type instanceof AadlReal)
								unitName = "Real";
							else if (type instanceof AadlInteger || type instanceof AadlString
									|| type instanceof AadlBoolean) {
								unitName = "Int";
							} else {
								throw new UnsupportedOperationException("cannot handle other types yet: " + type);
							}

							// create a simple function from component to
							// property type
							smtFunctionOutput += "(declare-fun " + prop + " (" + comp + ") " + unitName + ")\n";
						}

					} else {
						System.out.println("Property def not found for " + comp + "." + prop);
					}
				}
			}
		}
	}
}
