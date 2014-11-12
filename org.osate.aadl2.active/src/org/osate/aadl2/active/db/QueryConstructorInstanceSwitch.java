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

package org.osate.aadl2.active.db;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.resource.IEObjectDescription;
import org.osate.aadl2.AadlBoolean;
import org.osate.aadl2.AadlInteger;
import org.osate.aadl2.AadlReal;
import org.osate.aadl2.AadlString;
import org.osate.aadl2.AbstractNamedValue;
import org.osate.aadl2.BasicProperty;
import org.osate.aadl2.BooleanLiteral;
import org.osate.aadl2.ClassifierType;
import org.osate.aadl2.ClassifierValue;
import org.osate.aadl2.ComputedValue;
import org.osate.aadl2.EnumerationLiteral;
import org.osate.aadl2.EnumerationType;
import org.osate.aadl2.IntegerLiteral;
import org.osate.aadl2.ListType;
import org.osate.aadl2.ListValue;
import org.osate.aadl2.NamedValue;
import org.osate.aadl2.NumberValue;
import org.osate.aadl2.Property;
import org.osate.aadl2.PropertyAssociation;
import org.osate.aadl2.PropertyExpression;
import org.osate.aadl2.PropertySet;
import org.osate.aadl2.PropertyType;
import org.osate.aadl2.PropertyValue;
import org.osate.aadl2.RangeType;
import org.osate.aadl2.RangeValue;
import org.osate.aadl2.RealLiteral;
import org.osate.aadl2.RecordType;
import org.osate.aadl2.RecordValue;
import org.osate.aadl2.ReferenceType;
import org.osate.aadl2.ReferenceValue;
import org.osate.aadl2.StringLiteral;
import org.osate.aadl2.instance.ComponentInstance;
import org.osate.aadl2.instance.InstanceReferenceValue;
import org.osate.aadl2.instance.util.InstanceSwitch;
import org.osate.aadl2.modelsupport.modeltraversal.AadlProcessingSwitch;
import org.osate.aadl2.modelsupport.resources.OsateResourceUtil;
import org.osate.aadl2.properties.PropertyNotPresentException;
import org.osate.xtext.aadl2.properties.util.EMFIndexRetrieval;
import org.osate.xtext.aadl2.properties.util.PropertyUtils;

/** 
 * This class iterates through an instance aadl model and creates a query that mirrors this instance in the database. 
 * @author ivan
 *
 */
public class QueryConstructorInstanceSwitch extends InstanceSwitch<String> {

	private List<String> query;
	private List<String> tables;
	private Map<String, List<String>> metaOwners; // store association of property to list of owner components 
	private Map<String, List<Property>> propertiesCache; // sets to lists of properties 

	private int componentCounter; // index of the next added component

	public QueryConstructorInstanceSwitch() {
		query = new ArrayList<String>();
		tables = new ArrayList<String>();
		metaOwners = new HashMap<String, List<String>>(); 
		propertiesCache = null;

		componentCounter = 0;
	}
	
	/**
	 * Get the created query.
	 * @return list of queries created by traversing an aadl model. 
	 */
	public List<String> getSqlQuery() {
		return query;
	}

	/**
	 * Add a list of queries to the existing ones. 
	 * @param l list of queries
	 */
	private void addToQuery(List<String> l) {
		Iterator<String> i = l.iterator();
		while (i.hasNext()) {
			query.add(i.next());
		}
	}

	/**
	 * Collect properties from the workspace
	 */
	private void populatePropertiesCache(EObject context) { 
		propertiesCache = new HashMap<String, List<Property>>();

		for (IEObjectDescription ieo: EMFIndexRetrieval.getAllPropertySetsInWorkspace(context)) { 

			PropertySet ps = (PropertySet)OsateResourceUtil.getResourceSet().getEObject(ieo.getEObjectURI(), true);//(PropertySet)ieo.getEObjectOrProxy();
			propertiesCache.put(ps.getName(), new ArrayList<Property>()); 
			for (Property prop : ps.getOwnedProperties()) {
				propertiesCache.get(ps.getName()).add(prop);
			}
		}
	}

	/**
	 * Handle encountering a component instance in the aadl model. 
	 */
	public String caseComponentInstance(ComponentInstance compInst) {
		System.out.println("ComponentInstance " + compInst);

		String compCatName = "component";//o.getCategory().getLiteral().replaceAll("\\s+",""); 

		if (!tables.contains(compCatName)) {
			query.add("CREATE TABLE IF NOT EXISTS " + compCatName + " (componentID  MEDIUMINT NOT NULL, PRIMARY KEY(componentID), componentName varchar(500), componentType varchar(500));\n");
			tables.add(compCatName);
			query.add("INSERT INTO _meta (tableName, tableType, owner) VALUES ('" + compCatName + "', 'component', '')");
		}
		query.add("INSERT INTO " + compCatName + " (componentID, componentName, componentType) "
				+ "VALUES (" + componentCounter + ", '" + compInst.getInstanceObjectPath() + "', '" + compInst.getCategory().getName() + "');\n");


		boolean quickDbGeneration = true; 

		if (quickDbGeneration) { 
			// alternative: iterate through owned property associations
			// but it doesn't cover some necessary default values (e.g., Is_Multicell_Battery)
			Iterator<PropertyAssociation> i = compInst.getOwnedPropertyAssociations().iterator();
			while (i.hasNext()) {
				PropertyAssociation pa = i.next();

				// a weird check because theoretically it should be always true
				if (!compInst.acceptsProperty(pa.getProperty())) {
					System.out.println("NOT ACCEPTED owner " + compInst + " property " + pa.getProperty());
					continue;
				}

				generateSqlForProperty(pa.getProperty(), compInst, compCatName, componentCounter);
			}
		} else { 
			// the longer alternative, but covers default values
			if (propertiesCache == null)
				populatePropertiesCache(compInst.getComponentClassifier());

			// iterate through all workspace properties
			// decect acceptable and present ones and generate sql for them
			for (String propertySet: propertiesCache.keySet()) { 
				for (Property prop: propertiesCache.get(propertySet)) { 
					if (!compInst.acceptsProperty(prop))
						continue;

					try {
						generateSqlForProperty(prop, compInst, compCatName, componentCounter);
					} catch (PropertyNotPresentException e) { 
						System.out.println("not present, continuing");
					}
				}
			}
		}

		componentCounter++;
		return AadlProcessingSwitch.DONE;
	}

	/** 
	 * Add a query for a property association to the internal query storage. 
	 * @param lpa a property association
	 * @param owner owner of the property association
	 * @param ownerTableName table/type of component that contains the property
	 * @param ownerID id of the component that owns the property
	 */
	private void generateSqlForProperty(Property prop, ComponentInstance owner, String ownerTableName,
			int ownerID) {

		String propName = prop.getName();
		System.out.println("property " + prop);

		String tableName = propName;//ownerTableName + "_" + propName;
		PropertyType pt = prop.getPropertyType();
		String tableType = aadlTypeToSqlType(pt);

		if (tableType.startsWith("record")) { 
			// TODO handle record queries
			RecordType rt = (RecordType) pt;
			Iterator<BasicProperty> bpi = rt.getOwnedFields().iterator();
			while (bpi.hasNext()) {
				BasicProperty bp = bpi.next();
				System.out.println("record prop value " + bp);
			}

			// do something for records
		} else if (tableType.startsWith("list")) { 
			try {
				PropertyExpression listExp = PropertyUtils.getSimplePropertyListValue(owner, prop);
				if (listExp instanceof ListValue) {
					int valueIndex = 0;
					ListValue lv = (ListValue) listExp;
					Iterator<PropertyExpression> ipe = lv.getOwnedListElements().iterator();
					while (ipe.hasNext()) {
						PropertyExpression listItem = ipe.next();

						if (!tables.contains(tableName)) {
							query.add("CREATE TABLE IF NOT EXISTS "
									+ tableName
									+ "  (valueID  MEDIUMINT NOT NULL AUTO_INCREMENT, PRIMARY KEY(valueID), valueIndex MEDIUMINT, value varchar(3055), ownerID int);\n");
							tables.add(tableName);
						}

						String listItemString = simplePropertyToString(listItem);
						System.out.println("list item " + listItemString);
						query.add("INSERT INTO " + tableName + " (value, valueIndex, ownerID) VALUES ('"
								+ listItemString + "', " + valueIndex  + ", " + ownerID + ");\n");

						valueIndex++;
					}				
				} else
					throw new UnsupportedOperationException("Cannot construct a query for a list property " + prop);
			} catch (PropertyNotPresentException e) { 
				System.out.println("not present, continuing");
			}
		} else if (tableType.startsWith("range")) { 
			if (!tables.contains(tableName)) {
				query.add("CREATE TABLE IF NOT EXISTS "
						+ tableName
						+ "  (valueID  MEDIUMINT NOT NULL AUTO_INCREMENT, PRIMARY KEY(valueID), valueMin varchar(3055), valueMax varchar(3055), ownerID int);\n");
				tables.add(tableName);
			}

			try {
				RangeValue rv = (RangeValue) PropertyUtils.getSimplePropertyValue(owner, prop);
				String min = numberValueToString(rv.getMinimumValue());
				String max = numberValueToString(rv.getMaximumValue());

				query.add("INSERT INTO " + tableName + " (valueMin, valueMax, ownerID) "
						+ "VALUES ('" + min + "', '" + max + "', " + ownerID + ");\n");
			} catch (PropertyNotPresentException e) { 
				System.out.println("not present, continuing");
			}


		} else { 
			// simple types: not list, record, or range
			if (!tables.contains(tableName)) {
				query.add("CREATE TABLE IF NOT EXISTS "
						+ tableName
						+ "  (valueID  MEDIUMINT NOT NULL AUTO_INCREMENT, PRIMARY KEY(valueID), value varchar(3055), ownerID int);\n");
				tables.add(tableName);
			}

			try {
				PropertyExpression exp = PropertyUtils.getSimplePropertyValue(owner, prop);
				String value = simplePropertyToString(exp);
				query.add("INSERT INTO " + tableName + " (value, ownerID) "
						+ "VALUES ('" + value + "', " + ownerID + ");\n");
			} catch (PropertyNotPresentException e) { 
				System.out.println("not present, continuing");
			}
		}

		// handle meta for all property types 
		boolean needToUpdate = false;
		if (!metaOwners.containsKey(tableName)) {  
			//create a new list
			metaOwners.put(tableName, new ArrayList<String>()); 
			metaOwners.get(tableName).add(ownerTableName);
			needToUpdate = true; 
		} else {
			// already contains a record 
			if (!metaOwners.get(tableName).contains(ownerTableName)) { 
				// need to update record
				// remove the old row
				// this is very inefficient, but works with visitor pattern  
				query.add("DELETE FROM _meta WHERE tableName='" + tableName + "'");
				metaOwners.get(tableName).add(ownerTableName);
				needToUpdate = true; 
			}
		}

		if (needToUpdate) { 
			// convert to csv format 
			String ownersList = metaOwners.get(tableName).toString()
					.replace("[", "").replace("]", "").replace(", ", ",");

			query.add("INSERT INTO _meta (tableName, tableType, owner) VALUES ('" + 
					tableName + "', '" + tableType+ "', '"  + ownersList + "')");
		}
	}

	/**
	 * Converts an AADL property type to a string representation of a table type. 
	 * @param pt AADL type
	 * @return table type
	 */
	private String aadlTypeToSqlType(PropertyType pt) { 
		if (pt instanceof AadlBoolean) 
			return "bool";
		else if (pt instanceof AadlInteger) 
			return "int";
		else if (pt instanceof AadlReal) 
			return "real";
		else if (pt instanceof AadlString)
			return "string";
		else if (pt instanceof EnumerationType)
			return "string";
		else if (pt instanceof ClassifierType)
			return "string";
		if (pt instanceof ReferenceType)
			return "ref";
		if (pt instanceof ListType)
			return "list(" + aadlTypeToSqlType(((ListType) pt).getElementType()) + ")"; 
		if (pt instanceof RangeType)
			return "range(" + aadlTypeToSqlType(((RangeType) pt).getNumberType()) + ")";
		if (pt instanceof RecordType)
			return "record"; // TODO elaborate this
		else 
			throw new UnsupportedOperationException("Unsupported type of property " + pt);


	}

	/**
	 * Generate a string for a simple property expression 
	 * @param pe property expression
	 * @return a string to encode the property value in the db 
	 */
	private String simplePropertyToString(PropertyExpression pe) {
		// handles properties except records or lists
		String result = "";

		if (!(pe instanceof PropertyValue))
			result = "UNSUPPORTED";
		else if (pe instanceof BooleanLiteral)
			result = String.valueOf(((BooleanLiteral) pe).getValue());
		else if (pe instanceof NumberValue)
			result = numberValueToString((NumberValue) pe);
		else if (pe instanceof InstanceReferenceValue)
			result = ((InstanceReferenceValue) pe).getReferencedInstanceObject().getInstanceObjectPath();
		else if (pe instanceof ReferenceValue)
			result = "UNSUPPORTED REFERENCE VALUE";
		else if (pe instanceof StringLiteral)
			result = ((StringLiteral) pe).getValue();
		else if (pe instanceof RangeValue) {
			RangeValue rv = (RangeValue) pe;
			result = numberValueToString(rv.getMinimumValue()) + " .. " + numberValueToString(rv.getMaximumValue());
		} else if (pe instanceof ClassifierValue) {
			result = ((ClassifierValue) pe).getClassifier().getName();
		} else if (pe instanceof ComputedValue) {
			result = "UNSUPPORTED COMPUTED VALUE";
		} else if (pe instanceof RecordValue) {
			result = "UNSUPPORTED RECORD VALUE";
		} else if (pe instanceof NamedValue) {
			AbstractNamedValue anv = ((NamedValue) pe).getNamedValue();
			result = ((EnumerationLiteral) anv).getName();
		} else {
			result = "UNSUPPORTED NAMED VALUE";
		}
		return result;
	}

	/**
	 * Transform an aadl number value to a db representation. 
	 * @param nv number value
	 * @return a string that encodes the number value in the db
	 */
	private String numberValueToString(NumberValue nv) {
		// handles numbers
		if (nv instanceof IntegerLiteral)
			return String.valueOf(((IntegerLiteral) nv).getValue());
		else if (nv instanceof RealLiteral)
			return String.valueOf(((RealLiteral) nv).getValue());
		else
			return "UNSUPPORTED NUMBER VALUE";
	}
}