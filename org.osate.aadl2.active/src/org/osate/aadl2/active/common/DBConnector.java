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

package org.osate.aadl2.active.common;

import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * This is a specialized DB connector to simplify accessing an AADL DB.
 * Along with generic functions, it offers some AADL DB specific ones, 
 * like maintaining and searching through table metainformation. 
 * @author ivan
 */
public class DBConnector {

    private Connection connObj = null;
    private String mysqlDBName = "aadl";

    /**
     * Establish a persistent connection with the database. 
     */
    public void connect() {
	String mysqlServer = "jdbc:mysql://localhost:3306/";
	String mysqlUsername = "root";
	String mysqlPassword = "root";

	String mysqlDriverClass = "com.mysql.jdbc.Driver";

	System.out.println("JDBC connection using MySql");

	try {
	    Class.forName(mysqlDriverClass).newInstance(); // Loading the class
	    // through
	    // reflection
	    connObj = DriverManager.getConnection(mysqlServer + mysqlDBName, mysqlUsername, mysqlPassword);

	    // autocommit is disabled for batches but overall kept true to avoid freezing
	    connObj.setAutoCommit(true);
	    System.out.println("Connected to mysql - database name:" + mysqlDBName);

	} catch (Exception e) {
	    System.out.println("Unable to connect");
	    e.printStackTrace();
	}
    }

    /** 
     * Disconnect from the database. 
     */
    public void disconnect() {
	if (connObj != null)
	    try {
		connObj.close();
		System.out.println("Disconnected from mysql");
	    } catch (SQLException e) {
		e.printStackTrace();
	    }
    }

    /** 
     * Execute one update query.
     * @param q the query
     * @return 0 if successfully completed, -1 otherwise
     */
    public int executeUpdateQuery(String q) {
	List<String> l = new ArrayList<String>();
	l.add(q);
	return executeUpdateQueries(l);
    }

    /** 
     * Execute several update queries.
     * @param q the query
     * @return 0 if all successfully completed, -1 otherwise
     */
    public int executeUpdateQueries(List<String> q) {
	try {
	    connObj.setAutoCommit(false);
	    Statement st = connObj.createStatement();
	    Iterator<String> i = q.iterator();

	    while (i.hasNext()) {
		String cur = i.next();
		st.executeUpdate(cur);
	    }

	    connObj.commit();
	    connObj.setAutoCommit(true);
	} catch (SQLException e) {
	    try {
		connObj.rollback();
	    } catch (SQLException e1) {
		e1.printStackTrace();
	    }
	    e.printStackTrace();
	    return -1;
	}

	return 0;
    }

    /**
     * Execute a select query from the database. 
     * @param q a select query
     * @return result set 
     */
    public ResultSet executeSelectQuery(String q) {
	ResultSet rs = null;
	try {
	    Statement st = connObj.createStatement();

	    if (st.execute(q)) {
		rs = st.getResultSet();
	    } else {
		System.out.println("Select query not executed");
	    }
	} catch (SQLException e1) {
	    e1.printStackTrace();
	}
	return rs;
    }

    /**
     * Determines if a table exists in the AADL database.
     * @param tableName name of the table
     * @return true if exists, false otherwise
     */
    public boolean tableExists(String tableName) {
	DatabaseMetaData dbm;
	ResultSet tables;
	boolean exists = false;
	try {
	    dbm = connObj.getMetaData();
	    tables = dbm.getTables(null, null, tableName, null);
	    exists = tables.next();
	} catch (SQLException e) {
	    e.printStackTrace();
	}
	return exists;
    }

    /**
     * Determines the type of the table from the meta info. 
     * @param tableName name of the table
     * @return type of the table
     */
    public String getTableType(String tableName) {
	ResultSet rs = executeSelectQuery("SELECT tableType FROM _meta WHERE tableName = '" + tableName + "';");
	String tableType = null;

	try {
	    if (rs.next()) 
		tableType = rs.getString("tableType");
	    else 
		throw new UnsupportedOperationException("No such table " + tableName);
		

	    if (rs.next()) {
		throw new UnsupportedOperationException("Ambiguous table name request: " + tableName);
	    }

	} catch (SQLException e) {
	    e.printStackTrace();
	}
	return tableType;
    }
    
    /**
     * Gets certain component's DB ID from a given table and component's name. 
     * @param componentTableName table that contains components. 
     * @param componentName name of the component
     * @return ID of the component if exists, -1 otherwise.
     */

    public int getComponentIndex(String componentTableName, String componentName) {
	int componentID = -1;
	ResultSet rs = executeSelectQuery("SELECT componentID FROM " + componentTableName + " WHERE componentName = '"
		+ componentName + "';");
	try {
	    if (rs.next())
		componentID = rs.getInt("componentID");
	    // } else --- this should not be done because search doesn't mean to
	    // be definitive
	    // throw new
	    // UnsupportedOperationException("Component name not found");

	    if (rs.next())
		throw new UnsupportedOperationException("Ambiguous component name");

	} catch (SQLException e) {
	    e.printStackTrace();
	}

	return componentID;
    }
    
    /**
     * Determines a component ID by searching through all tables. Relies on qualified names for unambiguity. 
     * @param componentName name of the component. 
     * @return the first occurence of the component, -1 if not found. 
     */
    public int getComponentIndexAcrossAllTables(String componentName) { 
	// search through all tables for a component named componentName
	ResultSet rs = executeSelectQuery("SELECT tableName FROM _meta WHERE tableType = 'component';");
	String tableCandidate;
	int idCandidate = -1;
	try {
	    // search for potential component tables that would have this component
	    while(rs.next()) {
		tableCandidate = rs.getString("tableName");
		idCandidate = getComponentIndex(tableCandidate, componentName);
		if (idCandidate != -1)
		    break;
	    }
	} catch (SQLException e) {
	    e.printStackTrace();
	}
	
	return idCandidate;
    }

    /**
     * Cleans up the tables in database and recreates an empty metainformation table. 
     */
    public void cleanDB() {
	System.out.println("Cleaning database from existing tables");

	try {
	    // find the existing tables
	    Statement st = connObj.createStatement();
	    ResultSet rs = st.executeQuery("SELECT concat('DROP TABLE IF EXISTS ', table_name, ';') as q"
		    + " FROM information_schema.tables WHERE table_schema = '" + mysqlDBName + "';");

	    // drop the existing tables
	    List<String> dropQueries = new ArrayList<String>();
	    while (rs.next()) {
		System.out.println(rs.getString("q"));
		dropQueries.add(rs.getString("q"));
	    }
	    executeUpdateQueries(dropQueries);

	    // add the metainfo table
	    executeUpdateQuery("CREATE TABLE IF NOT EXISTS _meta "
		    + "(tableID MEDIUMINT NOT NULL AUTO_INCREMENT, PRIMARY KEY(tableID), "
		    + "tableName varchar(255), tableType varchar(255), owner varchar(255));\n");

	} catch (SQLException e) {
	    e.printStackTrace();
	}

    }
}
