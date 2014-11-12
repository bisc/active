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

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.channels.FileChannel;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;

import org.eclipse.emf.common.util.EList;
import org.osate.xtext.aadl2.contracts.Contract.Expression;
import org.osate.xtext.aadl2.contracts.Contract.LTLExpression;
import org.osate.xtext.aadl2.contracts.Contract.QFGTMREF;

/**
 * Commonly used functions for contracts.
 * @author ivan
 *
 */
public class ContractUtils {


	/////////////////////// CONTRACT GRAMMAR AND TYPE OPERATIONS ///////////////////////////

	/**
	 * Determines if an expression is an ltl expression. 
	 * @param e expression
	 * @return true if an ltl expression, otherwise false
	 */
	public static boolean isLtl(Expression e) { 
		// TODO make more complicated to check if there is any LTL deep in the expression
		return e instanceof LTLExpression;
	}

	/**
	 * Converts a QFGTMREF to an equivalent string, removing dots. 
	 * @param ref a qfgtmref
	 * @return string
	 */
	public static String QFGTMREFtoString(QFGTMREF ref) {
		Iterator<String> i = ref.getIds().iterator();
		String result = "";
		while (i.hasNext()) {
			result += i.next();
		}
		return result;
	}

	/**
	 * Create a single dot-separated string from a list of strings
	 * @param lst list of strings
	 * @return dot-appended string
	 */
	public static String appendAgregateStringList(EList<String> lst) {
		Iterator<String> it = lst.iterator();
		String id = "";

		while (it.hasNext()) {
			id += it.next();
			if (it.hasNext())
				id += ".";
		}

		return id;
	}

	/**
	 * Create a set of prefix strings (referenced identifiers) from a QFGTMREF
	 * @param name QFGTMREF
	 * @return set
	 */
	public static Set<String> QFGTMREFtoSet(QFGTMREF name) { 
		Set<String> ss = new HashSet<String>();
		List<String> l = name.getIds();
		if (l.size() == 1)
			ss.add(l.get(0));	    
		else if (l.size() == 2) {
			ss.add(l.get(0));
			ss.add(l.get(0) + "." + l.get(1));
		} else throw new UnsupportedOperationException("Only support QFGTMREF with 2 parts");
		return ss;
	}

	/**
	 * Returns an SMT type by a string value of a number
	 * @param value string of a number
	 * @return name of the smt type
	 */
	public static String decideSmtTypeByValue(String value) {
		try {
			Integer.parseInt(value);
			return "Int";
		} catch (NumberFormatException e) {
			//	    System.out.println("Not an int");
		}

		try {
			Float.parseFloat(value);
			return "Real";
		} catch (NumberFormatException e) {
			//	    System.out.println("Not a float");
		}

		return "String";
	}

	/**
	 * Convert a database representation of a number to a spin representation. Issues a warning if the number is not an integer.  
	 * @param dbNum database number as a string
	 * @return a spin number as a string
	 */
	public static String toSpinNumber(String dbNum) { 
		if (dbNum.contains(".")) {
			if(dbNum.matches("(\\d)+\\.(0)+")) {
				//		System.out.println("Integer: " + dbNum);
				return dbNum.split("\\.")[0];
			} else { 
				System.out.println("WARNING: spin launched on a noninteger: " + dbNum + " - flooring");
				double dbDouble = Double.parseDouble(dbNum); 
				return String.valueOf((Math.floor(dbDouble))); 
			}
		} else 
			return dbNum; 
	}

	///////////////////// FILE OPERATIONS ///////////////////////    

	/**
	 * Write a string to file.
	 * @param path to the file
	 * @param output string to write
	 * @param append if true, append to file, otherwise overwrite
	 */
	public static void writeToFile(String path, String output, boolean append) {
		// create a directory
		File file;
		FileWriter writer;

		// handle writing
		try {
			file = new File(path);
			writer = new FileWriter(file, append);
			writer.write(output);
			writer.close();
			System.out.println("Written to " + file.getAbsolutePath());
		} catch (IOException e1) {
			System.out.println("Writing to file failure");
			e1.printStackTrace();
		}
	}

	/** 
	 * Replace all strings in file as defined by a map: all key occurences are replaced by values 
	 * @param filePath path to the file 
	 * @param substitution replacement map 
	 */
	public static void replaceStringsInFile(String filePath, Map<String, String> substitution) { 
		Path path = Paths.get(filePath);
		Charset charset = StandardCharsets.UTF_8;

		String content;
		try {
			content = new String(Files.readAllBytes(path), charset);
			for(String s: substitution.keySet()) { 
				// escape special regex characters like $ or \
				content = content.replaceAll(Matcher.quoteReplacement(s), substitution.get(s));
			}
			Files.write(path, content.getBytes(charset));
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/** 
	 * Copies a file from source path to destination path. 
	 * @param sourcePath path to file that is copied
	 * @param destPath path to the destination 
	 * @throws IOException if copying doesn't complete
	 */
	public static void copyFile(String sourcePath, String destPath) throws IOException {
		File sourceFile = new File(sourcePath);
		File destFile = new File(destPath);

		if(!destFile.exists()) {
			destFile.createNewFile();
		}

		FileChannel source = null;
		FileChannel destination = null;

		try {
			source = new FileInputStream(sourceFile).getChannel();
			destination = new FileOutputStream(destFile).getChannel();
			destination.transferFrom(source, 0, source.size());
		}
		finally {
			if(source != null) {
				source.close();
			}
			if(destination != null) {
				destination.close();
			}
		}
	}

	////////////////////////////// OTHER //////////////////////////

	/**
	 * Run a shell command in the specified directory.  
	 * @param command command to be run
	 * @param dir the directory to run the command in. If dir is null, runs it in the current directory of the process.
	 * @return output of the command
	 */
	public static String executeShellCommand(String command, File dir) {

		StringBuffer output = new StringBuffer();
		System.out.println("Shell command:" + command);

		Process p;
		try {
			p = Runtime.getRuntime().exec(command, null, dir);
			p.waitFor();
			BufferedReader reader = 
					new BufferedReader(new InputStreamReader(p.getInputStream()));

			String line = "";			
			while ((line = reader.readLine())!= null) {
				output.append(line + "\n");
			}

		} catch (Exception e) {
			e.printStackTrace();
		}

		return output.toString();

	}
}