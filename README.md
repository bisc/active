# ACTIVE #

This is a source repository for ACTIVE (Analysis contraCT Integration VErifier) - a tool for integrating analysis contracts in cyber-physical system design. It is an OSATE2 plugin that introduces a contracts annex and allows a user to verify analysis contracts.

### Installation ###

* Follow the [instructions](https://wiki.sei.cmu.edu/aadl/index.php/Getting_Osate_2_sources) for installing OSATE2.
* Check out [osate2-core](https://github.com/osate/osate2-core) at 2.0.8-release; generate Properties and AADL grammars. 
* Check out the ACTIVE source (latest release recommended) from this repository. You will need all the contained projects. 
* Create a folder src-gen in org.osate.xtext.aadl2.contracts.
* Install MYSQL server. On ubuntu, it's packages mysql-server, mysql-common, and mysql-client.
* Set up MYSQL server with username=root and password=root. Start MYSQL server with default configuration (at port 3306). Create a database aadl in mysql.
* Install latest [Z3](https://z3.codeplex.com/releases) and make sure command "z3" is available through PATH. If the latest release produces errors, try version 4.3.1.
* Install latest [Spin](http://spinroot.com/spin/Src/index.html) and make sure command "spin" is available through PATH. If the latest release produces errors, try version 6.2.5. 
* Run the language infrastructure generation script GenerateContract.mwe2 in org.osate.xtext.aadl2.contracts.contract. Re-run it with every grammar change.
* Start OSATE2, import your AADL projects. ACTIVE example projects are available [here](https://github.com/bisc/active-examples). 
* Create an instance of a system (e.g., right-click a system implementation and select Instantiate System). 
* Select the instance and click the ACTIVE button in the toolbar. 
* Double-click the analysis you want to run, and ACTIVE will execute and verify a sequence of analyses. 

### Who do I talk to? ###

* Ivan Ruchkin iruchkin@cs.cmu.edu
* Dionisio De Niz dionisio@sei.cmu.edu
* Sagar Chaki chaki@sei.cmu.edu
* David Garlan garlan@cs.cmu.edu

### Version history ###

* 0.2.0: ACTIVE release for AVICPS14, November 2014.
	* osate2-core: 2.0.8-release, commit 3cf54645c169309170478d24a8496cfbf1fb1b34 (September 2014) 

### Copyright ###

Copyright (c) 2014 Carnegie Mellon University. All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following acknowledgments
and disclaimers.

2. Redistributions in binary form must reproduce the above
copyright notice, this list of conditions and the following
disclaimer in the documentation and/or other materials provided
with the distribution.

3. The names "Carnegie Mellon University," "SEI" and/or "Software
Engineering Institute" shall not be used to endorse or promote
products derived from this software without prior written
permission. For written permission, please contact
permission@sei.cmu.edu.

4. Products derived from this software may not be called "SEI" nor
may "SEI" appear in their names without prior written permission of
permission@sei.cmu.edu.

5. Redistributions of any form whatsoever must retain the following
acknowledgment:

This material is based upon work funded and supported by the
Department of Defense under Contract No. FA8721-05-C-0003 with
Carnegie Mellon University for the operation of the Software
Engineering Institute, a federally funded research and development
center.

Any opinions, findings and conclusions or recommendations expressed
in this material are those of the author(s) and do not necessarily
reflect the views of the United States Department of Defense.

NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE
ENGINEERING INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS"
BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO WARRANTIES OF ANY KIND,
EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT
LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR MERCHANTABILITY,
EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL. CARNEGIE
MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
INFRINGEMENT.

This material has been approved for public release and unlimited
distribution.

DM-0001534
