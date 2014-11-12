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

// Battery dimensions
#define ROWS $ROWS //4
#define COLS $COLS //4

// Battery output requirements 
#define GROUPSREQD $PARALREQ //3 // groups required in parallel to satisfy the current requirement
#define CELLSREQD $SERIALREQ //3 // cells required in serial to satisfy the voltage requirement

#define $SCHEDULER
//#define FGURR // fixed groups, unweighted round robin
//#define FGWRR // fixed groups, weighted round robin
//#define GPWRR // group packing, weighted round robin

#define LTL $LTL// ltl p1 { []( ((v1 == -1 && v2 == -1 && v3 == -1) || terminate) || (2*(v0 + v2 + v3) >= v1) )}
//#define LTL ltl p1{ 1==0}
//[](  \
//((v1 == -1 && v2 == -1 && v3 == -1) || terminate) || \
//(2*(v0 + v2 + v3) >= v1) \
//) \
}

//[]true \
//[]((v1 == -1 && v2 == -1 && v3 == -1) || terminate || (v1 > v3) )
// [] ((v1 == -1 || v2 == -1 || v3 == -1 || terminate) || CONTRACT )

#define HEADTOHEAD // enable this to connect groups head-to-head
//#define MIDTOMID 
//#define HEADTOTAIL

#define ROWSTOCOLS 
//#define COLSTOROWS // enable this to form groups by columns instead of rows in static init and group formation scheduler


//#define LTL 
// -----------------

#define TNDISTANCE 2 // max distance by 1-norm between two cells to be considered thermal neighbors

// memory allocation for groups
#define MAXGRNUM ((ROWS*COLS)/CELLSREQD + 1) //8 // max number of groups 
#define MAXGRSIZE ((ROWS*COLS)/GROUPSREQD + 1)//8 // max number of cells in a group

// all constants are assumed to fit into a byte
// CONSTRAINT occupancy: MAXGRNUM * MAXGRSIZE >= ROWS*COLS
// CONSTRAINT single group: MAXGRSIZE >= ROWS*COLS
// CONSTRAINT: CELLSREQD <= MAXGRSIZE
// CONSTRAINT: GROUPSREQD <= MAXGRNUM
// CONSTRAINT: CELLSREQD*MAXGRNUM >= ROWS*COLS
// CONSTRAINT: CELLSREQD*GROUPSREQD <= ROWS*COLS

#define KGROUPS GROUPSREQD // a parameter of weighted and unweighted KRR: select K most charged groups.
