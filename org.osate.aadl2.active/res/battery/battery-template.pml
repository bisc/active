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

///////////////////////// A battery model in Promela /////////////////////
// This model represents dynamic battery cell interconnections using various schedulers.

#include "$CONFIGFILENAME"

#include "util.pml"
#include "init.pml"
#include "sched.pml"
#include "monitor.pml"

// Data structures: 
mtype = {disc, char, idle}; // possible cell and group connectivity statuses

// cells 
typedef Cell { 
	byte group; // redundant with groups
	mtype conn; // connectivity status
	bool charge; //alternative to charges and discharges
}

typedef CellRow { 
	Cell cell[COLS]; 
	}

CellRow cells [ROWS]; // a physical matrix of cells, based on their location

// groups
typedef CellRef { // a reference to a cell
	byte x, y;
	}

typedef Group { // a single group
	CellRef cellref [MAXGRSIZE]; // this is REDUNDANT with cellgr but may be easier to use in some cases.
	byte size; 
	mtype conn;
	CellRef input, output;// tracks which cells are connected as input and output connection. May be the same cell.
	}

Group groups [MAXGRNUM];// groups of cells. Groups are connected in parallel to each other.
byte groupNum;// the current number of groups of size > 0, a shortcut for discharging schedulers to not iterate MAXGRNUM 

// termination condition flag
bool terminate = false; 

// the runtime aggregates about thermal neighbors
short v0 = -1, v1 = -1, v2 = -1, v3 = -1; 

init { 
	atomic { 
		// verify the constraints on input parameters 
		assert(MAXGRNUM*MAXGRSIZE >= ROWS*COLS);
		assert(CELLSREQD <= MAXGRSIZE);
		assert(GROUPSREQD <= MAXGRNUM);
		assert(CELLSREQD*MAXGRNUM >= ROWS*COLS);
		assert(CELLSREQD*GROUPSREQD <= ROWS*COLS);

		InitCellConn(idle);
		InitGroupConn(idle);
		InitCellCharge(true);

		// static setting of groups
		//InitSingleGroup();
		InitParallelGroups(CELLSREQD);  // group size

		#ifdef OUTPUT
		Print();	
		#endif
	}

	run Manager();
}

// A function to advance time
inline AdvancePeriod(){ 
	byte i, j;	
	Cell c;

	//foreach cell
	for (i: 0 .. ROWS - 1) { 
		for (j: 0 .. COLS -1) { 
			AssignCell(c, cells[i].cell[j]);		
			if
			:: c.conn == idle -> skip;
			:: c.conn == char -> 
				//printf("Advance: considering cell %d%d for charge \n", i, j);
				if
				:: true -> skip;
				:: true -> c.charge = true;
				fi;
			:: c.conn == disc ->
				//printf("Advance: considering cell %d%d for discharge \n", i, j);
				if
				:: true -> skip;
				:: true -> c.charge = false; 
				fi;
			fi;		
			AssignCell(cells[i].cell[j], c);		
		}
	}

	#ifdef OUTPUT
	printf("Manager: advanced period, groupNum %d\n", groupNum);
	#endif

	// assign local vars to 0 for verification purposes
	i = 0; 
	j = 0;
	ResetCell(c);
}

// the main process
proctype Manager(){ 
	#ifdef OUTPUT
	printf("Started the simulation\n");
	#endif	
	do ::
       		d_step { 
			#ifdef OUTPUT
			Print();	
			#endif

			// redistribute parallel groups of cells
			#ifdef FGURR
			UnweightedKRRDischarge();
			#elif defined FGWRR
			WeightedKRRDischarge();
			#elif defined GPWRR
			GroupFormationScheduler(CELLSREQD); // size of group
			WeightedKRRDischarge();
			#else 
			ERROR_NO_SCHEDULER_DEFINED;
			#endif
	
			//d_step { // charge scheduler (for the idle cells)
			//QuickAverageChargingScheduler();
			//}

			HeatNeighborMonitor();

			#ifdef OUTPUT
			Print();
			#endif		
		}
		atomic { 
			// reset the state for verification
			v0 = -1; 
			v1 = -1; 
			v2 = -1; 
			v3 = -1;

			if
			:: !terminate -> 
				AdvancePeriod();
				
			:: else 
				terminate = false; //reset state
				break;
			fi;
			//CleanCellRefs();
			// maybe reset all the groups and connections here when using a group scheduler? 
		}
	od;

	#ifdef OUTPUT
	printf("Terminated the simulation\n");
	#endif
}

LTL 
//ltl p1 { []( ((v1 == -1 && v2 == -1 && v3 == -1) || terminate) || (2*(v0 + v2 + v3) >= v1) )}


// Potential properties below:

// row 0 discharges all at the same time
/* 
[]!( 
cells[0].cell[0].conn == disc && 
cells[0].cell[1].conn == disc &&
cells[0].cell[2].conn == disc &&
cells[0].cell[3].conn == disc
)

// column 0 discharges all at the same time 
/*
[]!( 
	cells[0].cell[0].conn == disc && 
	cells[1].cell[0].conn == disc && 
	cells[2].cell[0].conn == disc && 
	cells[3].cell[0].conn == disc  
)
*/
