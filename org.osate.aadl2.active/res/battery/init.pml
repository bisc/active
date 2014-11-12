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

/////////////// Initializations for battery model ////////////////////

// initializes the matrix with random connections
inline InitAllRandom(){
		byte i, j, k;
		mtype b;
		Cell c;
		CellRef cr; 

		// set random connection values for group membership and cell connectivity
		for(i : 0 .. ROWS - 1) { 
			for (j : 0 .. COLS - 1) {
				select (b: idle .. disc); 
				c.conn = b;
				select (k: 0 .. MAXGRNUM -1 ); 
				c.group = k;
				AssignCell(cells[i].cell[j], c);

				AddCellRef(k, i, j);
			}
		}

		// set random connectivity for groups
		for(i : 0 .. MAXGRNUM - 1) { 
			select (b: idle .. disc); 
			groups[i].conn = b;
			}

		// using up the whole space
		groupNum = MAXGRNUM;
	}

// all cells are in one group linearly connected to one another
inline InitSingleGroup() {
	byte i, j;
	
	assert(MAXGRSIZE >= ROWS*COLS);

	CleanCellRefs();

	for(i : 0 .. ROWS - 1) { 
		for (j : 0 .. COLS - 1) {
			cells[i].cell[j].group = 0;

			AddCellRef(0, i, j);
		}
	}

	groupNum = 1;
}
	
// put cells into parallel groups composed by rows. Each group size of groupsize.
inline InitParallelGroups(groupSize) {
	byte i, j, group = 0, cellCount = 0;

	assert(ROWS*COLS <= MAXGRNUM * groupSize);
	assert(groupSize <= MAXGRSIZE);

	CleanCellRefs();

	#ifdef COLSTOROWS
	for (j : 0 .. COLS - 1) {
		for(i : 0 .. ROWS - 1) { 
	#endif
	#ifdef ROWSTOCOLS
	for(i : 0 .. ROWS - 1) { 
		for (j : 0 .. COLS - 1) {
	#endif
			if
			:: cellCount == groupSize -> 
				cellCount = 0;
				group++;
			:: else skip;
			fi;

			cells[i].cell[j].group = group;
			AddCellRef(group, i, j);

			cellCount++;
		}
	}

	// can set groupNum aggressively (if groupcount > CELLSREQD) or safely (always drop the last group)
	if
	:: cellCount == 0 -> 
		groupNum = group;
	:: cellCount >= 1 -> // filled up the last group
		groupNum = group + 1;
	fi; 
}

// attribute initializations
inline InitGroupConn(x) { 
	byte i;
	for(i : 0 .. MAXGRNUM - 1) { 
		groups[i].conn = x;
		}
	}

inline InitCellConn(x) { 
	byte i, j;
	for(i : 0 .. ROWS - 1) { 
		for (j : 0 .. COLS - 1) {
			cells[i].cell[j].conn = x;
		}
	}
	}


inline InitCellCharge(x) { 
	byte i, j;
	for(i : 0 .. ROWS - 1) { 
		for (j : 0 .. COLS - 1) {
			cells[i].cell[j].charge = x;
		}
	}
}
