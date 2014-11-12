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

////////////////////// Utilities for battery model in Promela /////////////////////////////
//// To be included with the model itself ////

inline SwapInt(arg1, arg2) { 
	int _t = arg1;
	arg1 = arg2;
	arg2 = _t;

	_t = 0;
}

inline SwapShort(arg1, arg2) { 
	short _t = arg1;
	arg1 = arg2;
	arg2 = _t;

	_t = 0;
}

// a cell copying operation
inline AssignCell(arg1, arg2) { 
	arg1.group = arg2.group;
	arg1.conn = arg2.conn;
	arg1.charge = arg2.charge;
}

// a cell ref copying operation
inline AssignCellRef(cellref1, cellref2) { 
	cellref1.x = cellref2.x;
	cellref1.y = cellref2.y;
}

// a cellref adding operation
inline AddCellRef(groupNumber, cellx, celly) { 
	groups[groupNumber].cellref[groups[groupNumber].size].x = cellx;
	groups[groupNumber].cellref[groups[groupNumber].size].y = celly;
	groups[groupNumber].size++;
}

// calculates the 1-norm distance between cells
inline AssignDistance(distVar, cellref1, cellref2) { 
	if
		:: cellref1.x >= cellref2.x -> 
			distVar = cellref1.x - cellref2.x;
		:: else 
			distVar = cellref2.x - cellref1.x;
	fi;

	if
		:: cellref1.y >= cellref2.y -> 
			distVar = distVar + cellref1.y - cellref2.y;
		:: else 
			distVar = distVar + cellref2.y - cellref1.y;
	fi;
}

// reset cell state
inline ResetCell(_c) { 
	_c.group = 0; 
	_c.conn = idle;
	_c.charge = false;
	}

// reset cell ref state
inline ResetCellRef(_cr) { 
	_cr.x = 0;
	_cr.y = 0;
	}

// reset group's input and output
inline ResetGroupInputOutput(_g) { 
	groups[_g].input.x = 0;
	groups[_g].input.y = 0;
	groups[_g].output.x = 0;
	groups[_g].output.y = 0;
}

// purges all cell references from groups
inline CleanCellRefs() { 
	byte _i, _j; 
	for (_i : 0 .. MAXGRNUM - 1) { 
		groups[_i].size = 0;
		groups[_i].input.x = 0;
		groups[_i].input.y = 0;
		groups[_i].output.x = 0;
		groups[_i].output.y = 0;

		for(_j: 0 .. MAXGRSIZE-1) { 
			groups[_i].cellref[_j].x = 0;
			groups[_i].cellref[_j].y = 0;
		}
	} 

	groupNum = 0;

	// not necessary because group formation already changes groups
	/*for (_i: 0 .. ROWS - 1) {
		for (_j: 0 .. COLS - 1) {
		cells[_i].cell[_j].group = 0;
		}
	} */

	_i = 0;
	_j = 0;
}

// printout cell groups and connectivity 
inline Print(){  
	Cell _c;
        byte _i, _j; 

        for(_i : 0 .. ROWS - 1) {  
		for (_j : 0 .. COLS - 1) { 
			AssignCell(_c, cells[_i].cell[_j]);
			//G Group number C cell connectivity status GC group connectivity status  D discharges till rest R rests till charge
			printf("g%dc%d", _c.group, _c.charge); 
			
		} 
		printf("\n"); 

		for (_j : 0 .. COLS - 1) { 
			printf("      "); 
		} 
		printf("\n"); 
	} 

	for(_i: 0 .. groupNum - 1){ 
		printf("gr%d: in %d%d, out %d%d\n", _i, groups[_i].input.x, groups[_i].input.y, groups[_i].output.x, groups[_i].output.y);
	}

	printf("\n"); 

	ResetCell(_c);
	_i = 0; 
	_j = 0; 
} 
