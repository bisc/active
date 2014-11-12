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

//////// To be included with the main battery //////////

// a helper for the monitor
typedef NeighborRow { 
	byte n[COLS];
	}
	
// tracks the required property and collects thermal neighbor data on it
inline HeatNeighborMonitor() { 
	NeighborRow neighbors[ROWS];
	byte dist;
	byte gr, cl; 
	byte cellDiscNum, groupDiscNum = 0;
	byte prevGroup;
	Cell c;
	CellRef cr, prevCr;

	// calculate cell neighbors
	// iterate through all groups and calculate distances to ones already visited, saving results in a matrix
	for (gr : 0 .. groupNum - 1) { 
		cellDiscNum = 0; // start over the cell counter in new group
		
		if	
		:: groups[gr].size > 0 && groups[gr].conn == disc -> 
			for(cl: 0 .. groups[gr].size - 1) { // iterate inside the group
				AssignCellRef(cr, groups[gr].cellref[cl]);
				AssignCell(c, cells[cr.x].cell[cr.y]);
				if
				:: c.conn == disc -> 
					// connection to previous cells within the group
					if 
					:: cellDiscNum != 0 -> 
						// check with the previous cell
						AssignDistance(dist, cr, prevCr);
						if
						:: dist <= TNDISTANCE -> 
							#ifdef OUTPUT
							printf("Monitor: detected in-group neighbors %d%d and %d%d\n", cr.x, cr.y, prevCr.x, prevCr.y);
							#endif
							neighbors[cr.x].n[cr.y]++;
							neighbors[prevCr.x].n[prevCr.y]++;
						:: else skip;
						fi;
					:: else skip;
					fi;

					cellDiscNum++;
					AssignCellRef(prevCr, cr);		
				:: else skip;
				fi;
			}
			// consider inputs and outputs
			// check input-output neighbors with previous group (only for non-first group)
			if
			:: groupDiscNum > 0 -> 
				AssignDistance(dist, groups[gr].input, groups[prevGroup].output);
				if
				:: dist <= TNDISTANCE -> 
					#ifdef OUTPUT
					printf("Monitor: detected between-group neighbors %d%d and %d%d\n", groups[gr].input.x, groups[gr].input.y, groups[prevGroup].output.x, groups[prevGroup].output.y);
					#endif
					neighbors[groups[gr].input.x].n[groups[gr].input.y]++;
					neighbors[groups[prevGroup].output.x].n[groups[prevGroup].output.y]++;
				:: else skip;
				fi;
			:: else skip;
			fi;
			
			groupDiscNum++;
			prevGroup = gr;
		:: else skip;
		fi;
	}

	// calculate neighbor stats and zero the matrix for verification
	// have to zero the counters because they were -1 before
	v0 = 0; 
	v1 = 0; 
	v2 = 0; 
	v3 = 0; 
	for(gr: 0 .. ROWS-1) {
		for (cl: 0 .. COLS-1) { 
			if
			:: neighbors[gr].n[cl] == 1 -> v1++;
			:: neighbors[gr].n[cl] == 2 -> v2++;
			:: neighbors[gr].n[cl] == 3 -> v3++;
			:: else skip;//printf("weird neighbors of %d%d are %d\n", gr, cl, neighbors[gr].n[cl]);
			fi;

			neighbors[gr].n[cl] = 0;
		} 
	}
	// TODO this assumes that the battery is fully scheduled. It's not true when terminate is set, but then again it's not part of verification.
	v0 = CELLSREQD * GROUPSREQD - v1 - v2 - v3;

	#ifdef OUTPUT
	printf("Monitor: v0 = %d, v1 = %d, v2 = %d, v3 = %d, disc groups = %d\n", v0, v1, v2, v3, groupDiscNum);
	#endif

	//byte n = v1 + v2 + v3;
	//assert(2*n*v1 + 2*n*v3 >= v1+v2+v3);// using a heat goodness function (2nv1+2nv3)/(v1+v2+v3) with cutoff 1. -- holds usually
	//assert(2*n*v1 + 2*n*v3 >= v1+v2+v3);// holds usually  

	//assert((v1+v3)*(v1+v3) >= v2);// using a heat goodness function k(v1+v3) vs v2 with k = v1+v3. 
	//assert((v1+v3)*(v1+v3) >= 3*v2); -- broken with weighed sched 2, 3, no group form
	//assert((v1+v3)*(v1+v3) >= 2*v2); -- broken with weighed sched 2, 3, no group form
	//assert((v1+v3)*(v1+v3) >= v2); --    holds with weighed sched 2, 3, no group form
	//assert((v1+v3)*(v1+v3) >= v2); --    holds with weighed sched 2, 3, with group form
	//assert((v1+v3)*(v1+v3) >= v2); --    holds with unweighed sched 2, 3, no group form

	//assert(2*(v1 + v3) >= v2);// using sagar's function 
	//assert(2*(v1 + v3) >= v2);// holds usually
	//assert(3*(v1 + v3) >= 2*v2);// holds with unweighed sched 2, 3, no group form
	//assert(3*(v1 + v3) >= 2*v2);// holds with weighed sched 2, 3, no group form
	//assert(3*(v1 + v3) >= 2*v2);// broken with weighed sched 2, 3,  group form

	// reset all variables for verification
	// n=0;
	// v1 = 0; v2 = 0; v3 = 0;

	gr = 0; cl = 0; 
	cellDiscNum = 0; groupDiscNum = 0;
	prevGroup = 0;
	ResetCell(c);
	ResetCellRef(cr); ResetCellRef(prevCr);
}

