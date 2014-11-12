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

/////////////////// Schedulers for battery ////////////////
/////////////////// To be included with the original battery file /////////////////

// creates groups out of cells
// should NOT be used with the unweighted krr scheduler because it messes up the groups, on which the latter implicitly relies
inline GroupFormationScheduler(groupSize) { 
	byte i, j;
	byte cellCount = 0;
	byte group = 0;
	CellRef cr; 
	
	// clean all group references
	CleanCellRefs();

	// put all charged cells into groups 
	#ifdef COLSTOROWS
	for (j : 0 .. COLS - 1) {
		for(i : 0 .. ROWS - 1) {
	#endif
	#ifdef ROWSTOCOLS
	for(i : 0 .. ROWS - 1) {
		for (j : 0 .. COLS - 1) {
	#endif
			if
			:: cells[i].cell[j].charge -> 
				#ifdef OUTPUT
				//printf("Groupform: Adding %d%d - charged\n", i, j);
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
			:: else skip;
			fi;
		}
	}

	// continue adding to the same group
	// without changing the cell counter or group #

	// put all uncharged cells into groups
	for(i : 0 .. ROWS - 1) {
		for (j : 0 .. COLS - 1) {
			if
			:: !cells[i].cell[j].charge -> 
				#ifdef OUTPUT
				//printf("Groupform: Adding %d%d - uncharged\n", i, j);
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
			:: else skip;
			fi;
		}
	}

        if
	:: cellCount == 0 ->
		groupNum = group;
	:: cellCount >= 1 -> // filled up the last group
		groupNum = group + 1;
	fi;

	// reset all local variables for verification
	i = 0;
	j = 0;
	group = 0;
	cellCount = 0;
}


// Discharges best KGROUPS groups and charges the worst one. 
inline WeightedKRRDischarge(){ 

        short chargeByGroup[MAXGRNUM]; // charge in each group, indexed by original group IDs.
	short groupByCharge[MAXGRNUM]; // groups sorted by charge

	byte gr, i, j; // counters
	Cell c;
	CellRef cr;
	short temp;// to exchange between variables, stores -1 sometimes
	short charge;// sums up total charge, which may (?) exceed 255

	// init arrays
	for(i: 0 .. MAXGRNUM - 1) { 
		groupByCharge[i] = -1;
		chargeByGroup[i] = -1;
	}

	// iterate through groups to determine the amount of charge left in them
	for(gr: 0 .. groupNum - 1) { // used to be MAXGRNUM
		// INVARIANT: a group's charge has been recorded in chargeByGroup iff the group is in the array groupByCharge.

		// find a group's charge
		charge = 0;
		for(i: 0 .. groups[gr].size - 1) { 
			AssignCellRef(cr, groups[gr].cellref[i]);		
			AssignCell(c, cells[cr.x].cell[cr.y]);
			if
				:: c.charge -> charge++; 
				:: else skip;
			fi;
		}

		chargeByGroup[gr] = charge;

		#ifdef OUTPUT
		//printf("DS: Group %d charge: %d\n", gr, charge);
		#endif 

		// insertion sort into groupsByCharge
		for (i: 0 .. groupNum-1) { // used to be MAXGRNUM
			if
			:: groupByCharge[i] == -1 -> 
				groupByCharge[i] = gr;
				break;
			:: else // in this case the i-th position has a valid group
				if
				:: charge > chargeByGroup[groupByCharge[i]] -> 
					temp = groupByCharge[i]; 
					groupByCharge[i] = gr;
					for(j: i+1 .. MAXGRNUM-1) { // shift-right cycle
						SwapShort(temp, groupByCharge[j]);

						// may cut the cycle short
						if
						:: temp == -1 -> break;
						:: else skip;
						fi;
						}
					break;// exit the insertion cycle
				:: else skip;
				fi;
			fi;
		}
	}

	#ifdef OUTPUT
	printf("DS: groupbycharge     :");
	for (i: 0 .. groupNum-1) { // used to be MAXGRNUM
		printf(" %d", groupByCharge[i]);
	}
	printf("\n");

	printf("DS: chargebygroup[gbc]:");
		for (i: 0 .. groupNum-1) { 
			printf("%d", chargeByGroup[groupByCharge[i]]);
		}
	printf("\n");
	#endif

	// assign group connectivity
	for(i: 0 .. groupNum - 1) { // used to be MAXGRNUM
		gr = groupByCharge[i];// group id 

		// the best K groups are discharging
		if 
		:: i <= KGROUPS - 1 && chargeByGroup[gr] > 0 -> groups[gr].conn = disc;
		:: (i > KGROUPS - 1 && i <= MAXGRNUM - 1) || (i <= KGROUPS - 1 && chargeByGroup[gr] == 0) -> groups[gr].conn = idle; 
		//:: i == MAXGRNUM - 1 -> groups[gr].conn = char; // charge the last/worst one
		fi;

		#ifdef OUTPUT
		printf("DS:Group %d #%d conn: %e", gr, i, groups[gr].conn);
		#endif

		// assign cell connectivity within group: currently dumb and may not satisfy the requirement
		ScheduleGroupCellsDischarge(gr);
	}	

	// reset all local variables for verificaiton
	for (i: 0 .. MAXGRNUM - 1) { // has to reset all memory to remove -1's
		chargeByGroup[i] = 0;
		groupByCharge[i] = 0;
		}

	i = 0;
	j = 0; 
	gr = 0;

	ResetCell(c);
	ResetCellRef(cr);

	temp = 0;
	charge = 0;
}

// Discharges KGROUPS in a row without regard to their charges
inline UnweightedKRRDischarge(){ 
	Cell c;
	CellRef cr;
	byte i, j;
	byte dischargeCount;
	short firstDischargedGr = -1;

	// iterate through groups to see which ones are discharging
	for(i : 0 .. groupNum - 1) { 
		if
		::groups[i].conn == disc && groups[i].size > 0 ->
			firstDischargedGr = i; 
			break;
		:: else skip;
		fi;
	}

	// set group statuses
	if
	:: firstDischargedGr == -1 -> // first iteration: discharge first K groups
		dischargeCount = KGROUPS;
		for(i: 0 .. groupNum - 1) { 
			// stop if assigned as many discharge groups as needed
			if 
			:: dischargeCount > 0 && groups[i].size > 0 -> 
				groups[i].conn = disc;
				dischargeCount--;
			:: else skip;
			fi;

			#ifdef OUTPUT
			printf("DS: Group %d conn: %e", i, groups[i].conn);
			#endif

			ScheduleGroupCellsDischarge(i);
		}
	:: else  // non-first iteration: discharge next K groups
		// ASSUMES that there are contiguous KGROUPS discharging
		dischargeCount = 0;
		for(i: 0 .. groupNum - 1) {
			j = (firstDischargedGr + i) % groupNum;
			if 
			:: groups[j].conn == disc -> // idle
				dischargeCount++; 
				groups[j].conn = idle;
			:: groups[j].conn == idle ->  // discharge or skip 
				if
				:: dischargeCount > 0 -> 
					groups[j].conn = disc;
					dischargeCount--;
				:: else skip;
				fi;
			:: groups[j].conn == char -> 
				if
				:: dischargeCount > 0 -> // discharge or set to idle
					groups[j].conn = disc;
					dischargeCount--;
				:: else groups[j].conn = idle;
				fi;
			fi;

			#ifdef OUTPUT
			printf("DS: Group %d conn: %e ", j, groups[j].conn);
			#endif

			// set cell charges and determine input and outputs
			ScheduleGroupCellsDischarge(j);

			#ifdef OUTPUT
			printf("in: %d%d out: %d%d", groups[j].input.x, groups[j].input.y, groups[j].output.x, groups[j].output.y);
			#endif
			}
	fi;

	// reset local variables for verification
	ResetCell(c);
	ResetCellRef(cr);
	i = 0;
	j = 0; 
	firstDischargedGr = 0; 
	dischargeCount = 0;
}

// propagates the group charge to each cell charge: 
// idle: all idle
// char: all char
// disc: puts CELLSREQD number of charged cells in the group to discharge. If not sufficient, 
inline ScheduleGroupCellsDischarge(_gr) { 
	Cell _c; 
	CellRef _cr; 
	byte _cellCount = 0; // number of cells remaining to assign to discharge
	byte _i;// cell counter in a group
	for (_i : 0 .. groups[_gr].size - 1) { 
			AssignCellRef(_cr, groups[_gr].cellref[_i]);		
			AssignCell(_c, cells[_cr.x].cell[_cr.y]);

			if 
			:: groups[_gr].conn == char -> // this scheduler doesn't deal with charging
				assert(false);//_c.conn = char;
			:: groups[_gr].conn == idle -> // set all to idle
				_c.conn = idle;
				ResetGroupInputOutput(_gr);
			:: groups[_gr].conn == disc -> 
				// set the required # of cells in the group to its status
				if 
				:: _cellCount < CELLSREQD && _c.charge -> 
					_c.conn = disc;
					// set the cell as an out
					InterGroupConnectivityScheduler(_cellCount, _gr, CELLSREQD, _cr.x, _cr.y);

					_cellCount++;

				:: else 
					_c.conn = idle; 
				fi; 
	
				#ifdef OUTPUT
				printf("cell %d%d conn: %e", _cr.x, _cr.y, _c.conn);
				#endif 		
						
			fi; 
			AssignCell(cells[_cr.x].cell[_cr.y], _c);
	}

	// terminate if haven't been able to assign enough cells in a discharging group
	#ifdef OUTPUT
	if 
	:: groups[_gr].size > 0 &&_cellCount < CELLSREQD && groups[_gr].conn == disc -> 
		terminate = true;
		printf("Couldn't assign all cells");
	:: else skip; 
	fi;
	printf("\n");
	#endif

	// reset all local variables
	ResetCell(_c);
	ResetCellRef(_cr);
	_i = 0;
	_cellCount = 0;
}

inline InterGroupConnectivityScheduler(_cell, _group, _groupSize, _i, _j) {
	#ifdef HEADTOHEAD
	// in is in the head, out is in the head
		if
		:: _cell == 0 -> 
			//printf("IGC group %d: assigning %d%d as input and output", _group, _i, _j);
			groups[_group].input.x = _i;				
			groups[_group].input.y = _j;				
			groups[_group].output.x = _i;				
			groups[_group].output.y = _j;				
		:: else skip; 
		fi;
	#endif
	#ifdef MIDTOMID 
	// connect cells in the middle of the group
	if
		:: _cell == _groupSize/2 -> 
			//printf("IGC group %d: assigning %d%d as input and output", _group, _i, _j);
			groups[_group].input.x = _i;				
			groups[_group].input.y = _j;				
			groups[_group].output.x = _i;				
			groups[_group].output.y = _j;				
		:: else skip; 
	fi;		
	#endif
	#ifdef HEADTOTAIL
	// in is in the head, out is in the tail
		if
		:: _cell == 0 -> 
			//printf("IGC group %d: assigning %d%d as input", _group, _i, _j);
			groups[_group].input.x = _i;				
			groups[_group].input.y = _j;				
		:: _cell == _groupSize - 1 -> 
			//printf("IGC group %d: assigning %d%d as output", _group, _i, _j);
			groups[_group].output.x = _i;				
			groups[_group].output.y = _j;				
		:: else skip; 
		fi;
	#endif
}

// find the first uncharged idle cell and charge it
// ASSUMES that is called after a discharging scheduler
inline QuickAverageChargingScheduler() { 
	Cell c;
	byte i, j; 
	for(i : 0 .. ROWS - 1) {
		for (j : 0 .. COLS - 1) {
			AssignCell(c, cells[i].cell[j]);

			// make sure that the charged cells have been reset by a discharge scheduler
			assert(c.conn != char);

			// charge the first idle uncharged cell
			if 
			:: !c.charge && c.conn == idle -> 
				c.conn = char;
				AssignCell(cells[i].cell[j], c);
				#ifdef OUTPUT
				printf("CS: Charging cell %d%d gr %d\n", i, j, c.group);
				#endif

				break;
			:: else skip;
			fi; 
		}

		// early cycle termination
		if 
		:: c.conn == char -> break;
		:: else skip;
		fi;
	}

	// reset local vars for verification
	ResetCell(c);
	i = 0; 
	j = 0;
}

