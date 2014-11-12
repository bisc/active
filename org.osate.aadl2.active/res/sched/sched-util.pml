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

// An EDF example of a runtime scheduler.
// ASSUMPTION: starting priorities are according to deadlines
inline EDFScheduler() { 
	// only works on job arrivals
	if
        :: else skip;
        :: lastArrivedJob != -1 ->

		int pri, it = 0, idsortcounter = 0, id;
		bool allocated = false;
		byte idsortdead[procnum]; 

		//printf("Priority array: ");
		// copy everything to array, preserving order and inserting a new guy 
		// note: the lastArrivedJob is already in the queue, so ignore him when I get to him
		it = 0; // idsortdead iterator
		for (pri: 0 .. procnum - 1) { 
			// going from lowest priority to highest
			// j is the array counter
			do
			:: else break;
			:: len(queues[pri]) > 0 -> 
				queues[pri]?id; 
		//		printf("checking:%d",id);
				if 
				:: id == lastArrivedJob -> skip; // ignore it for a moment
				:: id != lastArrivedJob -> 
					if
					:: allocated -> // insert-and-forget
						idsortdead[it] = id; 
						it++;
		//				printf("added:%d",id);
					:: !allocated -> // check how they relate
						if
						:: jobDeadline[id] <= jobDeadline[lastArrivedJob] -> // time to insert this one and the id
							idsortdead[it] = lastArrivedJob;
							idsortdead[it+1] = id; 
							it = it + 2;
							allocated = true;
		//					printf("added:%d %d ", lastArrivedJob, id);
						:: else // insert just id
							idsortdead[it] = id; 
							it++;
		//					printf("added:%d",id);
						fi;
					fi;	
				fi;
							od; 
		} 

		if 
		:: else skip; 
		:: !allocated -> // if the last arrived process was the closest deadline or the last one in the queues, 
				// then it won't get added in the cycle above; have to add manually.
			idsortdead[it] = lastArrivedJob;
			it++;
			//printf("added:%d",lastArrivedJob);
		fi;


		int threadCount = it; //remember the number of active threads 
		//printf("\n");
	
		// allocate threads from an array to the queue
		// iterate over active threads in the idsortdead
		// note: has to go starting from highest priority to respect fifo during queue insertions
		int lastDead = -1;//jobDeadline[idsortdead[threadCount-1]]; // deadline of the rightmost ID
		pri = procnum; // the counter for priority level, starting with the highest; is one more for the first cycle to decrement
		for (it: 0 .. threadCount - 1 ) { 
			id = idsortdead[threadCount -1 - it]; // thread ID under consideration, from the right end
			if 
			:: jobDeadline[id] > lastDead -> 
				pri--;
				lastDead = jobDeadline[id];
				queues[pri]!id; 
				prior[id] = pri;
				printf("EDF: Thread %d assigned priority %d\n", id, pri);
			:: jobDeadline[id] == lastDead -> 
				queues[pri]!id; 
				prior[id] = pri;
				printf("EDF: Thread %d assigned priority %d\n", id, pri);
			:: jobDeadline[id] < lastDead -> 
				printf("Exception - this shouldn't have happened - the array is sorted by deadline!\n");
				assert(false);
			fi;	
		} 
	fi;
}

// a priority updispatcher: takes jobs off processors and updates their progress
inline undispatch(){ 
	byte k;
	// zero out the currently running ones
	for (k: 0 .. procnum - 1) { 
		if 
			:: running[k] -> 
				// in case of non-determ sched points, the last two numbers zero each other out because there is no clock advancement
				jobWork[k] = jobWork[k] + clock - jobLastActivation[k];
		running[k] = false;
		:: else skip;
		fi;
	} 
}


inline rewindClocks(){ 
	// applicability: only do after all threads have arrived at least once
	// otherwise would have to deal with first arrival variable, and I don't want to yet.
	bool arrivedOnce = true;
	byte i; 
	
	for (i: 0 .. procnum - 1) {
		if 
		:: else skip;
		:: jobLastArrival[i] == -1 ->
			arrivedOnce = false; 
		fi;
	}
	
	if 
	:: else printf("Not all threads arrived, no rewind\n"); 
	:: arrivedOnce ->  
		// find the smallest value of all clock variables
		int earliestClock = clock;
		for (i: 0 .. procnum - 1) {
			if 
			:: else skip;
			:: jobLastArrival[i] < earliestClock -> earliestClock = jobLastArrival[i];// printf("Earliest clock %d: arrival of %d\n", earliestClock, i);
			fi;

			if 
			:: else skip;
			:: (jobDeadline[i] != -1) && (jobDeadline[i] < earliestClock) -> earliestClock = jobDeadline[i]; //printf("Earliest clock %d: job deadline of %d\n", earliestClock, i);
			fi;

			if 
			:: else skip;
			:: (jobLastActivation[i] != -1) && (jobLastActivation[i] < earliestClock) -> earliestClock = jobLastActivation[i];// printf("Earliest clock %d: last job activation of %d\n", earliestClock, i);
			fi;
		}
		
		// subtract from all available clocks
		if 
		:: else printf("Exception -- this shouldn't have happened"); assert(false);
		:: earliestClock == 0 -> printf("Earliest clock %d, no rewind\n", earliestClock);
		:: earliestClock > 0 -> 
			printf("Rewinding clock by %d\n", earliestClock);
			clock = clock - earliestClock;

			for (i: 0 .. procnum - 1) {
				jobLastArrival[i] = jobLastArrival[i] - earliestClock;

				if 
				:: else skip;// may have not arrived yet
				:: jobDeadline[i] != -1 -> jobDeadline[i] = jobDeadline[i] - earliestClock;
				fi;

				if 
				:: else skip;// may have not arrived or been dispatched yet
				:: jobLastActivation[i] != -1 -> jobLastActivation[i] = jobLastActivation[i] - earliestClock;
				fi;
			}
		fi;
	fi;
}

// a priority dispatcher: dispatches processes based on the priority queue
inline dispatchPriority() {
	byte k, level, processorcount = cpunum, length, id, l;

	for (k: 0 ..  procnum - 1 ) { // iteration on priorty levels
		// starting with the top level and going down
		level = procnum - 1 - k;
		copyChannel(queues[level], workqueue); 
		if
			:: empty(workqueue) -> skip; 	
		:: nempty(workqueue) ->
			length = len(workqueue);// number of processes at the current level 
		for (l: 1 .. length) { // this cycle is not to be broken: otherwise it's impossible to restore the channel's state
			workqueue?id;
			queues[level]!id;// save the value to the original queue, thus restoring it
			if
				:: processorcount > 0 ->
					running[id] = true;
			processorcount--; 
			jobLastActivation[id] = clock;
			:: else skip;
			fi;	
		}
		if
			:: processorcount == 0 -> break;
		:: else skip;
		fi;	
		fi;
	}

	printf("Dispatched: ");
	for (k: 0 .. procnum -1 ) { 
		printf("%d ", running[k]);
	}
	printf("\n");
}

// figures out the scheduling points and enables threads to arrive or end jobs
inline calculateTimeHorizon(){
	int i, j; // reusable counters	
	// track terminations and arrivals
	bool possibleTerm[procnum], earliestTerm[procnum], earliestArrival[procnum];// these arrays carry data from the first part of the function to the second one.
	bool hasArrival = false, hasTerm = false; // simplifying flags between two parts of the functions
	int earliestTermTime = -1, earliestArrivalTime = -1; // only used in the first part. earliestArrivalTime is among all threads that are earlier than all worst-case nondet events
	int earliestNextArrivalTime = -1; // the earliest next arrival among all running and not running threads

	//initialize arrays
	for(i: 0 .. procnum - 1) { 
		possibleTerm[i] = false;
		earliestTerm[i] = false;
		earliestArrival[i] = false;
		threadTurn[i] = false;
		det[i] = false;
	}


	// calculate the time horizon step 1: determine which scheduling points are possible, and which are the earliest
	for(i: 0 .. procnum - 1) { // iterate through all processes
		if 
		:: running[i] -> // currently running - termination possible
			possibleTerm[i] = true;
			int expectedTerm = jobLastActivation[i] + wcet[i] - jobWork[i];
			printf("Thread %d is running, its worst case time of finishing %d", i, expectedTerm);
			// see if this is the earliest
			if 
			:: !hasTerm || (hasTerm && (expectedTerm < earliestTermTime)) -> 
				printf("is the earliest of worst case nondet times so far\n");	
				hasTerm = true;
				earliestTermTime = expectedTerm;
				// erase the record of existing earliest non-det events
				for (j: 0 .. i - 1) {
					earliestTerm[j] = false;
				}
				earliestTerm[i] = true;	
			:: hasTerm && (expectedTerm  == earliestTermTime) -> 
				// record several coincinding non-det events
				printf("coincides with earliest of worst case nondet times so far\n");	
				earliestTerm[i] = true;	
			:: else printf("\n"); skip;
			fi;

			// find earliest next arrival time: running threads
			if 
			:: (earliestNextArrivalTime == -1) || (jobLastArrival[i] + period[i] < earliestNextArrivalTime) ->
				earliestNextArrivalTime = jobLastArrival[i] + period[i];
			:: else skip;
			fi;
		
		:: !queues[prior[i]]??[eval(i)] -> // a thread is not in the queue - it may arrive
			printf("Thread %d has not arrived yet", i);
			// is it possible for this job to arrive, given the running tasks, before all of their terminations?
			bool arrivesBeforeAllTerm = true;
			int expectedArrival;  
	
			if 
			:: jobLastArrival[i] == -1 -> expectedArrival = initialArrival[i]; // first time arrival
			:: jobLastArrival[i] != -1 -> expectedArrival = jobLastArrival[i] + period[i]; // non-first time arrival
			fi;
			// comparing the candidate arrival thread to all other threads, finishing and first arriving
			for(j: 0 .. procnum - 1 ){ 
				if 
					:: running[j] && expectedArrival > jobLastActivation[j] + wcet[j] - jobWork[j] ->
						arrivesBeforeAllTerm = false; 
					break;
				:: else skip;
				fi;
			};
			if 
			:: else printf(", its arrival %d is NOT before some worst-case nondet times\n", expectedArrival); skip;
			:: arrivesBeforeAllTerm -> 
				printf(", its arrival %d is before all worst-case nondet times", expectedArrival);
				if
					:: !hasArrival || hasArrival && (expectedArrival < earliestArrivalTime) ->
						hasArrival = true;
						printf(", its arrival is the earliest of all arrivals\n");
						earliestArrivalTime = expectedArrival;
						for (j: 0 .. i - 1) {
							earliestArrival[j] = false;
						}
						earliestArrival[i] = true;
					:: hasArrival && (expectedArrival == earliestArrivalTime) -> 
						printf(", its arrival coincides with the earliest of all arrivals\n");
						earliestArrival[i] = true;
					:: else printf("\n"); skip;
				fi;
			fi;
			
			// find earliest next arrival time: arriving threads
			if 
			:: (earliestNextArrivalTime == -1) || (expectedArrival < earliestNextArrivalTime) ->
				earliestNextArrivalTime = expectedArrival;
			:: else skip;
			fi;

		:: else// a thread that is ready in the queues: neither running, nor about to arrive 
			printf("Thread %d is ready\n", i);
		fi;
	}

	printf("Earliest term %d, earliest arrival before all nondet %d, earliest next arrival of all but ready threads %d\n", earliestTermTime,earliestArrivalTime, earliestNextArrivalTime);  
	
	// step 2: decide which thread(s) could take action now 
	// major options for threads: 
	if 
	// doesn't have arrivals earlier than worst-case termination times
	:: !hasArrival && hasTerm -> // then schedule the one with the earliest worst completion time
		printf("Has no arrivals, but some terminations\n");
		
		for (i: 0 .. procnum - 1) { 
			// all terminations can happen, and the earliest is deterministic
			if 
			:: possibleTerm[i] ->
				threadTurn[i] = true;
				// only the earliest worst-case non-deteterministic event is deterministic
				det[i] = earliestTerm[i]; 
			:: else skip;
			fi;
		}

	// has arrivals, but no terminations
	:: hasArrival && !hasTerm ->
		printf("Has arrivals, but no terminations\n");
		// then pick the earliest arrivals, make them all deterministic
		for(i: 0 .. procnum - 1) { 
			threadTurn[i] = earliestArrival[i];
			det[i] = earliestArrival[i];
		}

	// has at least one arrival and one termination/first arrival
	:: hasArrival && hasTerm ->
		printf("Has at least one arrival and one termination\n");
		// make all non-deterministic possible non-deterministically and the earliest arrival -- deterministically
		for (i: 0 .. procnum - 1) { 
			if 
			:: possibleTerm[i] ->
				threadTurn[i] = true; 
				det[i] = false;
			:: earliestArrival[i] -> 
				threadTurn[i] = true;
				det[i] = true;
			:: else skip;
			fi;
		}

	:: else  // no arrivals and no jobs to complete
		printf("Exception - this shouldn't have happened \n");
		assert(false);
	fi;

	// step 3: evaluate the termination condition
	byte numberOfActive = 0; // threads currently on processors
	byte numberInQueues = 0; // threads currently in queue (including those on processors)
	byte numberHadArrivals = 0; // threads that arrived at least once
	bool allTerminateBeforeArrival = true; // whether threads terminate 
	for (i: 0 .. procnum - 1) { 
		// TERMINATION: gathering info
		// need to investigate only the threads that are running now and compare to their arrivals -- other arrivals have already been handled by earliestNextArrivalTime
		if 
		::  possibleTerm[i] && running[i] ->
			numberOfActive++;
			assert(earliestNextArrivalTime != -1);
			// if a thread potentially finishes later than it arrives, then the termination condition is broken
			if 
			:: jobLastActivation[i] + wcet[i] - jobWork[i] > earliestNextArrivalTime ->
				allTerminateBeforeArrival = false;
			:: else skip;
			fi;
		:: else skip;
		fi;
		
		// make sure that threads had a chance to arrive
		if
		:: jobLastArrival[i] != -1 -> 
			numberHadArrivals++;
		:: else skip; 
		fi;

		// count the number in queues
		if
		:: queues[prior[i]]??[eval(i)] -> 
			numberInQueues++;
		:: else skip;	
		fi;
	}

	// TERMINATION: condition check
	// only applicable to the uniprocessor case
	// check for the termination condition: no arrivals before terminations AND threads running = threads in queues AND all running threads have a potential to terminate no later than the earliest next arrival of all running threads; OR no threads are running at all. All that pending that they had a chance to arrive.
	//THEN: deactivate new arrivals

	/*
	if 
	:: cpunum == 1 && numberOfActive !=0 && numberOfActive == numberInQueues && numberHadArrivals == procnum && allTerminateBeforeArrival ->
		printf("TERMINATING MODEL EXECUTION: termination condition met\n");	
		terminateExecution = true; 
	:: cpunum == 1 && numberOfActive == 0 && numberInQueues == 0 && numberHadArrivals == procnum-> 
		printf("TERMINATING MODEL EXECUTION: idle time\n");	
		terminateExecution = true;
	:: else skip;
	fi;
	*/

}

// HELPER FUNCTION
// moves the busy queues from FROM to TO, so that FROM is empty. 
// assumes the to is empty when called
// adjusts process priorities along the way. 
inline shiftQueue(from, to) {
	byte difference;
	int increment; 

	if 
	:: from >= to -> difference = from - to; increment = 1;
	:: else difference = to - from; increment = -1;
	fi; 

	int channel = to;
	for (i: 0..difference) { 
		copyChannel(channel + increment, channel);
		channel = channel + increment;	
	}
}

// HELPER CHANNEL
chan workqueue = [procnum] of {byte};// a temporary buffer to inspect queues

// HELPER FUNCTION
// copies the first channel into the second. a helper function for restoring channel's state.
inline copyChannel(ch1, ch2) { 
	byte chCount, chBuf, chSize;
	// clear the second 
	chSize = len(ch2);
	for (chCount: 1 .. chSize) { 
		ch2?chBuf;
	} 

	// copy the first into the second
	chSize = len(ch1);
	for(chCount: 1 .. chSize) { 
		ch1?chBuf; 	
		ch2!chBuf;
	}
}

