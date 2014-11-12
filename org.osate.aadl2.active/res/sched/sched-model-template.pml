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

/* A model for resource allocation with global scheduling and abstracted notion of time (only the sequence of scheduling points is modeled)*/
/* This program models scheduling across several processors */
// # of priority levels is assumed to be equal to the # of threads

#define procnum $THREADNUM
#define cpunum $PROCESSORNUM

#include "sched-util.pml"

// thread/task static parameters from aadl
int wcet[procnum];// task worst case execution time
int period[procnum]; // task period
int deadline[procnum]; // task deadline 
int prior[procnum]; // task priority level
int initialArrival[procnum];//  the first arrival time

// timing properties of a job
int jobLastArrival[procnum]; // last absolute time when a job arrived, -1 if never arrived
int jobLastActivation[procnum]; // absolute time when the current job was last dispatched to a processor, -1 if hasn't arrived or been dispatched yet
int jobDeadline[procnum]; // absolute time of the current job's deadline, -1 if hasn't arrived yet
int jobWork[procnum]; // the current job's work done towards completion, -1 if hasn't arrived yet

// execution sequencing
chan queues[procnum] = [procnum] of {byte}; // the priority queue
bool running[procnum]; // tracks which threads are running on processors
bool terminateExecution; // a flag set when a manager detects a termination; disables future arrivals
bool threadTurn[procnum];// true if a thread can take an action valid on the time horizon
bool managerTurn; // a flag that is set when the priority queue is modified. Marks a scheduling point

// scheduler parameters
bool enableEDF;
int lastArrivedJob; // set to the ID of the last arrived job on the arrival scheduling point; otherwise -1

// time horizon 
int clock;
bool det[procnum]; // a manager tells the threads whether their next event is deterministic (i.e. to advance the clock or not)

// TODO how to handle the ordering of events that arrive at the same instant. Right now: considering all orderings

init {
	atomic {
		printf("Initializing\n");
		int i;

$INITIALIZATION
	
		enableEDF = $ISEDF;
		bool fixedPhase = $FIXEDPHASE;

		/*
period[0] = 100;
period[1] = 150;
period[2] = 200;

deadline[0] = 100;
deadline[1] = 90;
deadline[2] = 200;

wcet[0] = 60;
wcet[1] = 15;
wcet[2] = 20;

// if EDF, initialize proportionally to deadlines
prior[0] = 2;
prior[1] = 1;
prior[2] = 0;

enableEDF = true;
bool fixedPhase = true;*/

		// explore initial phasings
		if 
		:: else skip; 
		:: !fixedPhase -> 
			printf("Selected arrival phasing:");
			int arrival;
			for(i: 0 .. procnum - 1) {
				select(arrival: 0 .. period[i] - 1);	
				initialArrival[i] = arrival;
				printf("%d", initialArrival[i]);
			}	
			printf("\n");
		fi;

		// setting initial values for runtime variables
		for(i: 0 .. procnum - 1) {
			running[i] = false;
			jobLastArrival[i] = -1;
			jobLastActivation[i] = -1;
			jobDeadline[i] = -1;
			jobWork[i] = -1;

			threadTurn[i] = false;
			det[i] = false;
		}

		// sequencing setup
		managerTurn = true; // manager goes first
		terminateExecution = false; 
		lastArrivedJob = -1; 
		clock = 0;
	
		run Manager();
		int id; 
		for (id: 0 .. procnum - 1) {
			run Thread(id);
		}

		printf("Initialization successful\n");
	}
}

proctype Thread(byte ID) {
	do

	// arrival of a job. Note: using atomic here because the select statement contains a non-deterministic loop
	// while a model is terminating a thread cannot arrive again	
	:: atomic { threadTurn[ID] && !running[ID] && !managerTurn && !terminateExecution -> 
		printf("Arrival for thread %d, det: %d\n", ID, det[ID]);
		queues[prior[ID]]!ID;

		if 
			:: det[ID] && jobLastArrival[ID] != -1 -> 
				clock = jobLastArrival[ID] + period[ID]; // deterministic advancement for a returning thread
			:: det[ID] && jobLastArrival[ID] == -1 -> 
				clock = initialArrival[ID]; // deterministic advancement for the first arrival
				printf("Advanced clock to %d\n", clock);
			:: !det[ID] -> // arrivals cannot be non-deterministic
				printf("Exception - this shouldn have happened!\n");
				assert(false);
		:: else skip;
			fi;

		// note: there cannot be a case where a non-first arrival is non-deterministic
		jobLastArrival[ID] = clock;
		jobDeadline[ID] = clock + deadline[ID];
		jobWork[ID] = 0;
		// not modifying jobLastActivation because it hasn't been dispatched

		managerTurn = true; 
		lastArrivedJob = ID; // for EDF
		printf("Status: clock: %d, jobLastArrival:%d, jobLastActivation:%d, jobDeadline:%d, jobWork:%d\n", clock, jobLastArrival[ID], jobLastActivation[ID], jobDeadline[ID], jobWork[ID]);
	}

	// termination of a job
	::d_step { threadTurn[ID] && running[ID] && !managerTurn ->
		printf("Terminating job for thread %d, det: %d\n", ID, det[ID]);

		printf("Status pre thread %d: clock: %d, jobLastArrival:%d, jobLastActivation:%d, jobDeadline:%d, jobWork:%d\n", ID, clock, jobLastArrival[ID], jobLastActivation[ID], jobDeadline[ID], jobWork[ID]);

		queues[prior[ID]]??eval(ID); // may not be the first ID in the queue because of several processors
		running[ID] = false; // doesn't need to record its progress after terminating
		if 
			:: det[ID] -> 
				clock = jobLastActivation[ID] + wcet[ID] - jobWork[ID];
			:: else skip;
		fi;

		if
			:: clock > jobDeadline[ID] ->
				printf("DEADLINE MISSED by %d\n", clock-jobDeadline[ID]);
				assert(false);
			:: else skip;
		fi;

		// purging the state
		jobDeadline[ID] = -1;
		jobLastActivation[ID] = -1; 
		jobWork[ID] = -1; // this has to be after the clock update
		// not modifying jobLastArrival because it's not a job's parameter

		managerTurn = true; 
		lastArrivedJob = -1; // for EDF

		printf("Status post thread %d: clock: %d, jobLastArrival:%d, jobLastActivation:%d, jobDeadline:%d, jobWork:%d\n", ID, clock, jobLastArrival[ID], jobLastActivation[ID], jobDeadline[ID], jobWork[ID]);
	}

	od
}

// does all the dirty work
proctype Manager() {
	do
		::d_step { managerTurn -> 
			printf("\n");
		
			// rewind clock variables
			rewindClocks();

			// run the scheduler
			if
			:: enableEDF ->  EDFScheduler();
			:: else skip;
			fi;

			// take threads off processors
			undispatch();

			// redispatch threads on processors 
			dispatchPriority();

			// calculate the scheduling points
			calculateTimeHorizon();

			// activate threads
			managerTurn = false;

			assert(clock < 10000);
		}
	od
}

$LTL

// thread 0 can be pre-empted only when its deadline is not further 
// ltl p0 { [] true }

/*
ltl p1 {
	[](	
		(running[1] && !running[0] && queues[prior[0]]?[0] && !managerTurn-> deadline[1] <= deadline[0]) 
	)
}
ltl p2 {
	[](	
		(running[0] && !running[1] && queues[prior[1]]?[1] && !managerTurn -> deadline[0] <= deadline[1]) 
	)
}ltl p3 {
	[](	
		(running[0] && !running[2] && queues[prior[2]]?[2]  && !managerTurn-> deadline[0] <= deadline[2])
	)
}ltl p4 {
	[](	
		(running[2] && !running[0] && queues[prior[0]]?[0]  && !managerTurn-> deadline[2] <= deadline[0]) 
	)
}ltl p5 {
	[](	
		(running[1] && !running[2] && queues[prior[2]]?[2]  && !managerTurn-> deadline[1] <= deadline[2])
	)
}ltl p6 {
	[](	
		(running[2] && !running[1] && queues[prior[1]]?[1]  && !managerTurn-> deadline[2] <= deadline[1])
	)
}

ltl p100 {
	[](  
	(	
		(running[1] && !running[0] && queues[prior[0]]?[0] && !managerTurn-> deadline[1] <= deadline[0]) 
	)
	 && (	
		(running[0] && !running[1] && queues[prior[1]]?[1] && !managerTurn -> deadline[0] <= deadline[1]) 
	)
	&& (	
		(running[0] && !running[2] && queues[prior[2]]?[2]  && !managerTurn-> deadline[0] <= deadline[2])
	)
	&& (	
		(running[2] && !running[0] && queues[prior[0]]?[0]  && !managerTurn-> deadline[2] <= deadline[0]) 
	)
	&& (	
		(running[1] && !running[2] && queues[prior[2]]?[2]  && !managerTurn-> deadline[1] <= deadline[2])
	)
	&& (	
		(running[2] && !running[1] && queues[prior[1]]?[1]  && !managerTurn-> deadline[2] <= deadline[1])
	)
	)
}*/
