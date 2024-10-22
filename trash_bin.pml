/*
	Trash bin system template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one trash bin and one user.

	This file contains the environment for the single trash bin system part of the assignment.
	It contains:
	- a specification of the trash bin
	- a specification of a simple server
	- a specification of a user
	- a specification of a trash truck
	- a (dummy) specification of the main controller
	- formulas to check the requested properties
*/

// CONSTANTS
// The number of trash bins.
#define NO_BINS 1
// The number of users.
#define NO_USERS 1

#define SINGLE_USER_ID 0
#define SINGLE_BIN_ID 0

// FORMULAS
// Insert the LTL formulas here
// ram1 The vertical ram is only used when the outer door is closed and locked
#define p1 (bin_status.ram == compress)
#define q1 (bin_status.out_door == closed)
#define r1 (bin_status.lock_out_door == closed)
ltl ram1 { [](p1 -> (q1 && r1))}

// ram2 The vertical ram is not used when the interior of the trash bin is empty.
#define p2 (bin_status.ram == compress)
#define q2 (bin_status.trash_compressed == 0)
ltl ram2 { []!(p2 && q2)}

// door1 The outer door can only be opened if no trash is in it. - SAFETY
#define p3 bin_status.out_door == closed
#define q3 bin_status.trash_in_outer_door > 0
ltl door1 { []((p3 && q3) -> (p3 U !q3)) }

// door2 The outer door can only be locked if the trap door is closed and no
// trash is on the trap door
#define p4 (bin_changed?[LockOuterDoor, true])
#define q4 (bin_status.trap_door == closed)
#define r4 (bin_status.trash_on_trap_door == 0)
ltl door2 { [](p4 -> (q4 && r4))}

// capacity1 Every time the trash bin is full, it is eventually not full anymore.
#define p5 (bin_status.full_capacity == true)
//ltl capacity1 { [](p5 -> <>!p5)}
ltl capacity1 { always (p5 -> eventually (!p5)) }

// user1 The user always eventually has no trash
#define p6 (has_trash == false)
ltl user1 { [](<>p6)}

// user2 Every time the user has trash they can deposit their trash.
#define p7 (has_trash == true)
#define q7 (can_deposit_trash?[SINGLE_USER_ID, true])
ltl user2 { [](p7 -> <>q7)}

// truck1 Every time the truck is requested for a trash bin, the truck has eventually emptied the bin.
ltl truck1 {[](request_truck?[SINGLE_BIN_ID] -> <>(bin_status.trash_compressed==0))}

// DATATYPES
// Type for components
mtype:comp = { OuterDoor, LockOuterDoor, TrapDoor }
// Type for door position.
mtype:pos = { closed, open };
// Type for ram position.
mtype:ram_pos = { idle, compress };
// Type for truck position.
mtype:truck_pos = { arrived, start_emptying, emptied };

// Datatype to store information on the trash bin 
typedef bin_t {
	// Status of doors and ram
	mtype:pos out_door;
	mtype:pos lock_out_door;
	mtype:pos trap_door;
	mtype:ram_pos ram;
	// Location of trash
	byte trash_in_outer_door;
	byte trash_on_trap_door;
	// Current level of trash
	byte trash_compressed;
	byte trash_uncompressed;
	// Exceptional behavior
	bool full_capacity;
	bool trap_destroyed;
	bool busy;
}


// VARIABLES
// Status of trash bin
bin_t bin_status;

// Maximal capacity of trash bin
byte max_capacity;

// User information
bool has_trash;

// Variable to decide if the card reading is enabled
// bool reader_enabled;

// CHANNELS
// Asynchronous channel to give command to doors and lock
chan change_bin = [1] of { mtype:comp, mtype:pos };
// Synchronous channel to acknowledge change in bin
chan bin_changed = [0] of { mtype:comp, bool };
// Synchronous channel to indicate that user closed the door
chan user_closed_outer_door = [0] of { bool };

// Synchronous channels to communicate with weight sensors in trap doors
chan weigh_trash = [0] of { bool };
chan trash_weighted = [0] of { byte };

// Synchronous channel to communicate with ram
chan change_ram = [0] of { mtype:ram_pos };
chan ram_changed = [0] of { bool };

// Asynchronous channel to communicate with the user
chan scan_card_user = [NO_USERS] of { byte };
chan can_deposit_trash = [NO_USERS] of { byte, bool };

// Synchronous channel to communicate with server
chan check_user = [0] of { byte };
chan user_valid = [0] of { byte, bool };

// Asynchronous channel to communicate with trash truck
chan request_truck = [NO_BINS] of { byte };
chan change_truck = [1] of { mtype:truck_pos, byte };
// Synchronous channel for communication between trash truck and trash bin
chan empty_bin = [0] of { bool };
chan bin_emptied = [0] of { bool };


// PROCESSES
// Trash bin process type.
// It models the physical components (doors, ram, sensors).
proctype bin(byte bin_id) {
	do
	// Outer door
	:: change_bin?OuterDoor, closed ->
		if
		:: bin_status.out_door == open ->
			bin_status.out_door = closed;
			user_closed_outer_door!true; // send to main control to begin trash disposal process
			bin_changed!OuterDoor, true;
		fi
	:: change_bin?OuterDoor, open ->
		if
		:: bin_status.out_door == closed && bin_status.lock_out_door == open ->
			bin_status.out_door = open;
			bin_changed!OuterDoor, true;
		fi
	:: change_bin?LockOuterDoor, closed ->
		if
		:: bin_status.lock_out_door == open && bin_status.out_door == closed ->
			atomic {
				bin_status.lock_out_door = closed;
				// Check if trash now falls through
				if
				:: bin_status.trash_in_outer_door > 0 && bin_status.trap_door == closed && bin_status.trash_on_trap_door == 0 ->
					// Trash in outer door falls on trap door
					bin_status.trash_on_trap_door = bin_status.trash_in_outer_door;
					bin_status.trash_in_outer_door = 0;
				:: bin_status.trash_in_outer_door > 0 && bin_status.trap_door == closed && bin_status.trash_on_trap_door > 0 ->
					// Trash in outer door stays, as trap door still contains trash
					skip;
				:: bin_status.trash_in_outer_door > 0 && bin_status.trap_door == open ->
					// Trash in outer door falls through trap door
					assert(bin_status.trash_on_trap_door == 0); // check if trap door is empty, when its open. cannot happen that its contains when it is open.
					bin_status.trash_uncompressed = bin_status.trash_uncompressed + bin_status.trash_in_outer_door;
					bin_status.trash_in_outer_door = 0;
				fi
			}
			bin_changed!LockOuterDoor, true;
		fi
	:: change_bin?LockOuterDoor, open ->
		if
		:: bin_status.lock_out_door == closed && bin_status.out_door == closed ->
			printf(">>>>> IS THIS CALLED?\n")
			bin_status.lock_out_door = open;
			bin_changed!LockOuterDoor, true;
		fi
	// Trap door
	:: weigh_trash?true ->
		if
		:: bin_status.trap_door == closed ->
			trash_weighted!bin_status.trash_on_trap_door;
		fi
	:: change_bin?TrapDoor, closed ->
		if
		:: bin_status.trap_door == open && bin_status.ram == idle ->
			bin_status.trap_door = closed;
			bin_changed!TrapDoor, true;
		:: bin_status.trap_door == open && bin_status.ram == compress ->
			bin_status.trap_destroyed = true;
			bin_changed!TrapDoor, false;
		fi
	:: change_bin?TrapDoor, open ->
		if
		:: bin_status.trap_door == closed ->
			atomic {
				bin_status.trap_door = open;
				// Trash on trap door falls through
				if
				:: bin_status.trash_on_trap_door > 0 ->
					bin_status.trash_uncompressed = bin_status.trash_uncompressed + bin_status.trash_on_trap_door;
					bin_status.trash_on_trap_door = 0;
				:: else ->
					skip;
				fi
			}
			bin_changed!TrapDoor, true;
		fi
	// Vertical ram
	:: change_ram?compress ->
		if
		:: bin_status.ram == idle ->
			atomic {
				bin_status.ram = compress;
				if
				:: bin_status.trap_door == open ->
					// Compress trash
					bin_status.trash_compressed = bin_status.trash_compressed + bin_status.trash_uncompressed / 2;
					bin_status.trash_uncompressed = 0;
				:: bin_status.trap_door == closed ->
					// Trap doors are destroyed
					bin_status.trap_destroyed = true;
				fi
			}
			ram_changed!true;
		fi
	:: change_ram?idle ->
		if
		:: bin_status.ram == compress ->
			bin_status.ram = idle;
			ram_changed!true;
		fi
	// Emptying through trash truck
	:: empty_bin?true ->
		if
		:: bin_status.out_door == closed && bin_status.lock_out_door == closed && bin_status.ram == idle ->
			atomic {
				bin_status.trash_compressed = 0;
				bin_status.trash_uncompressed = 0;

				bin_status.full_capacity = false;
			}
			bin_emptied!true;
		fi
	od
}

// Server process type.
// It models the central backend and administration interface.
proctype server() {
	byte user_id;
	do
	// Check validity of card
	:: check_user?user_id ->
		printf(">>>>>>> SERVER CHECK USER %d\n", user_id);
		if
		// Do not accept cards from user with id 42
		:: user_id != 42 ->
			printf(">>>>>>> VALID USER %d\n", user_id);
			user_valid!user_id, true;
		:: user_id == 42 ->
			printf(">>>>>>> INVALID USER %d\n", user_id);
			user_valid!user_id, false;
		fi
	od
}

// Trash truck process type.
// Remodel it to control the trash truck and handle requests by the controller!
proctype truck() {
	byte bin_id;
	do
	:: request_truck?<bin_id> ->
		assert(bin_status.full_capacity == true);
		printf(">>>> TRUCK RECEIVED THAT A BIN %d SHOULD BE EMPTIED\n", bin_id);
		// announce its arrival with the message arrived via the channel "change_truck"
		change_truck!arrived,true;
		
		change_truck?start_emptying, true;
		printf(">>>> TRUCK RECEIVED IT SHOULD START EMPTING BIN %d\n", bin_id);

		// technically the channel request_truck always contains at least one trash bin
		// since main_control called start_emptying.
		// https://spinroot.com/spin/Man/nempty.html
		assert(nempty(request_truck));

		// removes latest element from the channel and assigns to bin_id
		byte temp_bin_id;
		request_truck?temp_bin_id;

		assert(temp_bin_id == bin_id);

		// empty the trash bin
		// communicates with the trash bin via the channels "empty_bin" and "bin_emptied"
		printf(">>>> START EMPTYING BIN %d CURRENT LEVEL: %d / %d\n", bin_id, bin_status.trash_compressed, max_capacity);
		empty_bin!true;
		bin_emptied?true; // Hold until (Bin is ack as empty)
		printf(">>>> EMPTY BIN %d CURRENT LEVEL: %d / %d\n", bin_id, bin_status.trash_compressed, max_capacity);

		// communicates this with the main controller via the message "emptied"
		printf(">>>> TRUCK IS NOW EMPTIED\n");
		// printf("STOPPPED");
		// assert(false == true);
		change_truck!emptied, true;
	od
}


// User process type.
// The user tries to deposit trash.
proctype user(byte user_id; byte trash_size) {
	do
	// Get another bag of trash
	:: !has_trash ->
		has_trash = true;
	// Try to deposit trash
	:: has_trash ->
		// Scan card
		printf(">>>>> USER %d HAS TRASH SIZE: %d\n", user_id, trash_size);
		printf(">>>>> USER %d SCANS CARD\n", user_id);
		scan_card_user!user_id;
		if
		:: can_deposit_trash?user_id, true ->
			printf(">>>>> USER %d IS ALLOWED TO DEPOSIT TRASH\n", user_id);
			printf(">>>>> BEFORE: WAIT FOR THE BIN TO UNLOCK STATE: %d MUST BE %d\n", bin_status.lock_out_door, open);
			bin_changed?LockOuterDoor, true; // Holds until (Lock is ack as open)
			printf(">>>>> AFTER: WAIT FOR THE BIN TO UNLOCK STATE: %d MUST BE %d\n", bin_status.lock_out_door, open);
			// Open door
			printf(">>>>> BEFORE OPENING OUTER DOOR STATE: %d MUST BE %d\n", bin_status.out_door, open);
			change_bin!OuterDoor, open;
			bin_changed?OuterDoor, true; // Holds until (Outerdoor is ack as open)
			printf(">>>>> AFTER OPENING OUTER DOOR STATE: %d MUST BE %d\n", bin_status.out_door, open);
			atomic {
				if
				:: bin_status.trash_in_outer_door == 0 ->
					printf(">>>>> BEFORE TRASH IN OUTER DOOR IS %d MUST BE %d\n", bin_status.trash_in_outer_door, trash_size);
					// Deposit trash
					bin_status.trash_in_outer_door = trash_size;
					has_trash = false;
					printf(">>>>> AFTER TRASH IN OUTER DOOR IS %d MUST BE %d\n", bin_status.trash_in_outer_door, trash_size);
				:: bin_status.trash_in_outer_door > 0 ->
					printf(">>>>> TRASH IN OUTER DOOR IS NOT EMPTY\n");
					// Cannot deposit trash
					skip;
				fi
			}
			// Close door
			printf(">>>>> BEFORE: bin_status.out_door = %d MUST BE %d\n", bin_status.out_door, closed);
			change_bin!OuterDoor, closed;
			bin_changed?OuterDoor, true; // Hold until (Outerdoor is ack as closed)
			printf(">>>>> AFTER: bin_status.out_door = %d MUST BE %d\n", bin_status.out_door, closed);
		:: can_deposit_trash?user_id, false ->
			printf(">>>>> USER IS NOT ALLOWED TO DEPOSIT TRASH\n");
			skip;
		fi
	od
}


// DUMMY main control process type.
// Remodel it to control the trash bin system and handle requests by users!
proctype main_control() {
	byte bin_id = SINGLE_BIN_ID;
	byte user_id;
	byte trash_weight;

	do
	:: scan_card_user?user_id ->
		// - Check whether the card is valid
		// - Check whether the trash bin is full and no trash can be deposited.
		bool valid = false;
		check_user!user_id;
		user_valid?user_id, valid;
		printf(">>>>>> MAIN CONTROL USER %d IS %d \n", user_id, valid);
		if 
		:: valid == true ->
			if
			:: (!bin_status.full_capacity && !bin_status.trap_destroyed && !bin_status.busy) ->
				printf(">>>>>> MAIN CONTROL SINGLE BIN STATE:\n")
				printf(">>>>>> full_capacity: %d\n", bin_status.full_capacity);
				printf(">>>>>> trap_destroyed: %d\n", bin_status.trap_destroyed);
				printf(">>>>>> busy: %d\n", bin_status.busy);
				bin_status.busy = true;
				printf(">>>>> MAIN CONTROL ALLOW USER %d TO DEPOSIT TRASH\n", user_id);
				can_deposit_trash!user_id, true;
				printf(">>>>> MAIN CONTROL UNLOCK OUTER DOOR: %d MUST BE %d\n", bin_status.lock_out_door, open);
				change_bin!LockOuterDoor, open;
			:: else -> 
				printf(">>>>> MAIN CONTROL DENY USER %d TO DEPOSIT TRASH\n", user_id);
				can_deposit_trash!user_id, false;
			fi
		:: else ->
			printf(">>>>> MAIN CONTROL DENY USER %d TO DEPOSIT TRASH\n", user_id);
			can_deposit_trash!user_id, false;
		fi

	:: user_closed_outer_door?true ->
		printf(">>>> MAIN CONTROL USER HAS CLOSED THE OUTER DOOR\n");
		// steps:
		// the controller should interact with the trash bin such that:
		// 1. the trash is removed from the outer door
		printf(">>>> BEFORE MAIN CONTROL LOCK THE OUTER DOOR STATE: %d MUST BE %d\n", bin_status.lock_out_door, closed);
		change_bin!LockOuterDoor, closed;
		bin_changed?LockOuterDoor, true; // Hold until (Lock is ack as closed)
		printf(">>>> AFTER MAIN CONTROL LOCK THE OUTER DOOR STATE: %d MUST BE %d\n", bin_status.lock_out_door, closed);
	
		// 2. is weighted
		printf(">>>> MAIN CONTROL WEIGH TRASH\n");
		weigh_trash!true;
		trash_weighted?trash_weight; 
		printf(">>>> MAIN CONTROL WEIGHED TRASH EQUALS TO %d\n", trash_weight);

		printf(">>>>> MAIN CONTROL THE BIN IS NOT YET FULL\n");
		// 3. and then falls into the main chamber.
		printf(">>>>> BEFORE MAIN CONTROL OPEN TRAP DOOR STATE: %d MUST BE %d\n", bin_status.trap_door, open);
		change_bin!TrapDoor, open;
		bin_changed?TrapDoor, true; // Hold until (Trapdoor is ack as open)
		printf(">>>>> AFTER MAIN CONTROL OPEN TRAP DOOR STATE: %d MUST BE %d\n", bin_status.trap_door, open);


		printf(">>>>> BEFORE MAIN CONTROL COMPRESS RAM STATE: %d MUST BE %d\n", bin_status.ram, compress);
		change_ram!compress;
		ram_changed?true; // Hold until (Ram is ack as compressing)
		printf(">>>>> AFTER MAIN CONTROL COMRPESS RAM STATE: %d MUST BE %d\n", bin_status.ram, compress);

		if 
		:: bin_status.trash_compressed >= max_capacity -> 
			printf(">>>>> MAIN CONTROL BIN IS FULL %d\n", bin_id);
			bin_status.full_capacity = true;
			printf(">>>>> MAIN CONTROL CALL THE TRUCK ON THE BIN: %d\n", bin_id);
			request_truck!bin_id;
		:: else -> 
			printf(">>>>> MAIN CONTROL AFTER COMPRESS BIN IS NOT REACH MAX CAPACITY %d < %d\n", bin_status.trash_compressed, max_capacity);
			skip;
		fi

		printf(">>>>> BEFORE MAIN CONTROL IDLE RAM STATE: %d MUST BE %d\n", bin_status.ram, idle);
		change_ram!idle;
		ram_changed?true; // Hold until (Ram is ack as idle)
		printf(">>>>> AFTER MAIN CONTROL IDLE RAM STATE: %d MUST BE %d\n", bin_status.ram, idle);

		printf(">>>>> BEFORE MAIN CONTROL CLOSED TRAP DOOR STATE: %d MUST BE %d\n", bin_status.trap_door, closed);
		change_bin!TrapDoor, closed;
		bin_changed?TrapDoor, true; // should be true, as we change the ram to idle beforehand.
		printf(">>>>> AFTER MAIN CONTROL CLOSED TRAP DOOR STATE: %d MUST BE %d\n", bin_status.trap_door, closed);

		//if truck hasn't finished yet wait for it to do so
		if
		::request_truck?[bin_id] ->
			change_truck?arrived, bin_id
			printf(">>>>> MAIN CONTROL TRUCK HAS ARRIVED\n");
			printf(">>>>> MAIN CONTROL TRUCK START TO EMPTYING\n");
			change_truck!start_emptying, bin_id;
			change_truck?emptied, bin_id; // Hold until (Truck is ack as emptied the bin)
			printf(">>>>> MAIN CONTROL TRUCK HAS EMPTIED")
		::else -> skip
		fi

		printf(">>>>> MAIN CONTROL BIN IS NOW NOT BUSY\n");
		bin_status.busy = false;
	:: change_truck?arrived, true ->
		printf(">>>>> MAIN CONTROL TRUCK HAS ARRIVED\n");
		printf(">>>>> MAIN CONTROL TRUCK START TO EMPTYING\n");
		change_truck!start_emptying, true;
		change_truck?emptied, true; // Hold until (Truck is ack as emptied the bin)
		printf(">>>>> MAIN CONTROL TRUCK HAS EMPTIED THE TRASH\n");
		assert(bin_status.full_capacity == false);
		assert(bin_status.trash_compressed == 0);
		assert(bin_status.trash_uncompressed == 0);
	od
}

// Initial process that instantiates all other processes and
// creates the initial trash bin situation.
init {
	byte proc;
	atomic {
		// In the code below, the individual trash bins are initialised.
		// The assumption here is that N == 1.
		// When generalising the model for multiple bin, make sure that the do-statement is altered!	
		proc = 0;
		do
		:: proc < NO_BINS ->
			// Status of trash bin
			bin_status.out_door = closed;
			bin_status.lock_out_door = closed;
			bin_status.trap_door = closed;
			bin_status.ram = idle;
			bin_status.trash_in_outer_door = 0;
			bin_status.trash_on_trap_door = 0;
			bin_status.trash_compressed = 0;
			bin_status.trash_uncompressed = 0;
			bin_status.full_capacity = false;
			bin_status.trap_destroyed = false;
			bin_status.busy=false;
			max_capacity = 2;
			
			run bin(proc);
			proc++;
		:: proc == NO_BINS ->
			break;
		od;

		// Start the user process
		byte trash_size = 2;
		has_trash = true;
		run user(SINGLE_USER_ID, trash_size);

		// Start the server process
		run server();
		// Start the trash truck process
		run truck();

		// Start the control process for the trash bin
		// reader_enabled = true;
		run main_control();
	}
}