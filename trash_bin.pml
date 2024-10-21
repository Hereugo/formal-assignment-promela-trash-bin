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
#define NO_BINS 3
// The number of users.
#define NO_USERS 3

// FORMULAS
// Insert the LTL formulas here
// ltl door1 { ¬(bin_t.out_door == open && bin_t.trash_in_outer_door > 0) }


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

	// Synchronous channel for communication between trash truck and trash bin
	chan empty_bin = [0] of { bool };
	chan bin_emptied = [0] of { bool };
}


// VARIABLES
// Status of trash bin
bin_t bins[NO_BINS];

// Maximal capacity of trash bin
byte max_capacity;

// User Information
typedef user_t {
	byte user_id;
	byte trash_size;
	bool has_trash;
	bool valid;

	
}
user_t users[NO_USERS];

// CHANNELS
// Asynchronous channel to communicate with the user
chan scan_card_user = [NO_USERS] of { byte };
chan can_deposit_trash = [NO_USERS] of { byte, bool };

// Synchronous channel to communicate with server
chan check_user = [0] of { byte };
chan user_valid = [0] of { byte, bool };

// Asynchronous channel to communicate with trash truck
chan request_truck = [NO_BINS] of { byte };
chan change_truck = [1] of { mtype:truck_pos, byte };



// PROCESSES
// Trash bin process type.
// It models the physical components (doors, ram, sensors).
proctype bin(byte bin_id) {
	do
	// Outer door
	:: bins[bin_id].change_bin?OuterDoor, closed ->
		if
		:: bins[bin_id].out_door == open ->
			bins[bin_id].out_door = closed;
			bins[bin_id].user_closed_outer_door!true; // send to main control to begin trash disposal process (line ~304)
			bins[bin_id].bin_changed!OuterDoor, true;
		fi
	:: bins[bin_id].change_bin?OuterDoor, open ->
		if
		:: bins[bin_id].out_door == closed && bins[bin_id].lock_out_door == open ->
			bins[bin_id].out_door = open;
			bins[bin_id].bin_changed!OuterDoor, true;
		fi
	:: bins[bin_id].change_bin?LockOuterDoor, closed ->
		if
		:: bins[bin_id].lock_out_door == open && bins[bin_id].out_door == closed ->
			atomic {
				bins[bin_id].lock_out_door = closed;
				// Check if trash now falls through
				if
				:: bins[bin_id].trash_in_outer_door > 0 && bins[bin_id].trap_door == closed && bins[bin_id].trash_on_trap_door == 0 ->
					// Trash in outer door falls on trap door
					bins[bin_id].trash_on_trap_door = bins[bin_id].trash_in_outer_door;
					bins[bin_id].trash_in_outer_door = 0;
				:: bins[bin_id].trash_in_outer_door > 0 && bins[bin_id].trap_door == closed && bins[bin_id].trash_on_trap_door > 0 ->
					// Trash in outer door stays, as trap door still contains trash
					skip;
				:: bins[bin_id].trash_in_outer_door > 0 && bins[bin_id].trap_door == open ->
					// Trash in outer door falls through trap door
					assert(bins[bin_id].trash_on_trap_door == 0); // check if trap door is empty, when its open. cannot happen that its contains when it is open.
					bins[bin_id].trash_uncompressed = bins[bin_id].trash_uncompressed + bins[bin_id].trash_in_outer_door;
					bins[bin_id].trash_in_outer_door = 0;
				fi
			}
			bins[bin_id].bin_changed!LockOuterDoor, true;
		fi
	:: bins[bin_id].change_bin?LockOuterDoor, open ->
		if
		:: bins[bin_id].lock_out_door == closed && bins[bin_id].out_door == closed ->
			bins[bin_id].lock_out_door = open;
			bins[bin_id].bin_changed!LockOuterDoor, true;
		fi
	// Trap door
	:: bins[bin_id].weigh_trash?true ->
		if
		:: bins[bin_id].trap_door == closed ->
			bins[bin_id].trash_weighted!bins[bin_id].trash_on_trap_door;
		fi
	:: bins[bin_id].change_bin?TrapDoor, closed ->
		if
		:: bins[bin_id].trap_door == open && bins[bin_id].ram == idle ->
			bins[bin_id].trap_door = closed;
			bins[bin_id].bin_changed!TrapDoor, true;
		:: bins[bin_id].trap_door == open && bins[bin_id].ram == compress ->
			bins[bin_id].trap_destroyed = true;
			bins[bin_id].bin_changed!TrapDoor, false;
		fi
	:: bins[bin_id].change_bin?TrapDoor, open ->
		if
		:: bins[bin_id].trap_door == closed ->
			atomic {
				bins[bin_id].trap_door = open;
				// Trash on trap door falls through
				if
				:: bins[bin_id].trash_on_trap_door > 0 ->
					bins[bin_id].trash_uncompressed = bins[bin_id].trash_uncompressed + bins[bin_id].trash_on_trap_door;
					bins[bin_id].trash_on_trap_door = 0;
				:: else ->
					skip;
				fi
			}
			bins[bin_id].bin_changed!TrapDoor, true;
		fi
	// Vertical ram
	:: bins[bin_id].change_ram?compress ->
		if
		:: bins[bin_id].ram == idle ->
			atomic {
				bins[bin_id].ram = compress;
				if
				:: bins[bin_id].trap_door == open ->
					// Compress trash
					bins[bin_id].trash_compressed = bins[bin_id].trash_compressed + bins[bin_id].trash_uncompressed / 2;
					bins[bin_id].trash_uncompressed = 0;
				:: bins[bin_id].trap_door == closed ->
					// Trap doors are destroyed
					bins[bin_id].trap_destroyed = true;
				fi
			}
			bins[bin_id].ram_changed!true;
		fi
	:: bins[bin_id].change_ram?idle ->
		if
		:: bins[bin_id].ram == compress ->
			bins[bin_id].ram = idle;
			bins[bin_id].ram_changed!true;
		fi
	// Emptying through trash truck
	:: bins[bin_id].empty_bin?true ->
		if
		:: bins[bin_id].out_door == closed && bins[bin_id].lock_out_door == closed && bins[bin_id].ram == idle ->
			atomic {
				bins[bin_id].trash_compressed = 0;
				bins[bin_id].trash_uncompressed = 0;

				bins[bin_id].full_capacity = false;
			}
			bins[bin_id].bin_emptied!true;
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
		user_valid!user_id, users[user_id].valid;
	od
}

// Trash truck process type.
// Remodel it to control the trash truck and handle requests by the controller!
// TODO:
// when we are emptying the trash we are unable to determine which bin it is. (Figure out how to find bin_id)
proctype truck() {
	byte bin_id;
	do
	:: request_truck?bin_id ->
		// announce its arrival with the message arrived via the channel "change_truck"
		change_truck!arrived, true
	:: change_truck?start_emptying, true ->
		// empty the trash bin
		// communicates with the trash bin via the channels "empty_bin" and "bin_emptied"
		bins[bin_id].empty_bin!true
		bins[bin_id].bin_emptied?true // Hold until (Bin is ack as empty)
	
		// communicates this with the main controller via the message "emptied"
		change_truck!emptied, true
	od
}


// User process type.
// The user tries to deposit trash.
// TODO:
// - !! This must be implemented after TODO in main_control is complete.
// - determine bin_id that the user is interacting.
proctype user(byte user_id) {
	byte bin_id = 0;
	do
	// Get another bag of trash
	:: !users[user_id].has_trash ->
		users[user_id].has_trash = true;
	// Try to deposit trash
	:: users[user_id].has_trash ->
		// Scan card
		scan_card_user!user_id;
		if
		:: can_deposit_trash?user_id, true ->
			bins[bin_id].bin_changed?LockOuterDoor, true; // Holds until (Lock is ack as open)
			// Open door
			bins[bin_id].change_bin!OuterDoor, open;
			bins[bin_id].bin_changed?OuterDoor, true; // Holds until (Outerdoor is ack as open)
			atomic {
				if
				:: bins[bin_id].trash_in_outer_door == 0 ->
					// Deposit trash
					bins[bin_id].trash_in_outer_door = users[user_id].trash_size;
					users[user_id].has_trash = false;
				:: bins[bin_id].trash_in_outer_door > 0 ->
					// Cannot deposit trash
					skip;
				fi
			}
			// Close door
			bins[bin_id].change_bin!OuterDoor, closed;
			bins[bin_id].bin_changed?OuterDoor, true; // Hold until (Outerdoor is ack as closed)
		:: can_deposit_trash?user_id, false ->
			skip;
		fi
	od
}


// DUMMY main control process type.
// Remodel it to control the trash bin system and handle requests by users!

// TODO:
// Users do not care in which trash bin they deposit their trash. After scanning their card, the main_control can assign an available trash bin to the
// user. To this end, you can extend the messages delivered via the channel
// can_deposit_trash to indicate the bin_id where users should deposit the trash.
proctype main_control() {
	byte bin_id = 0;
	byte user_id;
	byte trash_weight;

	do
	:: scan_card_user?user_id ->
		// - Check whether the card is valid
		// - Check whether the trash bin is full and no trash can be deposited.
		bool valid;
		check_user!user_id;
		user_valid?user_id, valid;
		can_deposit_trash!user_id, (valid && !bins[bin_id].full_capacity);
		if 
		:: bins[bin_id].full_capacity != true ->
			bins[bin_id].change_bin!LockOuterDoor, open; // set outer door to be unlocked (i.e.) diff from opening, its just unlocks it 
		:: else ->
			skip;
		fi
	:: bins[bin_id].user_closed_outer_door?true ->
		// steps:
		// the controller should interact with the trash bin such that:
		// 1. the trash is removed from the outer door
		bins[bin_id].change_bin!LockOuterDoor, closed;
		bins[bin_id].bin_changed?LockOuterDoor, true; // Hold until (Lock is ack as closed)
	
		// 2. is weighted 
		bins[bin_id].weigh_trash!true;
		bins[bin_id].trash_weighted?trash_weight; 
		if
		:: bins[bin_id].full_capacity == true ->
			// TODO: 
			// Should something happen if trash bin is full, and the current trash is in the trap door level?
			// Cannot deposit trash
			skip;
		:: else ->
			// 3. and then falls into the main chamber.
			bins[bin_id].change_bin!TrapDoor, open;
			bins[bin_id].bin_changed?TrapDoor, true; // Hold until (Trapdoor is ack as open)

			bins[bin_id].change_ram!compress;
			bins[bin_id].ram_changed?true; // Hold until (Ram is ack as compressing)

			if 
			:: bins[bin_id].trash_compressed >= max_capacity -> 
				bins[bin_id].full_capacity = true;
			:: else -> 
				skip;
			fi
		fi

		bins[bin_id].change_ram!idle;
		bins[bin_id].ram_changed?true; // Hold until (Ram is ack as idle)

		bins[bin_id].change_bin!TrapDoor, closed;
		bins[bin_id].bin_changed?TrapDoor, true; // should be true, as we change the ram to idle beforehand.
	// truck request emptying of the trash bin if the trash bin is full. 
	:: bins[bin_id].full_capacity ->
		request_truck!bin_id;
		// change_truck?arrived, true; // Hold until (Truck is ack as arrived)

		// While waiting for the trash truck to arrive and empty the bin, users should still be
		// able to scan their card—and then be informed that trash deposit is not possible.
		if
		:: change_truck?arrived, true ->
			change_truck!start_emptying, true;
			change_truck?emptied, true; // Hold until (Truck is ack as emptied the bin)
		:: change_truck?arrived, false -> // user can still scan their card and then be informed that trash deposit is not possible.
			skip;
		fi
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
			bins[proc].out_door = closed;
			bins[proc].lock_out_door = closed;
			bins[proc].trap_door = closed;
			bins[proc].ram = idle;
			bins[proc].trash_in_outer_door = 0;
			bins[proc].trash_on_trap_door = 0;
			bins[proc].trash_compressed = 0;
			bins[proc].trash_uncompressed = 0;
			bins[proc].full_capacity = false;
			bins[proc].trap_destroyed = false;
			max_capacity = 2;
			run bin(proc);
			proc++;
		:: proc == NO_BINS ->
			break;
		od;

		// Start user processes
		proc = 0;
		do
		:: proc < NO_USERS ->			
			users[proc].user_id = proc;
			users[proc].valid = true;
			users[proc].has_trash = true;
			users[proc].trash_size = 2;
			run user(proc);
			proc++;
		:: proc == NO_USERS ->
			break;
		od;

		// Start the server process
		run server();
		// Start the trash truck process
		run truck();

		// Start the control process for the trash bin
		run main_control();
	}
}
