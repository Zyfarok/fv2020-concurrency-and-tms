module ModelingTM {
    type ProcessId = nat
    type MemoryObject = nat
    type MemoryObjectValue = nat
    type TimeStamp = nat

    class Operation {
        const isWrite: bool
        const memObject: MemoryObject
    }

    class Transaction {
        const ops: seq<Operation>
    }

    // Process state : transaction progress and process memory.
    class ProcessState {
        // currentTx : id of tx being processed. txs.size() means done.
        var currentTx: nat
        // currentOp :
        //      - tx.ops.size() represents tryCommit operation.
        //      - -1 represents abort operation
        //      - values in between represent read and write operations
        var currentOp: nat
        // sub-operations of the operation, see the step function
        var currentSubOp: nat

        // Set of read objects with original observed timestamp.
        var readSet: map<MemoryObject, TimeStamp>
        // Set of read objects with original observed value.
        var writeSet: map<MemoryObject, MemoryObjectValue>

        constructor () {
            currentTx := 0;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := map[];
        }
    }

    class TMSystem {
        const procs: set<ProcessId>
        // Ordered list of transaction that each process should process
        const txQueues : map<ProcessId, seq<Transaction>>
        // State and memory of processes
        const procStates : map<ProcessId, ProcessState>
        // Value of object (not actually necessary for the proofs)
        var objValues: map<MemoryObject, MemoryObjectValue>
        // Object lock.
        var objLocks: map<MemoryObject, bool>
        // Object timestamp. (Incremented at the end of any write transaction)
        var objTimeStamps: map<MemoryObject, nat>

        constructor (q: map<ProcessId, seq<Transaction>>) {
            procs := q.Keys;
            txQueues := q;
            procStates := map p: ProcessId | p in q :: new ProcessState(); // ???
            objValues := map o: MemoryObject | (
                exists p :: p in q && (
                    exists tx :: tx in q[p] && (
                        exists op :: op in tx.ops && op.memObject == o
                    )
                )
            ) :: 0;
            objLocks := map o: MemoryObject | (
                exists p :: p in q && (
                    exists tx :: tx in q[p] && (
                        exists op :: op in tx.ops && op.memObject == o
                    )
                )
            ) :: false;
            objTimeStamps := map o: MemoryObject | (
                exists p :: p in q && (
                    exists tx :: tx in q[p] && (
                        exists op :: op in tx.ops && op.memObject == o
                    )
                )
            ) :: 0;
        }

        method Step(p: ProcessId)
            requires p in procs // Replace with 
            modifies this
        {
            var txs := txQueues[p];
            var state := procStates[p];
            if (state.currentTx >= |txs|) {
                // Nothing left to do.
                return;
            }
            var tx := txs[state.currentTx];
            if (state.currentOp == |tx.ops|) {
                // tryCommit
                if(state.currentSubOp == 0) {
                    // Validate timestamps
                    if !(forall o :: o in state.readSet ==> state.readSet[o] == objTimeStamps[o]) {
                        // Write detected (timestamp changed), aborting.
                        state.currentOp := -1;
                        state.currentSubOp := 0;
                        return;
                    }
                    // Continue to next sub-op.
                    state.currentSubOp := state.currentSubOp + 1;
                } else if (state.currentSubOp == 1) {
                    // Check locks
                    if !(forall o :: o in state.readSet ==> o in state.writeSet || !objLocks[o]) {
                        // Write detected (locked), aborting.
                        state.currentOp := -1;
                        state.currentSubOp := 0;
                        return;
                    }
                    // Can commit ! Continue to next sub-op.
                    state.currentSubOp := state.currentSubOp + 1;
                } else if (state.currentSubOp == 2) {
                    // Update timestamps
                    objTimeStamps := map o | o in objTimeStamps ::
                        if(o in state.writeSet) then (objTimeStamps[o] + 1) else objTimeStamps[o];
                    // Continue to next sub-op.
                    state.currentSubOp := state.currentSubOp + 1;
                } else if (state.currentSubOp == 3) {
                    // Release locks
                    objLocks := map o | o in objLocks ::
                        if(o in state.writeSet) then false else objLocks[o];
                    state.writeSet := map[];
                    state.readSet := map[];
                    // Commited. Continue to next transaction.
                    state.currentTx := state.currentTx + 1;
                    state.currentOp := 0;
                    state.currentSubOp := 0;
                }
            } else if (state.currentOp == -1) {
                // Abort
                if(state.currentSubOp == 0) {
                    // Reset written values
                    objValues := map o | o in objValues ::
                        if(o in state.writeSet) then state.writeSet[o] else objValues[o];
                    // Continue to next sub-op.
                    state.currentSubOp := state.currentSubOp + 1;
                } else if (state.currentSubOp == 1) {
                    // Update timestamps
                    objTimeStamps := map o | o in objTimeStamps ::
                        if(o in state.writeSet) then (objTimeStamps[o] + 1) else objTimeStamps[o];
                    // Continue to next sub-op.
                    state.currentSubOp := state.currentSubOp + 1;
                } else if (state.currentSubOp == 2) {
                    // Release locks
                    objLocks := map o | o in objLocks ::
                        if(o in state.writeSet) then false else objLocks[o];
                    state.writeSet := map[];
                    state.readSet := map[];
                    // Restart transaction.
                    state.currentOp := 0;
                    state.currentSubOp := 0;
                }
            } else {
                var op := tx.ops[state.currentOp];
                var o := op.memObject;
                if(op.isWrite) {
                    // Write
                    if(state.currentSubOp == 0) {
                        if(!(op.memObject in state.writeSet)) {
                            // trylock
                            if(objLocks[o]) {
                                // Failed locking, aborting.
                                state.currentOp := -1;
                                state.currentSubOp := 0;
                                return;
                            } else {
                                // Aquire lock. Continue to next sub-op.
                                objLocks := objLocks[o := true];
                                state.writeSet := state.writeSet[o := objValues[o]];
                            }
                        }
                        state.currentSubOp := state.currentSubOp + 1;
                    } else if (state.currentSubOp == 1) {
                        // Do the write (simple increment). Continue to next op.
                        objValues := objValues[o := (objValues[o] + 1)];
                        state.currentOp := state.currentOp + 1;
                        state.currentSubOp := 0;
                    }
                } else {
                    // Read operation
                    if(state.currentSubOp == 0) {
                        if(o in state.writeSet || o in state.readSet) {
                            // Already in writeSet or readSet, fast-skip to next op.
                            state.currentOp := state.currentOp + 1;
                            state.currentSubOp := 0;
                            return;
                        }
                        // Read timestamp and add to readSet. Continue to next sub-op.
                        state.readSet := state.readSet[o := objTimeStamps[o]];
                        state.currentSubOp := state.currentSubOp + 1;
                    } else if (state.currentSubOp == 1) {
                        if(objLocks[o]) {
                            // Object is locked, aborting.
                            state.currentOp := -1;
                            state.currentSubOp := 0;
                        } else {
                            // All good. Continue to next op.
                            state.currentOp := state.currentOp + 1;
                            state.currentSubOp := 0;
                        }
                    }
                }
            }
        }
    }
}