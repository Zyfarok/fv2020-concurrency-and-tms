import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._

object ListProofs {
    @opaque
    def addNoDuplicate[A](ks: List[A], a: A): Unit = {
        require(!ks.contains(a) && ListOps.noDuplicate(ks))
    } ensuring {
        ListOps.noDuplicate(a :: ks)
    }

    @opaque
    def removeNoDuplicate[A](ks: List[A], remove: List[A]): Unit = {
        require(ListOps.noDuplicate(ks))
        decreases(ks.length)
        if(ks.nonEmpty) {
            removeNoDuplicate(ks.tail, remove)
        }
    } ensuring {
        ListOps.noDuplicate(ks -- remove)
    }

    @opaque
    def noDupContains[A](ks: List[A], a: A): Unit = {
        require(ListOps.noDuplicate(ks) && ks.nonEmpty)
    } ensuring {
        ks.head != a || !ks.tail.contains(a)
    }

    @opaque
    def differentIndexes[A](ks: List[A], a: A, b: A): Unit = {
        require(ListOps.noDuplicate(ks) && ks.contains(a) && ks.contains(b))
        decreases(ks.length)
        if(ks.head != a && ks.head != b) {
            differentIndexes(ks.tail, a, b)
        }
    } ensuring {
        (a != b) == (ks.indexOf(a) != ks.indexOf(b))
    }

    @opaque
    def containsMeanValidIndex[A](ks: List[A], a: A): Unit = {
        require(ks.contains(a))
        decreases(ks.length)
        if(ks.head != a)
            containsMeanValidIndex(ks.tail, a)
    } ensuring { ks.indexOf(a) < ks.length }
    
    @opaque
    def updatedListHasSameSize[A](vs: List[A], i: BigInt, a: A): Unit = {
        require(i >= 0 && i < vs.length)
        decreases(vs.length)
        if(i > 0)
            updatedListHasSameSize(vs.tail, i - 1, a)
    } ensuring { vs.updated(i, a).length == vs.length }

    @opaque
    def updateValid[A](xs: List[A], i: BigInt, a: A, j: BigInt): Unit = {
        require(i >= 0 && i < xs.length)
        updatedListHasSameSize(xs, i, a)
        if(i > 0){
            updateValid(xs.tail, i - 1, a, j - 1)
        }
    } ensuring {
        !(j >= 0 && j < xs.length) || (
            xs.updated(i,a)(j) == (if(j == i) a else xs(j))
        )
    }

    @opaque
    def allForall[A](xs: List[A], f: A => Boolean): Unit = {
        if(xs.nonEmpty) {
            allForall(xs.tail, f)
        }
    } ensuring {
        xs.forall(f) == forall((a: A) => !xs.contains(a) || f(a))
    }
}

case class LMap[K,V](keys: List[K], values: List[V]) {
    require(ListOps.noDuplicate(keys)) // keys is a set
    require(keys.length == values.length) // each key has a value

    def +(t: (K,V)): LMap[K,V] = t match {
        case (k,v) => this.+(k,v)
    }

    def +(k: K, v: V): LMap[K,V] = {
        decreases(length)
        if(contains(k)) {
            updated(k,v)
        } else {
            LMap(k :: keys, v :: values)
        }
    } ensuring {
        res => forall((x: K) => res.contains(x) == (x == k) || this.contains(x))
    }

    def updated(k: K, v: V): LMap[K,V] = {
        require(contains(k))
        decreases(length)
        val i = keys.indexOf(k)
        ListProofs.containsMeanValidIndex(keys, k)
        ListProofs.updatedListHasSameSize(values, i, v)
        if(keys.head != k) {
            assert(LMap(keys, values.updated(i, v)).tail == tail.updated(k,v))
        }
        ListProofs.updateValid(this.values, i, v, i)
        LMap(keys, values.updated(i, v))
    } ensuring {
        res => forall((x: K) => res.contains(x) == this.contains(x))
    }
    
    def apply(k: K): V = {
        require(contains(k))
        if(keys.head == k)
            values.head
        else
            tail(k)
    }

    def contains(k: K): Boolean = keys.contains(k)

    def contains(k: K, v: V): Boolean = contains(k) && this(k) == v

    def length = keys.length

    def isEmpty = keys.isEmpty

    def nonEmpty = keys.nonEmpty

    def tail: LMap[K,V] = {
        require(keys.nonEmpty)
        LMap(keys.tail, values.tail)
    }
    
    def mapValues(f: (K,V) => V): LMap[K,V] = {
        (keys, values) match {
            case (k :: ks, v :: vs) => {
                val nv = f(k, v)
                val xs = LMap(ks,vs).mapValues(f)
                LMap(keys, nv :: xs.values)
            }
            case (Nil(), Nil()) => this
        }
    } ensuring {
        res => res.keys == this.keys && res.values.length == this.values.length
    }
}

object LMap {
    def empty[A,B] = LMap(Nil[A](),Nil[B]())
}

object TMSystem {
    type Process = BigInt
    type MemoryObject = BigInt
    type TimeStamp = BigInt

    sealed abstract class Operation {
        def o: MemoryObject
    }
    case class Read(obj: MemoryObject) extends Operation {
        def o = obj
    }
    case class Write(obj: MemoryObject) extends Operation {
        def o = obj
    }

    case class Transaction(ops: List[Operation])

    case class ProcessState(
        currentTx: BigInt,
        currentOp: BigInt,
        currentSubOp: BigInt,
        readSet: LMap[MemoryObject, TimeStamp],
        writeSet: List[MemoryObject]
    ) {
        require(currentTx >= 0) // transaction queue starts with 0
        require(currentOp >= -1) // -1 means abort, other op codes are > 0
        require(currentSubOp >= 0 && currentSubOp < 4) // All ops have at most 4 subops
        require(ListOps.noDuplicate(writeSet)) // writeSet is a set

        def nextSubOp(): ProcessState = {
            require(currentSubOp < 3)
            ProcessState(currentTx, currentOp, currentSubOp + 1, readSet, writeSet)
        }
            
        def nextOp(): ProcessState = {
            ProcessState(currentTx, currentOp + 1, 0, readSet, writeSet)
        }
            
        def nextTx(): ProcessState = {
            ProcessState(currentTx + 1, 0, 0, LMap.empty[MemoryObject, TimeStamp], Nil())
        }

        def abortTx(): ProcessState = {
            ProcessState(currentTx, -1, 0, readSet, writeSet)
        }

        def restartTx(): ProcessState = {
            ProcessState(currentTx, 0, 0, LMap.empty[MemoryObject, TimeStamp], Nil())
        }

        def addToReadSet(obj: MemoryObject, ts: TimeStamp): ProcessState = {
            ProcessState(currentTx, currentOp, currentSubOp, readSet + (obj -> ts), writeSet)
        }

        def addToWriteSet(obj: MemoryObject): ProcessState = {
            require(!writeSet.contains(obj))
            ProcessState(currentTx, currentOp, currentSubOp, readSet, obj :: writeSet)
        }
    }

    val startProcess = ProcessState(0, 0, 0, LMap.empty[MemoryObject, TimeStamp], Nil())

    def validState(state: ProcessState, txs: List[Transaction], dirtyObjs: List[MemoryObject], lockedObjs: List[MemoryObject], objTimeStamps: LMap[MemoryObject, TimeStamp]) : Boolean = {
        true
    }

    case class SystemState(
        txQueues: LMap[Process, List[Transaction]],
        procStates: LMap[Process, ProcessState],
        dirtyObjs: List[MemoryObject],
        lockedObjs: List[MemoryObject],
        objTimeStamps: LMap[MemoryObject, TimeStamp]
    ) {
        require(ListOps.noDuplicate(dirtyObjs))
        require(ListOps.noDuplicate(lockedObjs))
        require(txQueues.keys == procStates.keys)
        require(procStates.keys.forall((p: Process) => {
            txQueues.contains(p) && validState(procStates(p), txQueues(p), dirtyObjs, lockedObjs, objTimeStamps)
        }))

        def updateState(proc: Process, state: ProcessState): SystemState = {
            require(txQueues.contains(proc) && validState(state, txQueues(proc), dirtyObjs, lockedObjs, objTimeStamps))
            val nProcStates = procStates + (proc -> state)

            assert(nProcStates(proc) == state)
            assert(nProcStates.keys.forall((p: Process) => {
                txQueues.contains(p) && validState(nProcStates(p), txQueues(p), dirtyObjs, lockedObjs, objTimeStamps)
            }))
            SystemState(txQueues, nProcStates, dirtyObjs, lockedObjs, objTimeStamps)
        }
        
        def markDirty(obj: MemoryObject): SystemState = {
            require(objTimeStamps.contains(obj) && !dirtyObjs.contains(obj))

            assert(procStates.keys.forall((p: Process) => {
                txQueues.contains(p) && validState(procStates(p), txQueues(p), obj :: dirtyObjs, lockedObjs, objTimeStamps)
            }))
            SystemState(txQueues, procStates, obj :: dirtyObjs, lockedObjs, objTimeStamps)
        }

        def cleanObjects(writeSet: List[MemoryObject]): SystemState = {
            require(
                writeSet.content.subsetOf(objTimeStamps.keys.content) &&
                writeSet.content.subsetOf(dirtyObjs.content)
            )
            val nDirtyObjs = dirtyObjs -- writeSet
            ListProofs.removeNoDuplicate(dirtyObjs, writeSet)

            assert(ListOps.noDuplicate(nDirtyObjs))
            assert(ListOps.noDuplicate(lockedObjs))
            assert(txQueues.keys == procStates.keys)

            assert(procStates.keys.forall((p: Process) => {
                txQueues.contains(p) && validState(procStates(p), txQueues(p), nDirtyObjs, lockedObjs, objTimeStamps)
            }))
            SystemState(txQueues, procStates, nDirtyObjs, lockedObjs, objTimeStamps)
        }

        def acquireLock(obj: MemoryObject): SystemState = {
            require(objTimeStamps.contains(obj) && !lockedObjs.contains(obj))
            ListProofs.addNoDuplicate(lockedObjs, obj)

            assert(procStates.keys.forall((p: Process) => {
                txQueues.contains(p) && validState(procStates(p), txQueues(p), dirtyObjs, obj :: lockedObjs, objTimeStamps)
            }))
            SystemState(txQueues, procStates, dirtyObjs, obj :: lockedObjs, objTimeStamps)
        }
        
        def releaseLocks(writeSet: List[MemoryObject]): SystemState = {
            require(
                writeSet.content.subsetOf(objTimeStamps.keys.content) &&
                writeSet.content.subsetOf(lockedObjs.content)
            )
            val nLockedObjs = lockedObjs -- writeSet
            ListProofs.removeNoDuplicate(lockedObjs, writeSet)

            assert(ListOps.noDuplicate(dirtyObjs))
            assert(ListOps.noDuplicate(nLockedObjs))
            assert(txQueues.keys == procStates.keys)

            assert(procStates.keys.forall((p: Process) => {
                txQueues.contains(p) && validState(procStates(p), txQueues(p), dirtyObjs, nLockedObjs, objTimeStamps)
            }))
            SystemState(txQueues, procStates, dirtyObjs, nLockedObjs, objTimeStamps)
        }
        
        def updateTimestamps(writeSet: List[MemoryObject]): SystemState = {
            require(
                writeSet.content.subsetOf(objTimeStamps.keys.content)
            )
            val nObjTimeStamps = tsUpdate(objTimeStamps, writeSet)

            assert(procStates.keys.forall((p: Process) => {
                txQueues.contains(p) && validState(procStates(p), txQueues(p), dirtyObjs, lockedObjs, nObjTimeStamps)
            }))
            SystemState(txQueues, procStates, dirtyObjs, lockedObjs, nObjTimeStamps)
        }

        def stateValid(proc: Process, state: ProcessState) : Boolean = {
            require(
                (procStates.keys contains proc) && (state == procStates(proc))
            )
            var pid_in_tx = txQueues contains proc
            var state_curr_lt_tx = state.currentTx <= txQueues(proc).size
            var state_status = false
            if (state.currentTx == txQueues(proc).size) {
                // Queue finished
                state_status = state.currentOp == 0 &&
                        state.currentSubOp == 0 &&
                        state.readSet.keys.size == 0 &&
                        state.writeSet.size == 0
            } else if (state.currentTx < txQueues(proc).size) {
                var ops = false
                // Queue unfinished
                var tx = txQueues(proc)(state.currentTx)
                state_status = (state.currentOp <= tx.ops.size) &&
                        state.currentOp >= -1
                    if (state.currentOp >= 0 && state.currentOp < tx.ops.size) (
                        // Read/Write operations have at most two subOps
                        ops = state.currentSubOp < 2
                    ) else if (state.currentOp == tx.ops.size) (
                        // tryCommit has 4 subOps
                        ops = state.currentSubOp < 4
                    ) else if (state.currentOp == -1) (
                        // abort has 3 subOps
                        ops = state.currentSubOp < 3
                    ) else ops = false

                state_status = ops && 
                        state.readSet.keys.size <= objTimeStamps.keys.size &&
                        state.writeSet.size <= dirtyObjs.size
            } else state_status = false

            pid_in_tx && state_curr_lt_tx && state_status
        }

        def validSystem(): Boolean = {
            var kys = procStates.keys
            var stVal = true
            var i : BigInt = kys.size
            var j = true
            while (i >= 0) {
                decreases(kys)
                if (j) j = false
                var ky = kys(i)
                stVal = stVal && stateValid(ky, procStates(ky))
                i = i - 1
            }

            (procStates.keys.size <= txQueues.keys.size) &&
            (dirtyObjs.size <= objTimeStamps.keys.size) &&
            (lockedObjs.size <= objTimeStamps.keys.size) &&
            stVal
        }
    }

    def tsUpdate(objTimeStamps: LMap[MemoryObject, TimeStamp], writeSet: List[MemoryObject]) = {
        objTimeStamps.mapValues{case (o, ts) => if(writeSet.contains(o)) ts + 1 else ts}
    }

    def startSystem(txQueues: LMap[Process, List[Transaction]]): SystemState = {
        var procStates = LMap(txQueues.keys, txQueues.values.map(_ => startProcess))
        var objs = txQueues.values.flatMap(txs => txs).flatMap(tx => tx.ops).map(op => op.o).toSet.toList
        assert(ListOps.noDuplicate(objs))
        var objTimeStamps = LMap(objs, objs.map(_ => BigInt(0)))
        assert(procStates.keys.forall((p: Process) => {
            txQueues.contains(p) && validState(procStates(p), txQueues(p), Nil(), Nil(), objTimeStamps)
        }))
        SystemState(txQueues, procStates, Nil(), Nil(), objTimeStamps)
    }
}