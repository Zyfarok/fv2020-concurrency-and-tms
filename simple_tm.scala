import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
import java.sql.Time

object TMSystem {
    type Process = BigInt
    type MemoryObject = BigInt
    type TimeStamp = BigInt

    def isValidSet[K](keys: List[K]): Boolean = {
        keys match {
            case k :: ks => !ks.contains(k) && isValidSet(ks)
            case Nil() => true
        }
    }

    case class LMap[K,V](keys: List[K], values: List[V]) {
        require(isValidSet(keys) && keys.length == values.length)

        def +(t: (K,V)): LMap[K,V] = t match {
            case (k,v) => this.+(k,v)
        }

        def +(k: K, v: V): LMap[K,V] =
            if(keys.contains(k))
                LMap(keys, values.updated(keys.indexOf(k), v))
            else
                LMap(Cons(k, keys), Cons(v, values))
        
        def map(f: (K,V) => (K,V)): LMap[K,V] = {
            (keys, values) match {
                case (Cons(k, ks), Cons(v, vs)) => {
                    val x = f(k, v)
                    val xs = LMap(ks,vs).map(f)
                    LMap(Cons(x._1, xs.keys), Cons(x._2, xs.values))
                }
                case (Nil(), Nil()) => this
            }
        }
    }

    object LMap {
        def emptyMap[A,B] = LMap(Nil[A](),Nil[B]())
    }

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
        writeSet: Set[MemoryObject]
    ) {
        def nextSubOp(): ProcessState =
            ProcessState(currentTx, currentOp, currentSubOp + 1, readSet, writeSet)
            
        def nextOp(): ProcessState =
            ProcessState(currentTx, currentOp + 1, 0, readSet, writeSet)
            
        def nextTx(): ProcessState =
            ProcessState(currentTx + 1, 0, 0, LMap.emptyMap[MemoryObject, TimeStamp], Set())

        def abortTx(): ProcessState =
            ProcessState(currentTx, -1, 0, readSet, writeSet)

        def restartTx(): ProcessState =
            ProcessState(currentTx, 0, 0, LMap.emptyMap[MemoryObject, TimeStamp], Set())

        def addToReadSet(obj: MemoryObject, ts: TimeStamp): ProcessState =
            ProcessState(currentTx, currentOp, currentSubOp, readSet + (obj -> ts), writeSet)

        def addToWriteSet(obj: MemoryObject): ProcessState =
            ProcessState(currentTx, currentOp, currentSubOp, readSet, writeSet + obj)
    }

    val startProcess = ProcessState(0, 0, 0, LMap.emptyMap[MemoryObject, TimeStamp], Set())

    case class SystemState(
        txQueues: LMap[Process, List[Transaction]],
        procStates: LMap[Process, ProcessState],
        dirtyObjs: Set[MemoryObject],
        lockedObjs: Set[MemoryObject],
        objTimeStamps: LMap[MemoryObject, TimeStamp]
    ) {
        def updateState(proc: Process, state: ProcessState): SystemState =
            SystemState(txQueues, procStates + (proc -> state), dirtyObjs, lockedObjs, objTimeStamps)
        
        def markDirty(obj: MemoryObject): SystemState =
            SystemState(txQueues, procStates, dirtyObjs + obj, lockedObjs, objTimeStamps)

        def cleanObjects(writeSet: Set[MemoryObject]): SystemState =
            SystemState(txQueues, procStates, dirtyObjs -- writeSet, lockedObjs, objTimeStamps)

        def acquireLock(obj: MemoryObject): SystemState =
            SystemState(txQueues, procStates, dirtyObjs, lockedObjs + obj, objTimeStamps)
        
        def releaseLocks(writeSet: Set[MemoryObject]): SystemState =
            SystemState(txQueues, procStates, dirtyObjs, lockedObjs -- writeSet, objTimeStamps)
        
        def updateTimestamps(writeSet: Set[MemoryObject]): SystemState =
            SystemState(txQueues, procStates, dirtyObjs, lockedObjs,
                    objTimeStamps.map{case (o, ts) => if (writeSet.contains(o)) (o, ts + 1) else (o, ts)})
    }

    def startSystem(txQueues: LMap[Process, List[Transaction]]): SystemState = {
        var procStates = LMap(txQueues.keys, txQueues.values.map(_ => startProcess))
        var objs = txQueues.values.flatMap(x => x).flatMap(tx => tx.ops).map(op => op.o).toSet.toList
        var objTimeStamps = LMap(objs, objs.map(_ => BigInt(0)))
        SystemState(txQueues, procStates, Set(), Set(), objTimeStamps)
    }
}