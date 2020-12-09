// import stainless.collection._
// import stainless.lang._
// import stainless.annotation._
// import stainless.equations._

type Process = BigInt
type MemoryObject = BigInt
type TimeStamp = BigInt

sealed abstract class Operation(obj: MemoryObject) {
    def o = obj
}
case class Read(obj: MemoryObject) extends Operation(obj)
case class Write(obj: MemoryObject) extends Operation(obj)

case class Transaction(ops: Seq[Operation])

case class ProcessState(
    currentTx: BigInt,
    currentOp: BigInt,
    currentSubOp: BigInt,
    readSet: Map[MemoryObject, TimeStamp],
    writeSet: Set[MemoryObject]
) {
    def nextSubOp(): ProcessState =
        ProcessState(currentTx, currentOp, currentSubOp + 1, readSet, writeSet)
        
    def nextOp(): ProcessState =
        ProcessState(currentTx, currentOp + 1, 0, readSet, writeSet)
        
    def nextTx(): ProcessState =
        ProcessState(currentTx + 1, 0, 0, Map(), Set())

    def abortTx(): ProcessState =
        ProcessState(currentTx, -1, 0, readSet, writeSet)

    def restartTx(): ProcessState =
        ProcessState(currentTx, 0, 0, Map(), Set())

    def addToReadSet(obj: MemoryObject, ts: TimeStamp): ProcessState =
        ProcessState(currentTx, currentOp, currentSubOp, readSet + (obj -> ts), writeSet)

    def addToWriteSet(obj: MemoryObject): ProcessState =
        ProcessState(currentTx, currentOp, currentSubOp, readSet, writeSet + obj)
}

val startProcess = ProcessState(0, 0, 0, Map(), Set())

case class SystemState(
    txQueues: Map[Process, Seq[Transaction]],
    procStates: Map[Process, ProcessState],
    dirtyObjs: Set[MemoryObject],
    lockedObjs: Set[MemoryObject],
    objTimeStamps: Map[MemoryObject, TimeStamp]
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
            objTimeStamps.map{case (o,ts) =>  if(writeSet.contains(o)) (o, ts + 1) else (o, ts)})
}

def startSystem(txQueues: Map[Process, Seq[Transaction]]): SystemState = {
    var procStates = txQueues.mapValues(_ => startProcess)
    var objs = txQueues.values.flatten.flatten(tx => tx.ops).map(op => op.o).toSet
    var objTimeStamps = objs.map(o => (o, BigInt(0))).toMap
    SystemState(txQueues, procStates, Set(), Set(), objTimeStamps)
}