// import stainless.collection._
// import stainless.lang._
// import stainless.annotation._
// import stainless.equations._

type Process = BigInt
type MemoryObject = BigInt
type MemoryObjectValue = BigInt
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
    writeSet: Map[MemoryObject, MemoryObjectValue]
) {
    def nextSubOp(): ProcessState =
        ProcessState(currentTx, currentOp, currentSubOp + 1, readSet, writeSet)
        
    def nextOp(): ProcessState =
        ProcessState(currentTx, currentOp + 1, 0, readSet, writeSet)
        
    def nextTx(): ProcessState =
        ProcessState(currentTx + 1, 0, 0, Map(), Map())

    def abortTx(): ProcessState =
        ProcessState(currentTx, -1, 0, readSet, writeSet)

    def restartTx(): ProcessState =
        ProcessState(currentTx, 0, 0, Map(), Map())

    def addToReadSet(obj: MemoryObject, ts: TimeStamp): ProcessState =
        ProcessState(currentTx, currentOp, currentSubOp, readSet + (obj -> ts), writeSet)

    def addToWriteSet(obj: MemoryObject, v: MemoryObjectValue): ProcessState =
        ProcessState(currentTx, currentOp, currentSubOp, readSet, writeSet + (obj -> v))
}

val startProcess = ProcessState(0, 0, 0, Map(), Map())

case class SystemState(
    txQueues: Map[Process, Seq[Transaction]],
    procStates: Map[Process, ProcessState],
    objValues: Map[MemoryObject, MemoryObjectValue],
    lockedObjs: Set[MemoryObject],
    objTimeStamps: Map[MemoryObject, TimeStamp]
) {
    def updateState(p: Process, s: ProcessState): SystemState =
        SystemState(txQueues, procStates + (p -> s), objValues, lockedObjs, objTimeStamps)
    
    def updateValue(o: MemoryObject, v: MemoryObjectValue): SystemState =
        SystemState(txQueues, procStates, objValues + (o -> v), lockedObjs, objTimeStamps)

    def restoreValues(writeSet: Map[MemoryObject, MemoryObjectValue]): SystemState =
        SystemState(txQueues, procStates, objValues ++ writeSet, lockedObjs, objTimeStamps)

    def acquireLock(o: MemoryObject): SystemState =
        SystemState(txQueues, procStates, objValues, lockedObjs + o, objTimeStamps)
    
    def releaseLocks(objs: Set[MemoryObject]): SystemState =
        SystemState(txQueues, procStates, objValues, lockedObjs -- objs, objTimeStamps)
    
    def updateTimestamps(objs: Set[MemoryObject]): SystemState =
        SystemState(txQueues, procStates, objValues, lockedObjs,
            objTimeStamps.map{case (o,ts) =>  if(objs.contains(o)) (o, ts + 1) else (o, ts)})
}

def startSystem(txQueues: Map[Process, Seq[Transaction]]): SystemState = {
    var procStates = txQueues.mapValues(_ => startProcess)
    var objs = txQueues.values.flatten.flatten(tx => tx.ops).map(op => op.o).toSet
    var objValues = objs.map(o => (o, BigInt(0))).toMap
    var objTimeStamps = objs.map(o => (o, BigInt(0))).toMap
    SystemState(txQueues, procStates, objValues, Set(), objTimeStamps)
}