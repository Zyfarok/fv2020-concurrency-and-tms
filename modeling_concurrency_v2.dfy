module ModelingConcurrency{
  type Process = nat // should be type Process(==)
  const P: set<Process> // processes
  datatype CState = Thinking | Hungry | Eating
  datatype TSState = TSState(ticket: int,
                             serving: int,
                             cs: map<Process, CState>,
                             t: map<Process, int>)
  type Schedule = nat -> Process
  type Trace = nat -> TSState

  class TicketSystem {
    predicate Valid(s: TSState)
    {
      s.cs.Keys == s.t.Keys == P &&
      s.serving <= s.ticket &&
      (forall p :: p in P && s.cs[p] != Thinking ==>
      s.serving <= s.t[p] < s.ticket) &&
      (forall p,q ::
          p in P && q in P && p != q &&
          s.cs[p] != Thinking && s.cs[q] != Thinking
          ==> s.t[p] != s.t[q]) &&
      (forall p :: p in P && s.cs[p] == Eating ==> s.t[p] == s.serving) &&
      (forall i :: s.serving <= i < s.ticket ==> TicketIsInUse(s, i))
    }
    
    predicate Init(s: TSState)
    {
      s.cs.Keys == s.t.Keys == P &&
      s.ticket == s.serving &&
      forall p :: p in P ==> s.cs[p] == Thinking
    }

    predicate Next(s: TSState, s': TSState)
    {
      Valid(s) &&
      exists p :: p in P && NextP(s, p, s')
    }
    
    predicate NextP(s: TSState, p: Process, s': TSState)
      requires Valid(s) && p in P
    {
      Request(s, p, s') || Enter(s, p, s') || Leave(s, p, s')
    }
  
    predicate Request(s: TSState, p: Process, s': TSState)
      requires Valid(s) && p in P
    {
      s.cs[p] == Thinking &&
      s'.ticket == s.ticket + 1 &&
      s'.serving == s.serving &&
      s'.t == s.t[p := s.ticket] &&
      s'.cs == s.cs[p := Hungry]
    }
    
    predicate Enter(s: TSState, p: Process, s': TSState)
      requires Valid(s) && p in P
    {
      s.cs[p] == Hungry &&
      s'.ticket == s.ticket &&
      s'.serving == s.serving &&
      s'.t == s.t &&
      ((s.t[p] == s.serving && s'.cs == s.cs[p := Eating]) ||
      (s.t[p] != s.serving && s'.cs == s.cs))
    }

    predicate Leave(s: TSState, p: Process, s': TSState)
      requires Valid(s) && p in P
    {
      s.cs[p] == Eating &&
      s'.ticket == s.ticket &&
      s'.serving == s.serving + 1 &&
      s'.t == s.t &&
      s'.cs == s.cs[p := Thinking]
    }
    
    predicate IsSchedule(schedule: Schedule)
    {
      forall i :: schedule(i) in P
    }
    
    predicate IsTrace(trace: Trace, schedule: Schedule)
      requires IsSchedule(schedule)
    {
      Init(trace(0)) &&
      forall i: nat ::
          Valid(trace(i)) && NextP(trace(i), schedule(i), trace(i+1))
    }
    
    predicate FairSchedule(schedule: Schedule)
    {
      IsSchedule(schedule) &&
      forall p,n :: p in P ==> HasNext(schedule, p, n)
    }

    predicate HasNext(schedule: Schedule, p: Process, n: nat)
    {
      exists n' :: n <= n' && schedule(n') == p
    }
 
    predicate TicketIsInUse(s: TSState, i: int)
      requires s.cs.Keys == s.t.Keys == P
    {
      exists p :: p in P && s.cs[p] != Thinking && s.t[p] == i
    }
    
    function CurrentlyServedProcess(s: TSState): Process
      requires Valid(s) && exists p :: p in P && s.cs[p] == Hungry
    {
      assert TicketIsInUse(s, s.serving);
      var q :| q in P && s.cs[q] != Thinking && s.t[q] == s.serving;
      q
    }
    
    lemma MutualExclusion(s: TSState, p: Process, q: Process)
      requires Valid(s) && p in P && q in P
      requires s.cs[p] == Eating && s.cs[q] == Eating
      ensures p == q
    {
    }
    
// doesn't hold
//    lemma Invariance(s: TSState, s': TSState)
//      ensures Init(s) ==> Valid(s)
//      ensures Valid(s) && Next(s, s') ==> Valid(s')
//    {    
//    }
    
    lemma GetNextStep(trace: Trace, schedule: Schedule, p: Process, n: nat)
            returns (n': nat)
      requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in P
      requires trace(n).cs[p] != Thinking && trace(n).t[p] == trace(n).serving
      ensures n <= n' && schedule(n') == p
      ensures trace(n').serving == trace(n).serving
      ensures trace(n').cs[p] == trace(n).cs[p]
      ensures trace(n').t[p] == trace(n).t[p]
      ensures forall q :: q in P && trace(n).cs[q] == Hungry ==>
            trace(n').cs[q] == Hungry && trace(n').t[q] == trace(n).t[q]
    {
      assert HasNext(schedule, p, n);
      var u :| n <= u && schedule(u) == p;
      n' := n;
      while schedule(n') != p
      invariant n' <= u
      invariant trace(n').serving == trace(n).serving
      invariant trace(n').cs[p] == trace(n).cs[p]
      invariant trace(n').t[p] == trace(n).t[p]
      invariant forall q :: q in P && trace(n).cs[q] == Hungry ==>
          trace(n').cs[q] == Hungry && trace(n').t[q] == trace(n).t[q]
      decreases u - n'
      {
        n' := n' + 1;
      }
    }
    
    lemma Liveness(trace: Trace, schedule: Schedule, p: Process, n: nat)
          returns (n': nat)
      requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in P
      requires trace(n).cs[p] == Hungry
      ensures n <= n' && trace(n').cs[p] == Eating
    {
      n' := n;
      while true
        invariant n <= n' && trace(n').cs[p] == Hungry
        decreases trace(n').t[p] - trace(n').serving
      {
        // find the currently served process and follow it out of the kitchen
        var q := CurrentlyServedProcess(trace(n'));
        if trace(n').cs[q] == Hungry {
          n' := GetNextStep(trace, schedule, q, n');
          n' := n' + 1; // take the step from Hungry to Eating
          if p == q {
            return;
          }
        }
        n' := GetNextStep(trace, schedule, q, n');
        n' := n' + 1; // take the step from Eating to Thinking
      }
    }
  }
}

