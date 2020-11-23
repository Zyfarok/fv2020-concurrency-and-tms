module ModelingConcurrency{
  type Process = nat // should be type Process(==)
  datatype CState = Thinking | Hungry | Eating

  class TicketSystem {
    var ticket: int
    var serving: int
    const P: set<Process> // processes
    var cs: map<Process, CState> // state each process is in
    var t: map<Process, int> // tickets held by each state
  
    constructor (processes: set<Process>)
      ensures Valid() && P == processes
    {
      P := processes;
      ticket := serving;
      cs := map p | p in processes :: Thinking;
      t := map p | p in processes :: 0;
    }
    
    predicate Valid()
      reads this
    {
      && cs.Keys == t.Keys == P
      && serving <= ticket
      && (forall p :: p in P && cs[p] != Thinking ==> serving <= t[p] < ticket)
      && (forall p,q ::
            p in P && q in P && p != q &&
            cs[p] != Thinking && cs[q] != Thinking
            ==> t[p] != t[q])
      && (forall p :: p in P && cs[p] == Eating ==> t[p] == serving)
    }
  
    method Request(p: Process)
      requires Valid() && p in P && cs[p] == Thinking
      modifies this
      ensures Valid()
    {
      t, ticket := t[p := ticket], ticket + 1;
      cs := cs[p := Hungry];
    }
    
    method Enter(p: Process)
      requires Valid() && p in P && cs[p] == Hungry
      modifies this
      ensures Valid()
    {
      if t[p] == serving {
        cs := cs[p := Eating];
      }
    }
    
    method Enter0(p: Process)
      requires Valid() && p in P && cs[p] == Hungry && t[p] == serving
      modifies this
      ensures Valid()
    {
      cs := cs[p := Eating];
    }
    
    method Leave(p: Process)
      requires Valid() && p in P && cs[p] == Eating
      modifies this
      ensures Valid()
    {
      serving := serving + 1;
      cs := cs[p := Thinking];
    }
    
    method Run(processes: set<Process>)
      requires processes != {}
      decreases *
    {
      var ts := new TicketSystem(processes);
      while exists p :: p in ts.P &&
            (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving)
        invariant ts.Valid()
        decreases *
      {
        var p :| p in ts.P && (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving);
        match ts.cs[p] {
          case Thinking => ts.Request(p);
          case Hungry => ts.Enter0(p);
          case Eating => ts.Leave(p);
        }
      }
    }
    
    // run method that records scheduling choices and sequence of states
    method RunRecord(processes: set<Process>)
      requires processes != {}
      decreases *
    {
      var ts := new TicketSystem(processes);
      var schedule := [];
      var trace := [(ts.ticket, ts.serving, ts.cs, ts.t)];
      while exists p :: p in ts.P &&
            (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving)
        invariant ts.Valid()
        decreases *
      {
        var p :| p in ts.P && (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving);
        schedule := schedule + [p];
        match ts.cs[p] {
          case Thinking => ts.Request(p);
          case Hungry => ts.Enter0(p);
          case Eating => ts.Leave(p);
        }
        trace := trace + [(ts.ticket, ts.serving, ts.cs, ts.t)];
      }
    }
    
// doesn't work
//    method RunFromSchedule2(processes: set<Process>, schedule: nat -> Process)
//      requires processes != {}
//      requires forall n :: schedule(n) in processes
//      decreases *
//    {
//      var ts := new TicketSystem(processes);
//      var n := 0;
//      while true
//        invariant ts.Valid()
//        decreases *
//      {
//        var p := schedule(n);
//        match ts.cs[p] {
//          case Thinking => ts.Request(p);
//          case Hungry => ts.Enter(p);
//          case Eating => ts.Leave(p);
//        }
//        n := n + 1;
//      }
//    }
    
    lemma MutualExclusion(p: Process, q: Process)
      requires Valid() && p in P && q in P
      requires cs[p] == Eating && cs[q] == Eating
      ensures p == q
    {
    }  
  }
}
