/////////////////////////////////////////////////////////////////////////////////
//////////////////////////////// PROCESS ////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////


sig C {}

sig Object {
ControlFlow: set Object
}

sig Activity extends Object {}

sig Task extends Activity {}

sig SubProcInvocation extends Activity {}

sig ReceiveTask extends Task {}

sig NonReceiveTask extends Task {}

sig Event extends Object {}

sig StartEvent extends Event {}

sig IntermediateEvent extends Event {
Excp: lone Activity
}

sig EndEvent extends Event {}

sig MessageEvent extends IntermediateEvent {}

sig TimerEvent extends IntermediateEvent {}

sig ErrorEvent extends IntermediateEvent {}

sig Gateway extends Object {}

sig ForkGateway extends Gateway {}
sig JoinGateway extends Gateway {}

sig XORGateway extends Gateway {
  Cond: Object -> lone C
}
sig EventGateway extends Gateway {}
sig MergeGateway extends Gateway {}

// Se $o_1 "ControlFlow" o_2$ e $o_1 in "XORGateway"$, entÃ£o, $exists c : c "Cond" (o_1, o_2)$
fact FactOne {
  all x : XORGateway | all y : x.ControlFlow | one x.Cond[y]
}


/////////////////////////////////////////////////////////////////////////////////
//////////////////////////////// MODEL //////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////


sig Process {
  objects: some Object
}


one sig Model {
  processes: some Process,
  top: one Process,
  map: SubProcInvocation lone -> one Process,
  HR: Process -> Process
}

fact noLooseObjects {
  all o : Object | one p : Process | o in p.objects
}

fact noTopInMap {
  all m : Model | all s : SubProcInvocation | m.map[s] != m.top
}

fact HRConnected {
  all m : Model | (m.top).*(m.HR) = m.processes
}

fact mapConnectivity {
  all m : Model | all p1, p2 : m.processes | (p1->p2) in m.HR iff (some s : p1.objects & SubProcInvocation | m.map[s] = p2)
}

fact topInProcesses {
  all m : Model | m.top in m.processes
} 

fact processesInModel {
  all m : Model | m.map in SubProcInvocation -> m.processes 
}


run {} for 3 but 2 Process
