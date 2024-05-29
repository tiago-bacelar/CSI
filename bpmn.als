/////////////////////////////////////////////////////////////////////////////////
//////////////////////////////// PROCESS ////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////


sig C {}


abstract sig Object {
  ControlFlow: set Object
}

abstract sig Activity extends Object {}
sig Task extends Activity {}
sig ReceiveTask extends Task {}
sig SubProcInvocation extends Activity {
  map: disj one Process
}


abstract sig Event extends Object {}
sig StartEvent extends Event {}

abstract sig IntermediateEvent extends Event {
  Excp: lone Activity
}

sig MessageEvent extends IntermediateEvent {}
sig TimerEvent extends IntermediateEvent {}
sig ErrorEvent extends IntermediateEvent {}

sig EndEvent extends Event {}


abstract sig Gateway extends Object {}

sig ForkGateway extends Gateway {}
sig JoinGateway extends Gateway {}
sig XORGateway extends Gateway {
  Cond: C lone -> Object
}
sig EventGateway extends Gateway {}
sig MergeGateway extends Gateway {}

// Se $o_1 "ControlFlow" o_2$ e $o_1 in "XORGateway"$, entÃ£o, $exists c : c "Cond" (o_1, o_2)$
fact FactOne {
  all x : XORGateway | x.Cond[C] = x.ControlFlow
}

/////////////////////////////////////////////////////////////////////////////////
//////////////////////////////// MODEL //////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////


sig Process {
  objects: set Object
}


sig Model {
  processes: set Process,
  top: one Process
}

fun Sdiamond[m : Model]: SubProcInvocation {
  m.processes.objects & SubProcInvocation
}

fun HR[m : Model]: Process -> Process {
  objects.map & m.processes -> m.processes
}

fact noLooseObjects {
  all o : Object | one objects.o
}

fact noLooseProcesses {
  all p: Process | one processes.p
}

fact FlowInsideProcess {
  objects.ControlFlow.~objects in iden
}

fact ExcpInsideProcess {
  objects.Excp.~objects in iden
}

fact noTopInMap {
  all m : Model | m.top not in Sdiamond[m].map
}

fact topInProcesses {
  all m : Model | m.top in m.processes
}

fact mapInModel {
  all m : Model | Sdiamond[m].map in m.processes
}

fact HRConnected {
  all m : Model | (m.top).*(HR[m]) = m.processes
}


// restricao 2
fact CondSimple {
  lone XORGateway.Cond[C]
}

// restricao 3
fact ExcpSimple {
  lone IntermediateEvent.Excp
}

// restricao 4 
fact StartiInOut {
  no  ControlFlow.StartEvent
  one StartEvent.ControlFlow
}
// restricao nao tem numero
fact StartIsTop { // dá erro
  Model.top in StartEvent

}



run {} for 3 but 2 Process

