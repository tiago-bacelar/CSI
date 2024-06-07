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


// restricao nao tem numero
fact StartIsTop { // dá erro
  //Model.top in StartEvent

}

// restricao 2
fact CondSimple {
  lone XORGateway.Cond[C]
}

// restricao 3
fact ExcpSimple {
  lone IntermediateEvent.Excp
}



// restricao 4.1
fact StartiInOut {
  no  ControlFlow.StartEvent
  one StartEvent.ControlFlow
}
// restricao 4.2 - para onde a exceção me leva não pode ter outras entradas
fact ExcpInOut {
  all ie : IntermediateEvent | all ie2: Excp.(Activity - ie.Excp) | no ie2 -> ie.Excp

}

// 5. $forall s in "EndEvent", "out"(s) = emptyset and abs("in"(s)) = 1$
fact EndEventInOut {
	one ControlFlow.EndEvent 
	no EndEvent.ControlFlow
}

// 6 .1 
fact ActivityInOut {
	one ControlFlow.Activity 
	one Activity.ControlFlow
}

// 6.2
fact IntermidiateEvent{
  all i : Excp.(Activity - IntermediateEvent.Excp) 
  		| one ControlFlow.i and one i.ControlFlow
}

// 7.1
fact ForkGatewayInOut { // não sei porque não consegui por em pointfree
  all f:ForkGateway | one ControlFlow.f and some f.ControlFlow
}

// 7.2
fact XORGatewayInOut { // não sei porque não consegui por em pointfree
  all f:XORGateway | one ControlFlow.f and some f.ControlFlow
}

// 7.3
fact EventGatewayInOut { // não sei porque não consegui por em pointfree
  all f:EventGateway | one ControlFlow.f and some f.ControlFlow
}
//8.1

fact JoinGatewayInOut { // não sei porque não consegui por em pointfree
  all f:JoinGateway | some ControlFlow.f and one f.ControlFlow
}

//8.2 
fact MergaGatewayInOut { // não sei porque não consegui por em pointfree
  all f:MergeGateway | some ControlFlow.f and one f.ControlFlow
}


// 9
fact EventGatewayIn {
  all f:EventGateway | f.ControlFlow in MessageEvent + TimerEvent + ReceiveTask
}


// 10 
// 11
// 12



run {} for 3 but 2 Process

