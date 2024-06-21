
/*
 * Authors:  
 * 	Miguel Ferreira	<pg10961@alunos.uminho.pt>
 * 	Samuel Silva   	<pg11034@alunos.uminho.pt>
 * Description: 
 *		This library was developed in the context of the
 *		FMSE (Formal Methods and Software Engineering)
 *		classes, see eg. www.di.uminho.pt/~jno/html/mfes-0708.html
 * Conventions:
 * 	- All relations begin with capital letters
 * 	- All functions begin with lowercase letters
 */

/***********************************************/

/**Id Definition*/
fun id[S: set univ] : univ -> univ {
	(S -> S) & iden
}

/**Kernel Definition*/
fun ker [R : univ -> univ] : univ -> univ {
	R . (~R)
}

/**Image Definition*/
fun img [R : univ -> univ] : univ -> univ {
	(~R) . R
}

/**Domain Definition*/
fun dom [R: univ->univ] : set (R.univ) { 
	R.univ
}

/**Domain as coreflexive */
fun delta [R : univ -> univ] : univ -> univ {
	ker[R] & iden
}

/**Range Definition*/
fun rng [R: univ->univ] : set (univ.R) { 
	univ.R
}

/**Range as coreflexive */
fun rho [R : univ -> univ] : univ -> univ {
	img[R] & iden
}

/***********************************************/

/**Reflexive Definition*/
pred Reflexive [R : univ -> univ, S: set univ] {
	id[S] in R
--	S <: iden in R
}

/**Correflexive Definition*/
pred Coreflexive [R : univ -> univ, S: set univ] {
	R in id[S]
--	S <: R in iden
}

/**Five Relations*/
pred Symmetric [R : univ -> univ] {
	R in ~R
}
pred Transitive [R : univ -> univ] {
	R.R in R
}
pred Cotransitive [R: univ -> univ] {
	R in R.R
}
pred Antisymmetric [R: univ -> univ, S: univ] {
	R & ~R in id[S]
}

/**Four Relations*/
pred Per [R: univ -> univ] {
	Symmetric[R]
	Transitive[R]
	Cotransitive[R]
}
pred Preorder [R: univ -> univ, S: set univ] {
	Transitive[R]
	Reflexive[R,S]
}
pred Equivalence [R: univ -> univ, S: set univ] {
	Per[R]
	Preorder[R,S]
}
pred Partialorder [R: univ -> univ, S: set univ] {
	Preorder[R,S]
	Antisymmetric[R,S]
}

/**Two Relations*/
pred Id [R: univ -> univ, S: set univ] {
	Coreflexive[R,S]
	Equivalence[R,S]
	Partialorder[R,S]
}
pred Linearorder [R: univ -> univ, S: set univ] {
	Partialorder[R,S]
	Connected[R,S]
}
pred Connected [R : univ -> univ, S: set univ] {
	(R + ~R) = (S -> S)
}

/** Four Relations */
pred Simple [R: univ -> univ, S: set univ] {
--	img[R] in id[S]}
	Coreflexive[img[R],S]}
pred Entire [R: univ -> univ, S: set univ] {
--	id[S] in ker[R]}
	Reflexive[ker[R],S]}
pred Surjective [R: univ -> univ, S: set univ] {
	id[S] in img[R]
--	Reflexive[img[R],S]
}
pred Injective [R: univ -> univ, S: set univ] {
--	ker[R] in id[S]}
	Coreflexive[ker[R],S]}

/** Four Relations */
pred Function [R: univ -> univ, A,B: set univ] {
	Simple[R,B]
	Entire[R,A]
}
pred Representation [R: univ -> univ, A: set univ] {
	Injective[R,A]
	Entire[R,A]
}
pred Abstraction [R: univ -> univ, B: set univ] {
	Simple[R,B]
	Surjective[R,B]
}
pred Bijection [R: univ -> univ, A, B: set univ] {
	Representation[R,A]
	Abstraction[R,B]
}

/***********************************************/

/** More Relations */
pred Assymetric [R: univ -> univ] {
	~R not in R
}
pred Acyclic [R: univ -> univ, S: set univ] {
	no ^R & id[S]
}

/***********************************************/

/** Galois Conections */
/*pred Galois [A,B: univ, f: A->B, g: B -> A] {
	Function[f]
	Function[g]
	f[A] in B <=> A in g[B]
--	f[Dom[f]] in Dom[g] <=> Dom[f] in g[Dom[g]]
--	A in (f.g)[A]
--	(g.f)[B] in B
}
*/
/***********************************************/

/**Utilities*/
fun converse [R: univ -> univ] : univ -> univ { ~R}
--fun dot [f,g: univ -> univ] : univ -> univ {g.f}

fun oplus[R,S: univ -> univ] : univ -> univ
{
--  S + (R - (dom[S] <: R))
    S + (univ - dom[S]) <: R
}

fun flip[R:univ -> univ -> univ]: univ -> univ -> univ {
   { b: univ, a: univ, c: univ | c in b.(a.R) }
}

/***********************************************/

/**reflexive and transitive closure*/
fun rtc[S: univ, r: univ -> univ] : univ -> univ {
	(S -> S) & *r
}


/////////////////////////////////////////////////////////////////////////////////
//////////////////////////////// PROCESS ////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////


sig C {}


abstract sig Object {
  process: Process,
  ControlFlow: set Object
}

abstract sig Activity extends Object {}
sig Task extends Activity {}
sig ReceiveTask extends Task {}
sig SubProcInvocation extends Activity {
  map: disj one Process // requisito 21 (parte 1)
}


abstract sig Event extends Object {}
sig StartEvent extends Event {}

abstract sig IntermediateEvent extends Event {
  Excp: lone Activity // requisito 3
}

sig MessageEvent extends IntermediateEvent {}
sig TimerEvent extends IntermediateEvent {}
sig ErrorEvent extends IntermediateEvent {}

sig EndEvent extends Event {}


abstract sig Gateway extends Object {}

sig ForkGateway extends Gateway {}
sig JoinGateway extends Gateway {}
sig DataGateway extends Gateway {
  Cond: C lone -> Object // requisito 1
}
sig EventGateway extends Gateway {}
sig MergeGateway extends Gateway {}


sig Process {}
one sig Top in Process {}


// este facto não é estritamente necessário, serve apenas para simplificar os modelos gerados
fact noLooseConditions {
  all c: C | some g: DataGateway | some g.Cond[c]
}

/////////////////////////////////////////////////////////////////////////////////
//////////////////////////////// UTILS //////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

//negation of iden
fun dif[S: set univ] : S -> S { (S->S) - iden }

pred in0 [S: set Object] { no ControlFlow.S }
pred out0[S: set Object] { no S.ControlFlow }
pred in1 [S: set Object] { Function[~ControlFlow&(S->Object),S,Object] }
pred out1[S: set Object] { Function[ControlFlow&(S->Object),S,Object] }
pred inN [S: set Object] { ControlFlow.(id[S]) in dif[Object].ControlFlow.(id[S]) }
pred outN[S: set Object] { id[S].ControlFlow in id[S].ControlFlow.(dif[Object]) }
// Não é necessário obrigar pelo menos uma entrada e saída, uma vez que isso é garantido pelos requisitos 16 e 17

fun HR: Process -> Process {
  (~process).map
}

/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////// REQUIREMENTS ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////


// requisito 2
fact DataGatewayExitsHaveACondition {
  all x : DataGateway | x.Cond[C] = x.ControlFlow
}


// requisito 4 
fact StartEventDegrees {
  in0[StartEvent]
  out1[StartEvent]
}

// requisito 5
fact EndEventDegrees {
  in1[EndEvent]
  out0[EndEvent]
}

// requisito 6
fact ActivityDegrees {
  in1[Activity]
  out1[Activity]
}

// requisito 7
fact IntermediateEventDegrees {
  in1[IntermediateEvent-dom[Excp]]
  in0[IntermediateEvent&dom[Excp]]
  out1[IntermediateEvent]
}

// requisito 8
fact ForkGatewayDegrees {
  in1[ForkGateway]
  outN[ForkGateway]
}

// requisito 9
fact DataGatewayDegrees {
  in1[DataGateway]
  outN[DataGateway]
}

// requisito 10
fact EventGatewayDegrees {
  in1[EventGateway]
  outN[EventGateway]
}

// requisito 11
fact JoinGatewayDegrees {
  inN[JoinGateway]
  out1[JoinGateway]
}

// requisito 12
fact MergeGatewayDegrees {
  inN[MergeGateway]
  out1[MergeGateway]
}

// requisito 13
fact EventGatewayExits {
  EventGateway.ControlFlow in MessageEvent + TimerEvent + ReceiveTask
}

// requisito 14
fact DataGatewayExitsOrder {
  //Alloy não suporta quantificações de ordem superior, mas isso não interessa uma vez que este requisito é trivial em modelos finitos
  //all g: DataGateway | some order: Object->Object | Linearorder[order,Object]
}

// requisito 15
fact DataGatewayMinExit {
  //Igual ao requisito anterior
}

// requisito 16
fact FlowStart {
  //Object in (StartEvent+dom[Excp]).*ControlFlow
  Surjective[*ControlFlow & ((StartEvent+dom[Excp])->Object),Object]
  //Surjective[*(ControlFlow+~Excp) & (StartEvent->Object),Object]
}

// requisito 17
fact FlowEnd {
  //Object in *ControlFlow.EndEvent
  Surjective[~*ControlFlow & (EndEvent->Object),Object]
}

// requisito 18
fact FlowInsideProcess {
  ControlFlow in ker[process]
  Excp in ker[process]
}

// requisito 19
fact ConnectedHR {
  //Top.*HR = Process
  //*(HR+~HR) = Process->Process
  Process->Process in *(HR+~HR)
}

// requisito 20
fact AcyclicHR {
  no ^HR & iden
}

// requisito 21 (parte 2)
fact MapSurjectiveButTop {
  Top not in Process.HR
}


run {} for 5

