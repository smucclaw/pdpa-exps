
#lang forge

option verbose 2
/*
TO DOs: 
=======

-1. Think more about how to model obligation
I think it *is* impt to be able to ask, not just whether it is __possible__ for org to notify affected before being told by PDPA not to do it, but also whether there is a scenario where the org is __required__ to notify the affected before subsequently being told that they must not notify.

OK but how to talk about obligation? 

Maybe:

* the DSL will translate obligation-talk (obligations should be one of the key domain concepts) to constraints that check, at the relevant deadlines (which can be based on time or based on other trigger events), whether the obligation has been met, and that transit to sanctions otherwise
* then when we need to check whether some actor is __obligated / required__ to do X by that deadline (i.e., whether X is an obligation), we can just use something like: is there a next state S' such that, if A does not do X by the deadline state, then A will be sanctioned in S' (in this use case, will move to OrgBrokeLaw state in S' / S' = OrgBrokeLaw)
* This would allow us to ask about obligations in our queries. And we'd be able to use the auxiliary relation trick to keep track in the visualizer of when specific obligations have been fulfilled or violated

Maybe the way to think about how to formulate the query, v2:

* the more general, fundamental principle here might be some sort of 'ought implies can' principle: the requirements / legislation should be such that parties can feasibly comply with them. 
    In particular --- and this would be an especially egregious violation of this principle --- we shouldn't have laws where you can end up breaking the law *even though the actions you took were ones that, in light of the info you had at the time, you might be reasonably expected to take in order to comply with the law*. (not saying the simpler 'had to take' b/c might quibble that the way to avoid possible race conditions is to ask the pdpc first before acting)

* So the queries that the above thought would suggest is: 
    [More general] Is it possible (is there a trace) where Org ends up breaking the law *even though Org's actions would have been permissible in light of the info Org had the time of said actions (i.e., Org's acitons in those states would not have triggered a transition to a sanction in the state where we check tt the operative obligations have been met)*?
    [Special case of the above] Is it possible (is there a trace) where Org ends up breaking the law *even though Org's actions would not only have been permissible, but in fact be what might be reasonably taken to be required to comply with the law, in light of the info Org had the time of said actions*?

These can be turned into properties in obvious ways, properties that can be checked for unsatisfiability.

What I like about this way of framing things:
    * feels like this does a better job of cutting the normative stuff here at its joints: that more general query seems like something we do want to ask about all legislation / contracts in general

----

Another related thought: maybe it is better to say something like 'declare start of obligation' + 'checkIfObligationFulfilled[state after post]` in the transition predicate for the state where the obligation can be performed, so as to be able to model obligations that extend over a particular temporal duration.
Look at how Symboleo does this!!!





0. Fix / check OrgNotifyAffectedIsForever and PDPCNotifyDecisionIsForever (write some examples / property tests)
1. Probably call State 'Time' instead of State
2. Experiment with putting the `next` field in State/time instead of the one sig Trace
3. Do the events / auxiliary relations thing from https://haslab.github.io/formal-software-design/modeling-tips/index.html#improved-visualisation-with-auxiliary-relations to make it clearer what transitions are taking place when!
4. Think more abt how i'm structuring the specification, esp. the traces stuff
5. Add more tests of the specification
6. Write up some tests of the system / properties + some run queries
7. Docs: Write up some docs; Collate simplifying / modelling choices / assumptions somewhere 
8. Do the temporal mode version

----------------------------------------
Legislation: https://sso.agc.gov.sg/Act/PDPA2012?ProvIds=pr3-,pr4-,pr26-,pr26A-,pr26B-,pr26C-,pr26D-

TO DO: Try the  Ray Reiter style of modelling as well! See Jackson Software Abstractions pg 197+

Assumptions
-----------



Notes re modelling approach
---------------------------

OK now that I've thought more about it, mutual exclusion is probably not the best analogy.
* Maybe one important difference is that in this context, the PDPC's decision always takes precedence over Org's, and so the usual, fairer solutions to synchronization won't really apply here. Also, it really dos not matter that PDPC can be in the CS at same time as Org, if PDPC always ends up making the same decision as Org re whether to notify.
* (Another, less impt difference is that here, we are assuming that once either PDPC or the Org gets into the CS --- i.e., once they decide to notify --- they don't ever leave.)



Notes re law
--------------
Re 
> on or after notifying the Commission under subsection (1), the organisation must also notify each affected individual affected by a notifiable data breach mentioned in section 26B(1)(a) in any manner that is reasonable in the circumstances.
There's a crucial difference between this and the req to notify the commission, in that there's no explicit deadline (though there's a vague 'reasonableness' req), whereas the org must notify the Commission no later than 3 days after org figures out that it's a notifiable data breach


Ideas
------
I think that this 'race condition' is a safety property: we only need a finite trace to get the counterexample


To think about
---------------
** Should we use temporal mode? prob best to try both and see how

* auxiliary relations for events, or just using a more events-based approach (where instead of writing a predicate for each operation, a signature is declared whose atoms represent a set of events)
    * see Raymond Reiter. The frame problem in the situation calculus: a simple solution (sometimes) and a completeness result for goal regression and [https://haslab.github.io/formal-software-design/modeling-tips/index.html#an-idiom-to-depict-events] 


[MAYBE] the message passing framework from the crypto case study might be a good way to conceptualize org notifying the PDPC and org notifying person


*/

abstract sig Actor {}
one sig PDPC, Org extends Actor {}
/* Modelling choices to think abt here: 

* I'm currently folding in Affected / Individual into the states instead of treating it as a separate actor to whom messages can be passed, but is that simplification OK?
* Is PDPC really on same ontological level as Org? Might make more sense to have separate sig for PDPC
* Might it be better to fold the PDPC stuff into the states?

======= How to model the state? =============
--- One way: something like

abstract sig WhetherToNotifyAffected {}
one sig NotifyAffected, PDPCSaysDoNotNotifyAffected extends WhetherToNotifyAffected {}

sig State {
    notifyStatus: func Actor -> WhetherToNotifyAffected,
}

--- Another way: use a very barebones main state sig and put the state info in the actor sub sigs 
sig TIME {
    next: lone TIME
}
...


--- Third way: really simplify and just have something like the following one sig states:
1. Initial
2. ThereIsNotifiableDB
3. ...?

*/

/*
Avishkar: distingusih between (i) comapny delibereately notifying individual despite receiving prohibition
and (ii) company notifies idnviidual and then commission 


Joe:
do a precondition check: when do not notify obligation comes into effect, 

two bool flags:
1. individual notified
2. do not notify indivdual
deadlock 

Martin: non-deadlock conception closer to how ppl think about it


I should finish up this model
see if what model checking results we can get out of it, how usefu lit is vis - a vis uppal

modelling of terminologies better in alloy than uppal
* an event is some sort of type, has x y z properties, possibly being triggered by somebody

had class definitions in baby L4 tht were ptu on hold, and that are similar to Alloy sigs
translating classes to Uppal difficult. So Alloy is useful target
*/


abstract sig Notification {}
one sig NotifyAffected, PDPCSaysDoNotNotifyAffected, PDPCNotifiedByOrg extends Notification {}
-- strictly speaking, NotifyAffected has two meanings here: for the PDPC, it means 'Org *must* notify affected', whereas for the org, it will be: Org has notified / is now notifying affected

/*
abstract sig Event {}
one sig InitNotifiableDataBreach, Stutter, OrgBreaksLaw, AllIsGood extends Event {}

Not sure if shld use Event or State for this --- look more closely at the tutorial + try to get better sense for how visualizer would handle this!
*/

sig State {
    notifyStatus: pfunc Actor -> Notification
    -- impt that this be pfunc and not func!

    next: lone State
    /* TO DO another time
    activeObligs: set Obligation,
    violatedObligs: set Obligation // obligs violated so far
    */
}

one sig stInitial, stNotifiableDataBreach, stDeadlineOrgNotifyPDPCAbtNDB, stOrgBrokeLaw, stAllDone extends State {}
--- TO DO: do we even need a AllIsWell/PDPCAndOrgAgree? Look at the oliver good enough paper again!


// abstract sig Event {}
// one sig evObligStart, evObligCheck extends Event {}
-- ignoring *non* notifiable data breaches since those aren't interesting

/*
would it make sense to use sigs for obligations too?
*/

abstract sig Obligation {
    actr: one Actor, 
    // can be set thereof in more complicated models
    // duration: set State, 
    // states where the obligation is active (and where the actor can take the relevant actio nor not),
    // maybe better to put this info in State sig?

    // add check_state and start_of_oblig?

    happy_posts: set State,
    penalty_posts: set State
    // where these are *immediate* post states 
    // from the possible happy and penalty post states, it should be possible to recover the __action(s)__ that the actor must take?
}

one sig oblOrgToNotifyPDPC, oblOrgToNotifyAffected extends Obligation {}
lone sig oblPDPCImposesGagOrder extends Obligation {}

------------------------ UTILITY FUNCS ---------------------------------------------------
-- states that r bet s1 and s2, not inclusive
fun between[s1: State, s2: State]: set State {
    s1.^(Lasso.nextState) & s2.^(~(Lasso.nextState))
}

fun betweenInclLeft[s1: State, s2: State]: set State {
    ( s1.^(Lasso.nextState) & s2.^(~(Lasso.nextState)) ) + s1
}



-- TO DO: do the auxiliary relatiosn thing from https://haslab.github.io/formal-software-design/modeling-tips/index.html#improved-visualisation-with-auxiliary-relations to make it clearer what's hpapening!
-- OrgViolatesLaw
--one sig Initial, OrgRecognizesNotifiableDataBreach extends State {} 
-- assume the req to notify is NOT waived in virtue of the org taking action to "[render] it unlikely that the notifiable data breach will result in significant harm to the affected individual"

pred init[s: State] {
    all actr: Actor | no s.notifyStatus[actr]
    --- linearity of next is handled by the run statements

    s = stNotifiableDataBreach
}

/*
TO DO
Right now im thinking of handling terminal states via extensions of state sig
*/
pred finis[s: State] {
    s = stOrgBrokeLaw or s = stAllDone --- stAllDone = state that we'll move to when we're done triggering and checking all the possible obligations
}

pred stutter[pre: State, post: State] {
    finis[pre] or { not enabledCheckIfOrgRespBrokeLaw[pre] and not enabledCheckIfOrgRespBrokeLaw[pre] }

    pre.notifyStatus = post.notifyStatus
    pre = stOrgBrokeLaw <=> post = stOrgBrokeLaw
    pre = stAllDone <=> post = stAllDone
    pre = stDeadlineOrgNotifyPDPCAbtNDB <=> post = stDeadlineOrgNotifyPDPCAbtNDB
    pre = stNotifiableDataBreach <=> post = stNotifiableDataBreach

}

/*
26D.—(1)  Where an organisation assesses, in accordance with section 26C, that a data breach is a notifiable data breach, the organisation must notify the Commission as soon as is practicable, but in any case no later than 3 calendar days after the day the organisation makes that assessment

(2)  Subject to subsections (5), (6) and (7), on or after notifying the Commission under subsection (1), the organisation must also notify each affected individual affected by a notifiable data breach mentioned in section 26B(1)(a) in any manner that is reasonable in the circumstances.
*/

// TO THINK ABT: Add a deadline state for org to respond to affected?
-- helper pred
pred OrgNotifiesAffectedOnOrAfterNotifyingPDPC[orgRespToNDBState: State] {
    orgRespToNDBState.notifyStatus[PDPC] = PDPCNotifiedByOrg -- guard

    // this is basically an exclusive or: Org either notifies affected at same time as notifying PDPC, or one state after
    not { 
        orgRespToNDBState.notifyStatus[Org] = NotifyAffected <=>
        { some orgRespToNDBState.next and { (orgRespToNDBState.next).notifyStatus[Org] = NotifyAffected } } 
    }
}

-- initial to stDeadlineOrgNotifyPDPCAbtNDB
pred deadlineOrgResponseToNDBNotifyPDPC[pre: State, post: State] {
    // moving to stDeadlineOrgNotifyPDPCAbtNDB (state representing deadline for org to notify PDPC)
    -- GUARDS
    pre = stInitial // might be stronger than what we really want, but nice to keep it simple for now
    PDPCSaysDoNotNotifyAffected not in pre.notifyStatus[PDPC]
    // I'm imagining the edge case where PDPC somehow pre-emptively tells the org not to notify affected people about any possible issues arising from some likely but not yet confirmed notifiable data breach

    -- ACTIONS
    pre.next = post

    // TO CHK: Might the first two be redundant tautologies?

    -- A. What can Org do?
    --- 1. Org either notifies PDPC by deadline, or does not 
    // Simplifying assumption: PDPC does not learn about data breach via other means by the next state
    stDeadlineOrgNotifyPDPCAbtNDB.notifyStatus[PDPC] = PDPCNotifiedByOrg or { no stDeadlineOrgNotifyPDPCAbtNDB.notifyStatus[PDPC] }
    --- 2. Org either (i) notifies affected on or after notifying PDPC, or (ii) does not notify affected individuals
    not { OrgNotifiesAffectedOnOrAfterNotifyingPDPC[stDeadlineOrgNotifyPDPCAbtNDB] <=> { no stDeadlineOrgNotifyPDPCAbtNDB.notifyStatus[Org] } }

    --- frame conditions
}
-- B. [TO DO] What are the consequences of Org's possible choices?
--- ah but which pred should that be in?

pred enabledCheckIfOrgRespBrokeLaw[pre: State] {
    pre = stDeadlineOrgNotifyPDPCAbtNDB
}

pred checkIfOrgRespBrokeLaw[pre: State, post: State] {
    enabledCheckIfOrgRespBrokeLaw[pre]
    
    { PDPCNotifiedByOrg not in pre.notifyStatus[PDPC] or not OrgNotifiesAffectedOnOrAfterNotifyingPDPC[pre] } => post = stOrgBrokeLaw
    /* TO DO: 
    1. Change to the post states of the oblig sig
    2. Refactor: instead of using `pre`, use the duration states of the obligation? i.e., if in any of the duration states we do the right thing, we're good, else we're in trouble... 
    */
}


pred enabledPDPCRespondsToOrg[pre: State] {
    // TO ADD: have not responded before


    // TO DO: Weaken this to: if in pre or in some state before pre, this is the case...
    pre.notifyStatus[PDPC] = PDPCNotifiedByOrg    
}
pred PDPCRespondsToOrg[pre: State, post: State] {
    enabledPDPCRespondsToOrg[pre]

    post.notifyStatus[PDPC] = NotifyAffected or post.notifyStatus[PDPC] = PDPCSaysDoNotNotifyAffected   
}


pred PDPCAndOrgAgree[s: State] {
    NotifyAffected in s.notifyStatus[PDPC] & s.notifyStatus[Org]
    PDPCSaysDoNotNotifyAffected not in s.notifyStatus[PDPC]
}

/*
More simplifying assumptions: Decisions by Org or PDPC re whether to notify affected will persist
*/
    // { some s: State | NotifyAffected in s.notifyStatus[Org] } => 
pred OrgNotifyAffectedIsForever {
    --- enforce that notification status persists in subsequent states of trace

    let stt = {st: State | NotifyAffected in st.notifyStatus[Org]} | 
        // for all subsequent states / times, that notification status persists
        { all s_after: State | s_after in stt.^next => NotifyAffected in s_after.notifyStatus[Org] } 
}
pred PDPCNotifyDecisionIsForever {
    let stt = {st: State | NotifyAffected in st.notifyStatus[PDPC]} | 
        // for all subsequent states / times, that notification status persists
        { all s_after: State | s_after in stt.^next => NotifyAffected in s_after.notifyStatus[PDPC] } 

    let stt2 = {st: State | PDPCSaysDoNotNotifyAffected in st.notifyStatus[PDPC]} | 
        { all s_after: State | s_after in stt2.^next => PDPCSaysDoNotNotifyAffected in s_after.notifyStatus[PDPC] } 
}

pred wellFormedObligations {
    // set the lone / one obligation sigs
}

pred wellformed {
    wellFormedObligations

    OrgNotifyAffectedIsForever
    PDPCNotifyDecisionIsForever
}

pred checkIfAllDone {

}

pred traces {
    /* 
    At least two possible approaches here

    1. Go through the states quasi-manually
    2. Do it like the deadlock and elevator examples, where we have possible transition predicates and enabling conditions for them
        -- Every transition is a valid move
        all s: State | some Trace.next[s] implies {transition[s, Trace.next[s]] or stutter[s, Trace.next[s]]}

    Let's try the quasi-manual approach first 
    */
    wellformed

    init[stInitial]
    no sprev: State | sprev.next = stInitial

    deadlineOrgResponseToNDBNotifyPDPC[stInitial, stDeadlineOrgNotifyPDPCAbtNDB] 
    // TO DO: add the logic about how to handle Org notifying affected at same tiem vs one state after here


    all s: State - stInitial | {
        some s.next implies {
            // TO DO: Think abt: WHEN can PDPC respond to ORg?
            checkIfOrgRespBrokeLaw[s, s.next] or
            PDPCRespondsToOrg[s, s.next] or
            checkIfAllDone[s, s.next]
            stutter[s, s.next]
            }
    }
}

test expect {
    --- tests of specification / model
    wellformedVacuity: { wellformed } is sat
    tracesVacuity: { traces } is sat

    --- tests of the legislation / 'system'
}

run { 
     traces
    } for {next is linear}

    



// pred traces {
//     init 
//     initialToNotifiableDB
// }

// run {
//     traces
// } for 5 Int for {next is linear}















-- maybe the way to talk about DB vs Notifible DB is with a predicate (or with var fields, a la location in the mutual exclusion example), and not sigs?
// abstract sig DataBreach {}
// one sig NonNotifiableDB, NotifiableDB extends DataBreach {}

/*

Scratchpad
--------


 
/*
How to model events?
How should we handle obligations and blame assignment?


pred Obligation[owedFrom, owedTo, duty, prereqs, exemptions, penalty] {

    -- and if penalty not paid (or if no penalty), then owedTo has run afoul of law / contract breached
}

pred BrokenLaw[t: Time, actr: Actor] {

}

maybe to get the contradikcton what we really need is

pred ObligatedToNotify[src, tgt] -- and also interval?



one sig Org extends Actor  {
    obligations:  set Oblig -> Time
}
*/