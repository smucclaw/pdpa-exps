#lang forge

option verbose 2
/*
TO DOs: 
=======

Ideas: 

Perhaps for each obligation, we should have:
* an 'oblig intro predicate':  state transition pred that introduces the obligation when guard is met and that MAYBE specifies when in the future to check for whether the obligation has been met (this can made into another predicate)
    MAYBE coz not clear whether this shld be done in this pred, or just be left to something else like the oblig check predicate
    maybe just say: in 3 steps, move to DedlnForThisOblig state? 
        But hmm, that works well for obligs with temporal deadlines, but wht if the deadline is not temporal, but rather conditional on some other event's obtaining? But OK it shouldn't be hard to tweak the code to get that too for those sorts of obligations
* an 'oblig check predicate': state transition pred that has as guard the condition from above for when to check whether the obligation in quesiton has been met, and that transitions to penalty state if obligation hasn't been met



-1. Think more about how to model obligation
I think it *is* impt to be able to ask, not just whether it is __possible__ for org to notify affected before being told by PDPA not to do it, but also whether there is a scenario where the org is __required__ to notify the affected before subsequently being told that they must not notify.

OK but how to talk about obligation? 

Maybe:

* the DSL will translate obligation-talk (obligations should be one of the key domain concepts) to constraints that check, at the relevant dedlns (which can be based on time or based on other trigger events), whether the obligation has been met, and that transit to sanctions otherwise
* then when we need to check whether some actor is __obligated / required__ to do X by that dedln (i.e., whether X is an obligation), we can just use something like: is there a next state S' such that, if A does not do X by the dedln state, then A will be sanctioned in S' (in this use case, will move to OrgBrokeLaw state in S' / S' = OrgBrokeLaw)
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
There's a crucial difference between this and the req to notify the commission, in that there's no explicit dedln (though there's a vague 'reasonableness' req), whereas the org must notify the Commission no later than 3 days after org figures out that it's a notifiable data breach


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
*/

abstract sig Notification {}
one sig nNotifyAffected, nOrgNOTnotifyAffected, nPDPCSaysDoNotNotifyAffected extends Notification {}
one sig nOrgNotifiesPDPC, nOrgNOTnotifyPDPC extends Notification {}
-- strictly speaking, nNotifyAffected has two meanings here: for the PDPC, it means 'Org *must* notify affected', whereas for the org, it will be: Org has notified / is now notifying affected

/*
abstract sig Event {}
one sig InitNotifiableDataBreach, Stutter, OrgBreaksLaw, AllIsGood extends Event {}

Not sure if shld use Event or State for this --- look more closely at the tutorial + try to get better sense for how visualizer would handle this!
*/
// Important modelling invariant: put all state-related stuff in this sig! That way will be clear what frame conditions etc to use 
sig State {
    notifyStatus: pfunc Actor -> Notification,
    -- impt that this be pfunc and not func!
    -- what notification(s) / notification decision(s) Actor has made

    next: lone State
    /* TO DO another time
    activeObligs: set Obligation,
    violatedObligs: set Obligation // obligs violated so far
    */
}

one sig stNDBreach, stDedlnOrgNotifyPDPC, stOrgBrokeLaw, stOrgNoLawBroken extends State {}
--- TO DO: do we even need a AllIsWell/PDPCAndOrgAgree? Look at the oliver good enough paper again!


// abstract sig Event {}
// one sig evObligStart, evObligCheck extends Event {}
-- ignoring *non* notifiable data breaches since those aren't interesting

// abstract sig Obligation {
//     actr: one Actor, 
//     // can be set thereof in more complicated models
//     // duration: set State, 
//     // states where the obligation is active (and where the actor can take the relevant actio nor not),
//     // maybe better to put this info in State sig?

//     // in this specification, all the obligations have exactly one trigger and exactly one check state
//     // oblig_trigger: one State, 
//     // Actually, may not make sense to include this given that oblig trigger may often include predicates, and so it may make more sense to just put that in the oblig introduction predicate
    
//     oblig_check: one State,
//     happy_posts: set State,
//     sanction_posts: lone State 
//     // in the more general case, this would be `set` and not `lone`
//     // where these are *immediate* post states 
//     // from the possible happy and sanction post states, it should be possible to recover the __action(s)__ that the actor must take?
// }

// one sig oblOrgToNotifyPDPC, oblOrgToNotifyAffected extends Obligation {}
// lone sig oblOrgSilencedByPDPC extends Obligation {}

// TO DO: Will have to addd obligation-related frame conditions and change preds too!


------------------------ UTILITY FUNCS ---------------------------------------------------
fun statesBefore[s: State]: set State {
    s.^(~next)
}

-- states that r bet s1 and s2, not inclusive
fun between[s1: State, s2: State]: set State {
    s1.^next & statesBefore[s2]
}

fun betweenInclLeft[s1: State, s2: State]: set State {
    ( s1.^next & s2.^(~next) ) + s1
}


-- TO DO: do the auxiliary relatiosn thing from https://haslab.github.io/formal-software-design/modeling-tips/index.html#improved-visualisation-with-auxiliary-relations to make it clearer what's hpapening!
-- OrgViolatesLaw
--one sig Initial, OrgRecognizesNotifiableDataBreach extends State {} 
-- assume the req to notify is NOT waived in virtue of the org taking action to "[render] it unlikely that the notifiable data breach will result in significant harm to the affected individual"

------------ PREDS -------------------------------------------------

// OK don't worry about obligs till I've got the overall structure of the states sorted out!
// pred initOblOrgSilencedByPDPC {
//     oblOrgSilencedByPDPC.actr = Org
//     oblOrgSilencedByPDPC.oblig_trigger = 
//     oblOrgSilencedByPDPC.oblig_check = 
//     oblOrgSilencedByPDPC.happy_posts = 
//     oblOrgSilencedByPDPC.sanction_posts = 
// }

// pred initOblOrgToNotifyPDPC {
//     oblOrgToNotifyPDPC.actr = Org
//     oblOrgToNotifyPDPC.oblig_trigger = stNDBreach
//     oblOrgToNotifyPDPC.oblig_check = stDedlnOrgNotifyPDPC
//     oblOrgToNotifyPDPC.happy_posts = 
//     oblOrgToNotifyPDPC.sanction_posts = 
// }

// pred initOblOrgToNotifyAffected {
//     oblOrgToNotifyAffected.actr = Org
//     oblOrgToNotifyAffected.oblig_trigger = stNDBreach
//     oblOrgToNotifyAffected.oblig_check = stDedlnOrgNotifyPDPC
//     oblOrgToNotifyAffected.happy_posts = 
//     oblOrgToNotifyAffected.sanction_posts = 
// }

// pred initObligations[initialst: State] {
//     // set the lone / one obligation sigs
//     initOblOrgToNotifyPDPC
//     initOblOrgToNotifyAffected
//     oblOrgSilencedByPDPC in initialst.*next => initOblOrgSilencedByPDPC
// }

pred initNDB[s: State] {
    all actr: Actor | no s.notifyStatus[actr]
    --- linearity of next is handled by the run statements

}

/*
TO DO
Right now im thinking of handling terminal states via extensions of state sig
*/
pred finis[s: State] { // check if we're in a 'terminal' state
    s = stOrgBrokeLaw or s = stOrgNoLawBroken --- stOrgNoLawBroken = state that we'll move to when we're done triggering and checking all the possible obligations and Org did not break law
}

pred someSubstantiveTransEnabled[pre: State] {
    enabledOrgPotentiallyNotifiesAffected[pre] or 
    enabledOrgPotentiallyNotifiesPDPC[pre] or 
    enabledPostprocessOrgNotifPDPC[pre] or
    enabledPostprocessOrgNotifiesAffected[pre] or

    enabledPDPCRespondsToOrg[pre] or
    enabledPostprocessPDPCRespondsToOrg[pre]
}
// TO DO: Chk / refactor
pred stutter[pre: State, post: State] {
    finis[pre] or { not someSubstantiveTransEnabled[pre] }

    pre.notifyStatus = post.notifyStatus
    pre = stOrgBrokeLaw <=> post = stOrgBrokeLaw
    pre = stOrgNoLawBroken <=> post = stOrgNoLawBroken
    pre = stDedlnOrgNotifyPDPC <=> post = stDedlnOrgNotifyPDPC
    pre = stNDBreach <=> post = stNDBreach
}

/*
26D.—(1)  Where an organisation assesses, in accordance with section 26C, that a data breach is a notifiable data breach, the organisation must notify the Commission as soon as is practicable, but in any case no later than 3 calendar days after the day the organisation makes that assessment

(2)  Subject to subsections (5), (6) and (7), on or after notifying the Commission under subsection (1), the organisation must also notify each affected individual affected by a notifiable data breach mentioned in section 26B(1)(a) in any manner that is reasonable in the circumstances.

(6)  An organisation must not notify any affected individual in accordance with subsection (2) if —
(a)	a prescribed law enforcement agency so instructs; or
(b)	the Commission so directs.

How I'm thinking about (6):
* we might imagine the obligation from (2) just being waived / vanishing once the Comission says that ppl shldn't be notified, and a new obligation to not notify coming into play

*/

-- helper fn
fun preStatesWithPriorNotifn (actr: Actor, notifn: Notification, pre: State): set State {
    {s: State | s in (statesBefore[pre] + pre) and notifn in s.notifyStatus[actr]}
}

-- IMPT: orgPotentiallyNotifiesPDPC and orgPotentiallyNotifiesAffected are NOT 'happy path / what a law-abiding Org would do' preds. 
-- Think of them instead as 'what it minimally takes for the state transitions to be wellformed / for the specification to work' preds

pred enabledOrgPotentiallyNotifiesPDPC[pre: State] {
    // 1. Org has not made this move (potentially notifying PDPC) in pre or before
    no preStatesWithPriorNotifn[Org, nOrgNotifiesPDPC, pre]
    no preStatesWithPriorNotifn[Org, nOrgNOTnotifyPDPC, pre]

    // 3. Rule out the edge case where PDPC somehow pre-emptively tells the org not to notify affected people about any possible issues arising from some likely but not yet confirmed notifiable data breach
    nPDPCSaysDoNotNotifyAffected not in pre.notifyStatus[PDPC]
}

pred orgPotentiallyNotifiesPDPC[pre: State, post: State] {
    enabledOrgPotentiallyNotifiesPDPC[pre]
    
    -- ACTIONS
    // 1. Org either notifies PDPC or does not 
    not orgPotentiallyNotifiesAffected[pre, post] => {
        post.notifyStatus[Org] = pre.notifyStatus[Org] + nOrgNotifiesPDPC or
        post.notifyStatus[Org] = (pre.notifyStatus[Org] + nOrgNOTnotifyPDPC)
    }
    orgPotentiallyNotifiesAffected[pre, post] => {
        post.notifyStatus[Org] = pre.notifyStatus[Org] + nOrgNotifiesPDPC + nNotifyAffected or
        post.notifyStatus[Org] = pre.notifyStatus[Org] + nOrgNotifiesPDPC + nOrgNOTnotifyAffected or
        post.notifyStatus[Org] = pre.notifyStatus[Org] + nOrgNOTnotifyPDPC + nNotifyAffected or
        post.notifyStatus[Org] = pre.notifyStatus[Org] + nOrgNOTnotifyPDPC + nOrgNOTnotifyAffected 
    }
    // this alrdy encodes a frame condition as well
    // note tt we want it to be possible for org to inform affected at same time as they inform pdpc

    --- other frame conditions 
    post.notifyStatus[PDPC] = pre.notifyStatus[PDPC]
    // Modelling assumption: PDPC cannot respond to Org at the same time that Org notifies PDPC; there needs to be at least one tick in between

    // TO DO: include oblig related state when get around to adding that
}

pred enabledPostprocessOrgNotifPDPC[pre: State] {
    nOrgNOTnotifyPDPC in pre.notifyStatus[Org] or nOrgNotifiesPDPC in pre.notifyStatus[Org]
}
pred postprocessOrgNotifiesPDPC[pre: State, post: State] {
    enabledPostprocessOrgNotifPDPC[pre]

    // Make sure the PDPC related notification flags not in post
    nOrgNotifiesPDPC not in post.notifyStatus[Org]
    nOrgNOTnotifyPDPC not in post.notifyStatus[Org]
}


pred enabledOrgPotentiallyNotifiesAffected[pre: State] {
    // 1. First time Org considering whether to notify affected / making this move wrt affected
    // no {s: State | s in statesBefore[pre] and OrgPotentiallyNotifiesAffected[s, s.next]}
    // I think the above is just super computationally intensive -- need to replace with something else!
    no preStatesWithPriorNotifn[Org, nNotifyAffected, pre]
    no preStatesWithPriorNotifn[Org, nOrgNOTnotifyAffected, pre]

    /* NOT requiring tt 
        (i) Org have informed PDPC before this, 
        or 
        (ii)  PDPC not have told Org not to notify
    because orgPotentiallyNotifiesAffected isn't supposed to be a 'happy path only' predicate 
    orgPotentiallyNotifiesAffected is more like a 'what it takes for the state transition to be well-formed' predicate 
    */
}
pred orgPotentiallyNotifiesAffected[pre: State, post: State] {
    enabledOrgPotentiallyNotifiesAffected[pre]

    -- ACTIONS
    nOrgNOTnotifyAffected in post.notifyStatus[Org] or 
    nNotifyAffected in post.notifyStatus[Org]

    --- other frame conditions 
    // Do NOT say that post.notifyStatus[PDPC] must = pre's!
    
    // TO DO: include oblig related state when get around to adding that
}

pred enabledPostprocessOrgNotifiesAffected[pre: State] {
    nNotifyAffected in pre.notifyStatus[Org] or nOrgNOTnotifyAffected in pre.notifyStatus[Org]
}
pred postprocessOrgNotifiesAffected[pre: State, post: State] {
    enabledPostprocessOrgNotifiesAffected[pre]

    // post.notifyStatus[Org] = pre.notifyStatus[Org] - nNotifyAffected - nOrgNOTnotifyAffected
    nNotifyAffected not in post.notifyStatus[Org]
    nOrgNOTnotifyAffected not in post.notifyStatus[Org]
}


pred enabledPDPCRespondsToOrg[pre: State] {
    // Require that PDPC has not made any kind of response before
    no {s: State | s in (statesBefore[pre] + pre) and some s.notifyStatus[PDPC]}

    // Simplifying modelling assunmption: Require that in pre or in some state before pre, Org has notified PDPC (not just that they've considered doing so!)
    some preStatesWithPriorNotifn[Org, nOrgNotifiesPDPC, pre]
}
// TO DO: Check this, have been refactoring a lot
pred PDPCRespondsToOrgIfOrgHadNotified[pre: State, post: State] {
    enabledPDPCRespondsToOrg[pre]

    post.notifyStatus[PDPC] = nNotifyAffected or post.notifyStatus[PDPC] = nPDPCSaysDoNotNotifyAffected   
    // Simplifying modelling assumption: PDPC won't just ignore Org's notification and do nothing

    // TO DO: Handle oblig triggering and exempting stuff based on whether PDPC says to or not to notify affected
}

pred enabledPostprocessPDPCRespondsToOrg[pre: State] {
    nNotifyAffected in pre.notifyStatus[PDPC] or nPDPCSaysDoNotNotifyAffected in pre.notifyStatus[PDPC]
}
pred postprocessPDPCRespondsToOrg[pre: State, post: State] {
    enabledPostprocessPDPCRespondsToOrg[pre]

    nNotifyAffected not in post.notifyStatus[PDPC] 
    nPDPCSaysDoNotNotifyAffected not in post.notifyStatus[PDPC]
}


pred checkIfSomeObligationViolated[oblig: Obligation, pre: State, post: State] {
    -- Guards
    // Chk that pre is in oblig's oblig_check states

    -- Actions
    // Remove the obligation in question from set of active obligations
    // If obligation violated, go to sanction state
    // else, go to ...?
}



--- TO DO: we'll also want some way to checking if all active obligations to date will be satisfied in light of the actions that have been taken
pred checkIfActiveObligsToDateSatisfied[pre: State, post: State] {
    
    // { nOrgNotifiesPDPC not in pre.notifyStatus[PDPC] or not orgNotifiesAffectedOnOrAfterNotifyingPDPC[pre] } => post = stOrgBrokeLaw
    /* TO DO: 
    1. Change to the post states of the oblig sig
    2. Refactor: instead of using `pre`, use the duration states of the obligation? i.e., if in any of the duration states we do the right thing, we're good, else we're in trouble... 
    */
}


pred enabledCheckAllObligsAtFinalDedln[pre: State] {
    // TO DO: pre = ...? 
}
pred checkAllObligsAtFinalDedln[pre: State, post: State] {
    enabledCheckAllObligsAtFinalDedln[pre]

}


pred PDPCAndOrgAgree[s: State] {
    nNotifyAffected in s.notifyStatus[PDPC] & s.notifyStatus[Org]
    nPDPCSaysDoNotNotifyAffected not in s.notifyStatus[PDPC]
}

----------- TO DO: Add event funs! -----------

-- helper pred
pred PDPCRespondsOnThisState[s: State] {
    nNotifyAffected in s.notifyStatus[PDPC] or nPDPCSaysDoNotNotifyAffected in s.notifyStatus[PDPC]
}

pred PDPCWillRespondWithinOneTick {
    // [Simplifying modelling assumption] a 'non-starvation' property of sorts for PDPC: PDPC will always respond to Org's notification within 1 tick, if Org notifies PDPC in one of the first TWO steps
    all s: State - stNDBreach | 
        { 
            nOrgNotifiesPDPC in s.notifyStatus[Org] =>
                    PDPCRespondsToOrgIfOrgHadNotified[s, s.next] 
        }
    // nOrgNotifiesPDPC in (stNDBreach.next).notifyStatus[Org] => PDPCRespondsToOrgIfOrgHadNotified[stNDBreach.next, (stNDBreach.next).next]

    // nOrgNotifiesPDPC in ((stNDBreach.next).next).notifyStatus[Org] => PDPCRespondsToOrgIfOrgHadNotified[(stNDBreach.next).next, ((stNDBreach.next).next).next]
}



pred ifOrgNotifiesPDPCDoesSoWithinFirstThreeSteps { 
    // for well-formedness
    {some s: State | nOrgNotifiesPDPC in s.notifyStatus[Org]} implies
        {
            nOrgNotifiesPDPC in (stNDBreach.next).notifyStatus[Org] or 
            nOrgNotifiesPDPC in ((stNDBreach.next).next).notifyStatus[Org] or
            nOrgNotifiesPDPC in (((stNDBreach.next).next).next).notifyStatus[Org] // to allow for possibility of missing dateline
        } 
}
pred wellformed {
    ifOrgNotifiesPDPCDoesSoWithinFirstThreeSteps
    PDPCWillRespondWithinOneTick

    // don't think we need these after all, given that we can just talk about  obligations that get triggered and persist (and given how that's clearer)
    // OrgNotifyAffectedIsForever
    // PDPCNotifyDecisionIsForever
}

pred checkIfAllDone {

}

pred nextNotLawBroken[s: State] {
    some s.next and stOrgBrokeLaw not in s.next 
}

// for testing
pred toyStutter[pre: State, post: State] {
    pre.notifyStatus = post.notifyStatus
    
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

    // stNDBreach is our initial state
    initNDB[stNDBreach] 
    no sprev: State | sprev.next = stNDBreach
    
    all s: State | {
        some s.next implies {
            orgPotentiallyNotifiesPDPC[s, s.next] or
            postprocessOrgNotifiesPDPC[s, s.next] or
            
            orgPotentiallyNotifiesAffected[s, s.next] or
            postprocessOrgNotifiesAffected[s, s.next] or

            PDPCRespondsToOrgIfOrgHadNotified[s, s.next] or
            postprocessPDPCRespondsToOrg[s, s.next]
            // or
            // toyStutter[s, s.next]
            // or
            // TO DO: Chk that basic infra / state transitions work first before adding in obligation stuff
            // checkAllObligsAtFinalDedln[s, s.next] or
            // stutter[s, s.next]
            }
    }
}



test expect {
    --- tests of specification / model
    wellformedVacuity: { wellformed } is sat
    tracesVacuity: { traces } is sat

    EnablingPredForNotifyingPDPCIsSat: {
        traces
        some {s: State | enabledOrgPotentiallyNotifiesPDPC[s]}
    } for {next is linear} is sat

    PossibleOrgNotifiesPDPC: {
        traces 
        some {s: State | nOrgNotifiesPDPC in s.notifyStatus[Org]}
    }  for 4 State for {next is linear} is sat 

    PossibleOrgNotNotifyPDPC: {
        traces 
        no {s: State | nOrgNotifiesPDPC in s.notifyStatus[Org]}
    }  for 4 State for {next is linear} is sat 

    PossibleOrgNotifiesAffected: {
        traces 
        some {s: State | nNotifyAffected in s.notifyStatus[Org]}
    }  for {next is linear} is sat 

    OrgNotifiesAffectedOnlyAtMostOnce: {
        traces implies #{s: State | nNotifyAffected in s.notifyStatus[Org]} <= 1
    } for 3 State for {next is linear} is theorem
    -- TO DO: check with higher number of states once we fix the stutter transitions

    PossibleOrgNotifyAffectedBeforeNotifyingPDPC: {
        traces
        some disj s1, s2: State | 
            { 
                s2 in s1.^next
                nNotifyAffected in s1.notifyStatus[Org]
                nOrgNotifiesPDPC in s2.notifyStatus[Org]
            }
    } for {next is linear} is sat

    PossibleOrgNotifyAffectedBeforeNOTNotifyingPDPC: {
        traces
        some disj s1, s2: State | 
            { 
                s2 in s1.^next
                nNotifyAffected in s1.notifyStatus[Org]
                nOrgNOTnotifyPDPC in s2.notifyStatus[Org]
            }
    } for {next is linear} is sat

    PossibleOrgNOTNotifyAffectedBeforeNotifyingPDPC: {
        traces
        some disj s1, s2: State | 
            { 
                s2 in s1.^next
                nOrgNOTnotifyAffected in s1.notifyStatus[Org]
                nOrgNotifiesPDPC in s2.notifyStatus[Org]
            }
    } for {next is linear} is sat

    PossibleOrgNOTNotifyAffectedBeforeNOTNotifyingPDPC: {
        traces
        some disj s1, s2: State | 
            { 
                s2 in s1.^next
                nOrgNOTnotifyAffected in s1.notifyStatus[Org]
                nOrgNOTnotifyPDPC in s2.notifyStatus[Org]
            }
    } for {next is linear} is sat


    PDPCWillNotMakeBothNotifications: {
        traces implies #{s: State | nNotifyAffected in s.notifyStatus[PDPC] or nPDPCSaysDoNotNotifyAffected in s.notifyStatus[PDPC] } <= 1      
    } for 3 State for {next is linear} is theorem
    -- TO DO: check with higher number of states once we fix the stutter transitions

    PossibleForPDPCToSayNotify: {
        traces
        some {s: State | nNotifyAffected in s.notifyStatus[PDPC]}
    } for 4 State for {next is linear} is sat
   
    PossibleForPDPCToImposeGagOrder: {
        traces
        some {s: State | nPDPCSaysDoNotNotifyAffected in s.notifyStatus[PDPC]}
    } for 4 State for {next is linear} is sat

    PDPCWillNotRespondToOrgAtSameTimeThatOrgConsidersNotifyingPDPC: {
        traces  
        some s: State | PDPCRespondsToOrgIfOrgHadNotified[s, s.next] and orgPotentiallyNotifiesPDPC[s, s.next]
    } for {next is linear} is unsat

    PDPCWillNotRespondToOrgBeforeOrgConsidersNotifyingPDPC: {
        traces  
        some disj s1, s2: State | 
            {
                s2 in s1.^next
                nNotifyAffected in s1.notifyStatus[PDPC] or nPDPCSaysDoNotNotifyAffected in s1.notifyStatus[PDPC]
                
                nOrgNotifiesPDPC in s2.notifyStatus[Org] or nOrgNOTnotifyPDPC in s2.notifyStatus[Org]
                // this obviously assumes that the org move pred will make one of these two moves
            }
    } for 3 State for {next is linear} is unsat

    PDPCWillAlwaysRespondToOrgIfOrgNotifiesIt:  {
        traces  
        some s1: State | 
            {
                s1 = stNDBreach or s1 = stNDBreach.next 
                nOrgNotifiesPDPC in s1.notifyStatus[Org] 

                
                no {s2: State | s2 in s1.^next and (nNotifyAffected in s2.notifyStatus[PDPC] or nPDPCSaysDoNotNotifyAffected in s2.notifyStatus[PDPC])}
            } 
    } for 4 State for {next is linear} is unsat



    /*TO DO: 
    PDPC will always respond if it's been notified by Org

    */

    --- tests of the legislation / 'system'


}


run { 
     traces
    } for exactly 4 State for {next is linear}

    

// 

// pred traces {
//     init 
//     initialToNotifiableDB
// }

// run {
//     traces
// } for 5 Int for {next is linear}