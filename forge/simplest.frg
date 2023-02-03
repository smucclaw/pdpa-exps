#lang forge

option verbose 2

abstract sig Duration {}
one sig dOne, dTwo extends Duration {}

abstract sig Actor {}
one sig PDPC extends Actor {}
one sig Org extends Actor {
    durationNotifyAffected: one Duration
}
/* Modelling choices to think abt here: 

* I'm currently folding in Affected / Individual into the states instead of treating it as a separate actor to whom messages can be passed, but is that simplification OK?
* Is PDPC really on same ontological level as Org? Might make more sense to have separate sig for PDPC
* Might it be better to fold the PDPC stuff into the states?
*/

abstract sig Notification {}

one sig nNotifyAffected, nPDPCSaysDoNotNotifyAffected extends Notification {}
one sig nOrgNotifiesPDPC extends Notification {}
-- strictly speaking, nNotifyAffected has two meanings here: for the PDPC, it means 'Org *must* notify affected', whereas for the org, it will be: Org has notified / is now notifying affected


/*
abstract sig Event {}
one sig InitNotifiableDataBreach, Stutter, OrgBreaksLaw, AllIsGood extends Event {}

Not sure if shld use Event or State for this --- look more closely at the tutorial + try to get better sense for how visualizer would handle this!
*/
// Important modelling invariant: put all state-related stuff in this sig! That way will be clear what frame conditions etc to use 
sig State {
    notifyStatus: set Actor -> Notification,
    -- impt that this be pfunc and not func!
    -- what notification(s) / notification decision(s) Actor has made

    next: lone State
}

one sig stNDBreach extends State {}
-- ignoring *non* notifiable data breaches since those aren't interesting


------------------------ UTILITY FUNCS ---------------------------------------------------
// could make an org / pdpc notification sig...
fun notifs[actr: Actor]: set Notification {
    actr = Org => (nNotifyAffected + nOrgNotifiesPDPC) else nNotifyAffected + nPDPCSaysDoNotNotifyAffected
}

// set of actors that are 'in the critical section' in that state; i.e., that are sending notification of some sort re the affected
fun inCS[s: State]: set Actor {
    {actr: Actor | s.notifyStatus[actr] in nNotifyAffected + nPDPCSaysDoNotNotifyAffected}
}

fun statesBefore[s: State]: set State {
    s.^(~next)
}

fun statesAfterIncl[s: State]: set State {
    s + s.^next
}

-- states that r bet s1 and s2, not inclusive
fun between[s1: State, s2: State]: set State {
    s1.^next & statesBefore[s2]
}

fun betweenInclLeft[s1: State, s2: State]: set State {
    ( s1.^next & s2.^(~next) ) + s1
}

fun betweenInclBoth[s1: State, s2: State]: set State {
    ( s1.^next & s2.^(~next) ) + s1 + s2
}


-- assume the req to notify is NOT waived in virtue of the org taking action to "[render] it unlikely that the notifiable data breach will result in significant harm to the affected individual"

------------ PREDS -------------------------------------------------
// linearity of next is handled by the run statements

pred initNDBWhereNotifyAffectedInstantaneous[s: State] {
    all actr: Actor | no s.notifyStatus[actr]
    Org.durationNotifyAffected = dOne    
}
pred initNDB[s: State] {
    all actr: Actor | no s.notifyStatus[actr]
    Org.durationNotifyAffected = dTwo    
}


/* TO DO
1. Look into whether shld add enabledOrgDoesNotNotifyAffected and enabledOrgDoesNotNotifyPDPC. I want to say no b/c those woudl be true even if we do want to stutter, but not sure
*/
pred someSubstantiveTransEnabled[pre: State] {
    -- org notification transitions
    enabledOrgStartsNotifyingAffected[pre] or
    enabledOrgNotifAffectedContinues[pre] or
    // or enabledOrgDoesNotNotifyAffected[pre] or

    enabledOrgNotifiesPDPC[pre] or 
    // enabledOrgDoesNotNotifyPDPC[pre] or
    
    enabledCleanupOrgNotifPDPC[pre] or
    enabledCleanupOrgNotifiesAffected[pre] or

    -- pdpc notification transitions
    enabledPDPCRespondsToOrg[pre] or
    enabledCleanupPDPCRespondsToOrg[pre] 
}
// 
/*
TO DO: Chk / refactor*/
pred stutter[pre: State, post: State] {
    not someSubstantiveTransEnabled[pre]

    pre.notifyStatus = post.notifyStatus
    pre = stNDBreach <=> post = stNDBreach
}

/*
26D.—(1)  Where an organisation assesses, in accordance with section 26C, that a data breach is a notifiable data breach, the organisation must notify the Commission as soon as is practicable, but in any case no later than 3 calendar days after the day the organisation makes that assessment

(2)  Subject to subsections (5), (6) and (7), on or after notifying the Commission under subsection (1), the organisation must also notify each affected individual affected by a notifiable data breach mentioned in section 26B(1)(a) in any manner that is reasonable in the circumstances.

(6)  An organisation must not notify any affected individual in accordance with subsection (2) if —
(a)	a prescribed law enforcement agency so instructs; or
(b)	the Commission so directs.
*/

-- helper fn
fun preStatesWithPriorNotifn (actr: Actor, notifn: Notification, pre: State): set State {
    {s: (statesBefore[pre] + pre) | notifn in s.notifyStatus[actr]}
}

-- IMPT: orgNotifiesPDPC and orgStartsNotifyingAffected are NOT 'happy path / what a law-abiding Org would do' preds. 
-- Think of them instead as 'what it minimally takes for the state transitions to be wellformed / for the specification to work' preds

// pred enabledOrgDoesNotNotifyPDPC[pre: State] {
//     not (some pre.next and orgNotifiesPDPC[pre, pre.next])
// }
pred orgDoesNotNotifyPDPC[pre: State, post: State] {
    // enabledOrgDoesNotNotifyPDPC[pre]
    nOrgNotifiesPDPC not in post.notifyStatus[Org]
}

pred enabledOrgNotifiesPDPC[pre: State] {
    // 1. Org has not made this move (potentially notifying PDPC) in pre or before
    no preStatesWithPriorNotifn[Org, nOrgNotifiesPDPC, pre]
    // no preStatesWithPriorNotifn[Org, nOrgNOTnotifyPDPC, pre]

    // 3. Require that PDPC not have somehow told Org to notify or not notify ahead of time
    // This rules out, e.g., the edge case where PDPC somehow pre-emptively tells the org not to notify affected people about any possible issues arising from some likely but not yet confirmed notifiable data breach
    no {s: State | s in (statesBefore[pre] + pre) and some s.notifyStatus[PDPC]}
}

pred orgNotifiesPDPC[pre: State, post: State] {
    enabledOrgNotifiesPDPC[pre]
    
    -- ACTIONS
    nOrgNotifiesPDPC in post.notifyStatus[Org]
    // nOrgNOTnotifyPDPC in post.notifyStatus[Org]
    // We don't necessarily want to preserve what was in pre, b/c may want to clean up / remove notification(s) from before
    // note tt we want it to be possible for org to inform affected at same time as they inform pdpc

    // 2. mandate cleanup
    some post.next => cleanupOrgNotifiesPDPC[post, post.next]

    --- other frame conditions 
    no post.notifyStatus[PDPC]
    // Modelling assumption: PDPC cannot respond to Org at the same time that Org notifies PDPC; there needs to be at least one tick in between. (And we assumed in the enabling / preconditions that PDPC hadn't told Org anything before post.)
}


pred orgHasNotifiedPDPC[s: State] {
    nOrgNotifiesPDPC in s.notifyStatus[Org]
}
pred enabledCleanupOrgNotifPDPC[pre: State] {
    orgHasNotifiedPDPC[pre]
}
pred cleanupOrgNotifiesPDPC[pre: State, post: State] {
    enabledCleanupOrgNotifPDPC[pre]

    // Make sure the PDPC related notification flags not in post
    nOrgNotifiesPDPC not in post.notifyStatus[Org]
}


pred enabledOrgStartsNotifyingAffected[pre: State] {
    // 1. First time Org considering whether to notify affected / making this move wrt affected
    no preStatesWithPriorNotifn[Org, nNotifyAffected, pre]
    // no preStatesWithPriorNotifn[Org, nOrgNOTnotifyAffected, pre]

    /* NOT requiring tt 
        (i) Org have informed PDPC before this, 
        or 
        (ii)  PDPC not have told Org not to notify
    because orgStartsNotifyingAffected isn't supposed to be a 'happy path only' predicate 
    orgStartsNotifyingAffected is more like a 'what it takes for the state transition to be well-formed' predicate 
    */
}
pred orgStartsNotifyingAffected[pre: State, post: State] {
    enabledOrgStartsNotifyingAffected[pre]

    -- ACTIONS
    Org.durationNotifyAffected = dOne => {
        nNotifyAffected in post.notifyStatus[Org]
        some post.next => cleanupOrgNotifiesAffected[post, post.next]
    }
    Org.durationNotifyAffected = dTwo => {
        nNotifyAffected in post.notifyStatus[Org]
        some post.next => nNotifyAffected in (post.next).notifyStatus[Org]
        some (post.next).next => cleanupOrgNotifiesAffected[post.next, (post.next).next] 
    }

    --- other frame conditions 
    // Do NOT say that post.notifyStatus[PDPC] must = pre's!
}

pred orgNotifyAffectedFlagUp[s: State] {
    nNotifyAffected in s.notifyStatus[Org]
}
pred enabledOrgNotifAffectedContinues[pre: State] {
    orgNotifyAffectedFlagUp[pre]
}
pred orgNotifAffectedContinues[pre: State, post: State] {
    enabledOrgNotifAffectedContinues[pre]

    orgNotifyAffectedFlagUp[post]
}


pred enabledOrgDoesNotNotifyAffected[pre: State] {
    not orgStartsNotifyingAffected[pre.~next, pre]
}
pred orgDoesNotNotifyAffected[pre: State, post: State] {
    enabledOrgDoesNotNotifyAffected[pre]

    nNotifyAffected not in post.notifyStatus[Org]   
}


pred enabledCleanupOrgNotifiesAffected[pre: State] {
    orgNotifyAffectedFlagUp[pre]   
}
pred cleanupOrgNotifiesAffected[pre: State, post: State] {
    enabledCleanupOrgNotifiesAffected[pre]

    nNotifyAffected not in post.notifyStatus[Org]
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

    post.notifyStatus[PDPC] in nNotifyAffected + nPDPCSaysDoNotNotifyAffected   
    // Simplifying modelling assumption: PDPC won't just ignore Org's notification and do nothing

    some post.next => cleanupPDPCRespondsToOrg[post, post.next]
}

pred PDPCResponded[s: State] {
    nNotifyAffected in s.notifyStatus[PDPC] or nPDPCSaysDoNotNotifyAffected in s.notifyStatus[PDPC]
}
pred enabledCleanupPDPCRespondsToOrg[pre: State] {
    PDPCResponded[pre]
}
pred cleanupPDPCRespondsToOrg[pre: State, post: State] {
    enabledCleanupPDPCRespondsToOrg[pre]

    nNotifyAffected not in post.notifyStatus[PDPC] 
    nPDPCSaysDoNotNotifyAffected not in post.notifyStatus[PDPC]
}



pred PDPCAndOrgAgree[s: State] {
    nNotifyAffected in s.notifyStatus[PDPC] & s.notifyStatus[Org]
    nPDPCSaysDoNotNotifyAffected not in s.notifyStatus[PDPC]
}


pred PDPCNotifsImpliesPDPCMoved {
    all s: statesAfterIncl[stNDBreach] |  
        {
            some s.next 
            nNotifyAffected in (s.next).notifyStatus[PDPC] or nPDPCSaysDoNotNotifyAffected in (s.next).notifyStatus[PDPC]
        } implies
            {
                PDPCRespondsToOrgIfOrgHadNotified[s, s.next]
            }
}

pred orgNotifsImpliesOrgMoved {

    all s: statesAfterIncl[stNDBreach] |  
        {
            some s.next 
            nOrgNotifiesPDPC in (s.next).notifyStatus[Org] 
        } implies orgNotifiesPDPC[s, s.next]

    all s: statesAfterIncl[stNDBreach] |  
        {
            some s.next 
            nOrgNotifiesPDPC not in (s.next).notifyStatus[Org] 
        } implies orgDoesNotNotifyPDPC[s, s.next]

    // if org notifies affected flag up in post but not in pre, it's cos of orgStartsNotifyingAffected
    all s: statesAfterIncl[stNDBreach] |  
        {
            some s.next 
            nNotifyAffected not in s.notifyStatus[Org]
            nNotifyAffected in (s.next).notifyStatus[Org]
        } implies orgStartsNotifyingAffected[s, s.next]
    // if org notifies affected flag up in pre and post, it's cos of orgStartsNotifyingAffected
    all s: statesAfterIncl[stNDBreach] |  
        {
            some s.next 
            nNotifyAffected in s.notifyStatus[Org]
            nNotifyAffected in (s.next).notifyStatus[Org]
        } implies orgNotifAffectedContinues[s, s.next]


    all s: statesAfterIncl[stNDBreach] |  
        {
            some s.next 
            nNotifyAffected not in (s.next).notifyStatus[Org] 
        } implies orgDoesNotNotifyAffected[s, s.next]

}


pred PDPCWillRespondWithinOneTick {
    // [Simplifying modelling assumption] a 'non-starvation' property of sorts for PDPC: PDPC will always respond to Org's notification within 1 tick
    all s: statesAfterIncl[stNDBreach] | orgHasNotifiedPDPC[s] => PDPCRespondsToOrgIfOrgHadNotified[s, s.next] 
}

pred ifOrgNotifiesPDPCOrgDoesSoWithinFirstThreeSteps { 
    // for well-formedness / modelling convenience; in particular, to not have traces that are unnecessarily long
    // Within first *3* steps presupposes that deadline is in 2 steps (i.e., is at ((stNDBreach.next).next )
    (some {s: State | s in (stNDBreach + stNDBreach.^next) and orgHasNotifiedPDPC[s]}) implies
        {
            orgHasNotifiedPDPC[stNDBreach.next] or 
            orgHasNotifiedPDPC[((stNDBreach.next).next)] or 
            orgHasNotifiedPDPC[(((stNDBreach.next).next).next)]
            // to allow for possibility of notifying PDPC but missing dateline (i.e., notifying *only after* the deadln)
        } 
}

pred notifStatusesCorrespondToActorNotifs {
    all s: statesAfterIncl[stNDBreach] | s.notifyStatus[Org] in notifs[Org] and s.notifyStatus[PDPC] in notifs[PDPC]
}


pred wellformed {
    -- notification mechanics wellformed
    notifStatusesCorrespondToActorNotifs
    orgNotifsImpliesOrgMoved
    PDPCNotifsImpliesPDPCMoved

    ifOrgNotifiesPDPCOrgDoesSoWithinFirstThreeSteps
    PDPCWillRespondWithinOneTick
}


// pred enabledTransitn[pre: State] { 
//     // what is required for a substantive transition to occur
//     not finis[pre]
// }
pred transitn[pre: State, post: State] {
    // enabledTransitn[pre]
    
    orgNotifiesPDPC[pre, post] or
    orgDoesNotNotifyPDPC[pre, post] or

    orgStartsNotifyingAffected[pre, post] or
    (Org.durationNotifyAffected = dTwo => orgNotifAffectedContinues[pre, post]) or
    orgDoesNotNotifyAffected[pre, post] or
    
    PDPCRespondsToOrgIfOrgHadNotified[pre, post]
    
    // to think abt: is there any value to having states that do nothing but clean up some prev event?
    // cleanupOrgNotifiesAffected[pre, post] or
    // cleanupPDPCRespondsToOrg[pre, post] or
    // cleanupOrgNotifiesPDPC[pre, post] or
}
pred traces {
    wellformed

    // stNDBreach is our initial state
    initNDB[stNDBreach] 
    no sprev: State | sprev.next = stNDBreach
    
    all s: State | {
        some s.next implies { transitn[s, s.next]  or stutter[s, s.next] }
    }
}

// run {
//     traces
//     // some
// } for exactly 5 State for {next is linear}

-- run of the 'race condition', formulated in a somewhat low-level way
// 'Is there a state where org starts notifying affected at same time as org notifies pdpc, but where pdpc tells org that they must not notify affected while org is in the middle of notifying the affected?'
run {
    traces
    some s: State |
        {   
            orgHasNotifiedPDPC[s]
            // org notifies pdpc at s

            orgNotifyAffectedFlagUp[s] and orgNotifyAffectedFlagUp[s.next] 
            // org's notifying of affected takes place over s and s.next

            nPDPCSaysDoNotNotifyAffected in (s.next).notifyStatus[PDPC]
            // pdpc says not to notify on s.next
        }
} for 5 State for {next is linear} 




// TO DO: Add the in cs stuff -- both runs and tests
