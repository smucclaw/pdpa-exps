#lang forge
open "simplest.frg"

test expect {
    /*
    TO DO:
    * Add tests to figure out the greatest lower bound for number of states for tests / runs
    * If Org.durationNotifyAffected = dTwo => If org starts notifying affected at least two states before the end, then org will spend two states notifying affected
    */


    --- Tests of specification / model ----------------------------------------------------------
    wellformedVacuity: { wellformed } is sat
    tracesVacuity: { traces } is sat

    ------- Notification mechanics

    PossibleNoNotificationsOccur: {
        traces
        no {s: State | orgHasNotifiedPDPC[s] or PDPCResponded[s] or orgNotifyAffectedFlagUp[s]}
    } for 5 State for {next is linear} is sat

    EnablingPredForNotifyingPDPCIsSat: {
        traces
        some {s: State | enabledOrgNotifiesPDPC[s]}
    } for {next is linear} is sat

    PossibleOrgNotifiesPDPC: {
        traces 
        some {s: State | s in statesAfterIncl[stNDBreach] and nOrgNotifiesPDPC in s.notifyStatus[Org]}
    }  for 4 State for {next is linear} is sat 

    // This must be at least 4 states for reasons I do not currently understand
    PossibleOrgNotNotifyPDPC: {
        traces 
        no {s: State | s in statesAfterIncl[stNDBreach] and orgHasNotifiedPDPC[s]}
    }  for 5 State for {next is linear} is sat 
 

    PossibleOrgNotifiesAffected: {
        traces 
        some {s: State | s in statesAfterIncl[stNDBreach] and nNotifyAffected in s.notifyStatus[Org]}
    }  for {next is linear} is sat 

    PossibleOrgNotifyBothAffectedAndPDPCOnSameState: {
        traces 
        some {s: State | nOrgNotifiesPDPC in s.notifyStatus[Org] and nNotifyAffected in s.notifyStatus[Org]}
    }  for {next is linear} is sat 

    PossibleOrgNotifyAffectedBeforeNotifyingPDPC: {
        traces
        some disj s1, s2: State | 
            { 
                s1 in statesAfterIncl[stNDBreach]
                s2 in s1.^next
                nNotifyAffected in s1.notifyStatus[Org]
                nOrgNotifiesPDPC in s2.notifyStatus[Org]
            }
    } for {next is linear} is sat

    PossibleOrgNotifyAffectedButNeverNotifyPDPC: {
        traces
        some s: State | 
            { 
                s in statesAfterIncl[stNDBreach]                
                nNotifyAffected in s.notifyStatus[Org]
            }
        no {s: State | s in statesAfterIncl[stNDBreach] and orgHasNotifiedPDPC[s]}
    } for {next is linear} is sat


    PossibleOrgNotifyPDPCButNeverNotifyAffected: {
        traces
        some s: State | 
            { 
                s in statesAfterIncl[stNDBreach]   
                orgHasNotifiedPDPC[s] 
            }
        no {s: State | s in statesAfterIncl[stNDBreach] and nNotifyAffected in s.notifyStatus[Org]}
    } for {next is linear} is sat

    PossibleForPDPCToSayNotify: {
        traces
        some {s: State | s in statesAfterIncl[stNDBreach] and nNotifyAffected in s.notifyStatus[PDPC]}
    } for 4 State for {next is linear} is sat
   
    PossibleForPDPCToImposeGagOrder: {
        traces
        some {s: State | s in statesAfterIncl[stNDBreach] and nPDPCSaysDoNotNotifyAffected in s.notifyStatus[PDPC]}
    } for 4 State for {next is linear} is sat

    PDPCWillNotRespondToOrgAtSameTimeThatOrgConsidersNotifyingPDPC: {
        traces  
        some s: State | 
        {
            s in statesAfterIncl[stNDBreach]
            PDPCRespondsToOrgIfOrgHadNotified[s, s.next]  
            orgNotifiesPDPC[s, s.next]
        }
    } for {next is linear} is unsat

    OrgNotifyingPDPCIsDueToMovePred: {
        traces
        some s: State |
            { 
                s in statesAfterIncl[stNDBreach]
                nOrgNotifiesPDPC in (s.next).notifyStatus[Org]
                not orgNotifiesPDPC[s, s.next]
            }
    } for 4 State for {next is linear} is unsat

    OrgNotifyingAffectedIsDueToMovePred: {
        traces
        some s: State |
            { 
                s in statesAfterIncl[stNDBreach]
                no preStatesWithPriorNotifn[Org, nNotifyAffected, s]
                nNotifyAffected in (s.next).notifyStatus[Org] 

                not orgStartsNotifyingAffected[s, s.next]
            }
    } for 4 State for {next is linear} is unsat

    // nNotifyAffected in s.notifyStatus[Org]
    OrgStartsNotifyingAffectedPredRunsOnlyAtMostOnce: {
        traces implies #{s: statesAfterIncl[stNDBreach] | orgStartsNotifyingAffected[s, s.next]} <= 1
    } for 5 State for {next is linear} is theorem
    -- TO DO: check with higher number of states once we fix the stutter transitions

    OrgNotifsToAffectedOnlyTwoStatesMax: {
        traces implies 
            #{s: statesAfterIncl[stNDBreach] | nNotifyAffected in s.notifyStatus[Org]} <= 2
    } for 5 State for {next is linear} is theorem

    // clean up occurs once, max (max, b/c org may not notify PDPC)
    CleanupOrgNotifiesPDPCOnceMax: {
        traces implies 
            #{s: State | 
                s in statesAfterIncl[stNDBreach] and
                some s.next and
                cleanupOrgNotifiesPDPC[s, s.next]} <= 1
    } for 5 State for {next is linear} is theorem

    OrgNotifsToPDPCOnlyOnOneStateMax: {
        traces implies 
            #{s: State | s in statesAfterIncl[stNDBreach] and
                nOrgNotifiesPDPC in s.notifyStatus[Org]} <= 1
    } for 5 State for {next is linear} is theorem

    PDPCWillNotMakeBothTypesOfNotificationOnSameState: {
        traces implies 
            no {s: State | nNotifyAffected + nPDPCSaysDoNotNotifyAffected in s.notifyStatus[PDPC]}
    }  for 5 State for {next is linear} is theorem

    PDPCNotifsOnlyOnOneStateMax: {
        traces implies 
            #{s: State | nNotifyAffected in s.notifyStatus[PDPC] or 
                nPDPCSaysDoNotNotifyAffected in s.notifyStatus[PDPC]} <= 1
    } for 5 State for {next is linear} is theorem
 
    // Suppose PDPC tells Org not to notify affected. It's still possible for Org to subsequently notify affected.
    OrgCanStillNotifyEvenAfterPDPCSaysNotTo: {
        traces
        some s: State |
            { 
                s in statesAfterIncl[stNDBreach]
                nPDPCSaysDoNotNotifyAffected in s.notifyStatus[PDPC]
                some s.next
                nNotifyAffected in (s.next).notifyStatus[Org] 
            }
    } for 4 State for {next is linear} is sat


    PDPCWillNotRespondToOrgBeforeOrgConsidersNotifyingPDPC: {
        traces  
        some disj s1, s2: State | 
            {
                s1 in statesAfterIncl[stNDBreach]   
                s2 in s1.^next
                nNotifyAffected in s1.notifyStatus[PDPC] or nPDPCSaysDoNotNotifyAffected in s1.notifyStatus[PDPC]
                
                nOrgNotifiesPDPC in s2.notifyStatus[Org] 
                // this obviously assumes that the org move pred will make one of these two moves
            }
    } for 3 State for {next is linear} is unsat

    PDPCWillAlwaysRespondToOrgIfOrgNotifiesIt:  {
        traces implies
            {
                orgHasNotifiedPDPC[stNDBreach.next] 
                => some {s2: State | s2 in (stNDBreach.next).^next and 
                                    (nNotifyAffected in s2.notifyStatus[PDPC] or nPDPCSaysDoNotNotifyAffected in s2.notifyStatus[PDPC])}
            }
    } for exactly 4 State for {next is linear} is theorem

    // It's possible for Org to notify PDPC and for PDPC to __subsequently__ say to notify while Org is IN MIDDLE OF notifying affected
    PDPCCanSayNotToNotifyEvenAfterOrgHasNotifiedAffected: {
        traces
        some s: State |
            {   
                orgHasNotifiedPDPC[s]
                // org notifies pdpc at s

                orgNotifyAffectedFlagUp[s] and orgNotifyAffectedFlagUp[s.next] 
                // org's notifying of affected takes place over s and s.next

                nNotifyAffected in (s.next).notifyStatus[PDPC]
                // pdpc says to notify on s.next
            }
    } for 5 State for {next is linear} is sat


    ----- 'the race condition' -----------------------

    // It's possible for Org to notify PDPC and for PDPC to __subsequently__ say NOT to notify while Org is IN MIDDLE OF notifying affected
    PDPCCanSayNotToNotifyEvenAfterOrgHasNotifiedAffected: {
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
    } for 5 State for {next is linear} is sat


    // critical section version variant query; this is more permissive b/c this also includes situations where Org and PDPC agree that affected should be notified
    PDPCAndOrgAreInCriticalSectionAtSameTime: {
        traces
        some s: State | Org + PDPC in inCS[s]
    } for 4 State for {next is linear} is sat



    ------- Obligation mechanics

    /*TO DO: 
    1. Once an obligation is introduced / activated, it will stay in the activeObligs field till it gets checked / till we get to the associated deadln state (in a more complicated specification, this would be a disjunction: e.g., could also be till it gets waived, or...)
    2. Obligations are checked only on the states we want to check them at 
    3. When obligations are violated, we transit to the associated breach state
    */

    --- tests of the legislation / 'system'
}
