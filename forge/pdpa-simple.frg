
#lang forge


/*
Legislation: https://sso.agc.gov.sg/Act/PDPA2012?ProvIds=pr3-,pr4-,pr26-,pr26A-,pr26B-,pr26C-,pr26D-


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
one sig NotifyAffected, DoNotNotifyAffected extends WhetherToNotifyAffected {}

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
distingusih between (i) comapny delibereately notifying individual despite receiving prohibition
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
one sig NotifyAffected, DoNotNotifyAffected, OrgNotifyPDPC extends Notification {}
-- strictly speaking, NotifyAffected has two meanings here: for the PDPC, it means 'Org *must* notify affected', whereas for the org, it will be: Org has notified / is now notifying affected

sig State {
    notifyStatus:  pfunc Actor -> Notification,
    -- impt that this be pfunc and not func!
    next: lone State
}

one sig Initial, OrgRecognizesNotifiableDataBreach, OrgViolatesLaw extends State {} 
-- assume the req to notify is NOT waived in virtue of the org taking action to "[render] it unlikely that the notifiable data breach will result in significant harm to the affected individual"

pred init {
    all actr: Actor | no Initial.notifyStatus[actr]
    --- linearity of next is handled by the run statements
}

pred initialToNotifiableDB {
    Initial.next = OrgRecognizesNotifiableDataBreach

    -- frame condition:
    OrgRecognizesNotifiableDataBreach.notifyStatus = Initial.notifyStatus
}


pred OrgRespondsToNDB {

}

pred PDPCRespondsToOrg {

}



run { 
    init 
    initialToNotifiableDB
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


/*abstract sig Event {}
one sig Init, OrgRecognizesNotifiableDataBreach, OrgBrokeLaw extends Event {}
-- ignoring *non* notifiable data breaches since those aren't interesting
 

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