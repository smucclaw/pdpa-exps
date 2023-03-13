This repo contains a Forge specification of the PDPA 'race condition'.

## What is Forge?
Let's begin with the most obvious question you might have: What is Forge?

The short answer is that it's an Alloy-like language that's geared towards pedagogical purposes and rapid prototyping.

For a longer answer, see Tim Nelson's response:
> Forge is designed specifically for teaching. It has features like partial instances, test blocks, and the Sterling visualizer. Alloy has some features that Forge doesn't support, like the `fact` keyword, and somewhat better library support for relations. [...] The solvers are the same.

## How can I run this?

To run the Forge specifications, see https://github.com/tnelson/Forge/wiki/Installation

## The specification

`simplest.frg` contains the specification and two run statements (simulations), while `tests-simplest.frg` contains the tests.

In particular, `simplest.frg` contains the following two run statements:

1.  Find me a state where Org starts notifying affected individuals at the same time as Org notifies PDPC, but where PDPC tells Org that they must not notify affected while Org is in the middle of notifying the affected
2.  Find me a state where both the Org and PDPC are in 'the critical section' --- where an actor is in the critical section iff they are sending a notificatio nof some sort with regards to the affected.


### Modelling assumptions

The most important simplifying, modeling assumptions include:

* PDPC cannot respond to Org at the same time that Org notifies PDPC; there needs to be at least one tick in between.
* PDPC won't just ignore Org's notification and do nothing
* PDPC will always respond to Org's notification within 1 tick

We are also ignoring *non*-notifiable data breaches in this specification, since that's not relevant to the 'race condition'