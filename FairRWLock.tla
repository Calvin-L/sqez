---- MODULE FairRWLock ----

EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Readers,
    Writers

ASSUME ReadersAndWritersDisjoint == Readers \intersect Writers = {}
Clients == Readers \union Writers

VARIABLES
    pc,
    lock_mode,
    lock_count,
    lock_queue

vars == <<pc, lock_mode, lock_count, lock_queue>>

TypeOK ==
    /\ pc \in [Clients -> {"idle", "wait", "sleep", "cs"}]
    /\ lock_mode \in {"idle", "read", "write"}
    /\ lock_count \in Nat
    /\ lock_queue \in Seq(Clients)

Init ==
    /\ pc = [c \in Clients |-> "idle"]
    /\ lock_mode = "idle"
    /\ lock_count = 0
    /\ lock_queue = <<>>

BeginAcquire(c) ==
    /\ pc[c] = "idle"
    /\ lock_queue' = lock_queue \o <<c>>
    /\ pc' = [pc EXCEPT ![c] = "wait"]
    /\ UNCHANGED <<lock_mode, lock_count>>

SafeToEnter(desired_mode) ==
    LET TRANSITION_TABLE ==
        ("idle" :> {"read", "write"}) @@
        ("read" :> {"read"}) @@
        ("write" :> {}) IN
    desired_mode \in TRANSITION_TABLE[lock_mode]

NotifyAll(_pc) ==
    [c \in Clients |-> IF _pc[c] = "sleep" THEN "wait" ELSE _pc[c]]

EnterCS(c) ==
    /\ pc[c] = "wait"
    \* /\ lock_mode \in {"idle", "read"}
    /\ LET desired_mode == IF c \in Writers THEN "write" ELSE "read" IN
       IF lock_queue[1] = c /\ SafeToEnter(desired_mode) THEN
        /\ lock_mode' = desired_mode
        /\ lock_count' = lock_count + 1
        /\ lock_queue' = SubSeq(lock_queue, 2, Len(lock_queue))
        /\ pc' = [(IF desired_mode = "read" THEN NotifyAll(pc) ELSE pc) EXCEPT ![c] = "cs"]
       ELSE
        /\ pc' = [pc EXCEPT ![c] = "sleep"]
        /\ UNCHANGED <<lock_mode, lock_count, lock_queue>>

Release(c) ==
    /\ pc[c] = "cs"
    /\ lock_count' = lock_count - 1
    /\ lock_mode' = IF lock_count' = 0 THEN "idle" ELSE lock_mode
    /\ pc' = [(IF lock_count' = 0 THEN NotifyAll(pc) ELSE pc) EXCEPT ![c] = "idle"]
    /\ UNCHANGED <<lock_queue>>

Next ==
    \/ \E c \in Clients:
        \/ BeginAcquire(c)
        \/ EnterCS(c)
        \/ Release(c)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in Clients: WF_vars(EnterCS(c))
    /\ \A c \in Clients: WF_vars(Release(c))

LockModeCorrect ==
    CASE
        lock_mode = "idle" -> {c \in Clients: pc[c] = "cs"} = {}
        []
        lock_mode = "read" -> {c \in Clients: pc[c] = "cs"} \subseteq Readers
        []
        lock_mode = "write" -> \E w \in Writers: {c \in Clients: pc[c] = "cs"} = {w}

MutualExclusion ==
    \A c \in Clients:
        pc[c] = "cs" => (\A w \in (Writers \ {c}): pc[w] /= "cs")

\* Not quite liveness... but basically: threads should get a chance to enter
\* the critical section ASAP.
ThreadsThatCanEnterCSAreNotAsleep ==
    \A c \in Clients:
        (lock_queue /= <<>> /\ lock_queue[1] = c /\ SafeToEnter(IF c \in Writers THEN "write" ELSE "read")) => pc[c] /= "sleep"

Liveness ==
    \A c \in Clients: pc[c] = "wait" ~> pc[c] = "cs"

====

---- CONFIG FairRWLock ----

SPECIFICATION Spec

CONSTANT Readers = {r1, r2, r3}
CONSTANT Writers = {w1, w2, w3}

INVARIANT TypeOK
INVARIANT LockModeCorrect
INVARIANT MutualExclusion
INVARIANT ThreadsThatCanEnterCSAreNotAsleep
PROPERTY Liveness

====
