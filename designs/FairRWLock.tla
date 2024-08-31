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
    active_clients,
    pending_readers,
    pending_writers

vars == <<pc, lock_mode, active_clients, pending_readers, pending_writers>>

TypeOK ==
    /\ pc \in [Clients -> {"idle", "wait", "sleep", "cs"}]
    /\ lock_mode \in {"idle", "read", "write"}
    /\ active_clients \subseteq Clients
    /\ pending_readers \subseteq Readers
    /\ pending_writers \in Seq(Writers)

DesiredMode(c) == IF c \in Writers THEN "write" ELSE "read"

Init ==
    /\ pc = [c \in Clients |-> "idle"]
    /\ lock_mode = "idle"
    /\ active_clients = {}
    /\ pending_readers = {}
    /\ pending_writers = <<>>

FastAcquire(c) ==
    /\ pc[c] = "idle"
    /\ lock_mode = "idle"
    /\ pending_readers = {}
    /\ pending_writers = <<>>
    /\ lock_mode' = DesiredMode(c)
    /\ pc' = [pc EXCEPT ![c] = "cs"]
    /\ UNCHANGED <<active_clients, pending_writers, pending_readers>>

SlowAcquire(c) ==
    /\ pc[c] = "idle"
    /\ IF c \in Readers THEN
        /\ pending_readers' = pending_readers \union {c}
        /\ UNCHANGED pending_writers
       ELSE
        /\ pending_writers' = pending_writers \o <<c>>
        /\ UNCHANGED pending_readers
    /\ pc' = [pc EXCEPT ![c] = "wait"]
    /\ UNCHANGED <<lock_mode, active_clients>>

NotifyAll(_pc) ==
    [c \in Clients |-> IF _pc[c] = "sleep" THEN "wait" ELSE _pc[c]]

EnterCS(c) ==
    /\ pc[c] = "wait"
    /\ IF lock_mode = "idle" THEN
        /\ IF DesiredMode(c) = "write" THEN
            /\ IF pending_writers[1] = c THEN
                /\ pending_writers' = SubSeq(pending_writers, 2, Len(pending_writers))
                /\ lock_mode' = DesiredMode(c)
                /\ pc' = [pc EXCEPT ![c] = "cs"]
               ELSE
                /\ pc' = [pc EXCEPT ![c] = "sleep"]
                /\ UNCHANGED <<lock_mode, pending_writers>>
            /\ UNCHANGED <<active_clients, pending_readers>>
           ELSE
            /\ active_clients' = active_clients \union pending_readers
            /\ pending_readers' = {}
            /\ lock_mode' = "read"
            /\ pc' = [pc EXCEPT ![c] = "cs"]
            /\ UNCHANGED pending_writers
       ELSE
        /\ IF c \in active_clients THEN
            /\ pc' = [pc EXCEPT ![c] = "cs"]
           ELSE
            /\ pc' = [pc EXCEPT ![c] = "sleep"]
        /\ UNCHANGED <<active_clients, lock_mode, pending_readers, pending_writers>>

Release(c) ==
    /\ pc[c] = "cs"
    /\ LET new_active_clients == active_clients \ {c} IN
       IF new_active_clients = {} THEN
        /\ IF lock_mode = "write" THEN
            /\ IF pending_readers /= {} THEN
                /\ lock_mode' = "read"
                /\ active_clients' = new_active_clients \union pending_readers
                /\ pending_readers' = {}
               ELSE
                /\ lock_mode' = "idle"
                /\ active_clients' = new_active_clients
                /\ UNCHANGED pending_readers
            /\ UNCHANGED pending_writers
           ELSE
            /\ IF pending_writers /= <<>> THEN
                /\ lock_mode' = "write"
                /\ active_clients' = new_active_clients \union {pending_writers[1]}
                /\ pending_writers' = SubSeq(pending_writers, 2, Len(pending_writers))
               ELSE
                /\ lock_mode' = "idle"
                /\ active_clients' = new_active_clients
                /\ UNCHANGED pending_writers
            /\ UNCHANGED pending_readers
        /\ pc' = [NotifyAll(pc) EXCEPT ![c] = "idle"]
       ELSE
        /\ active_clients' = new_active_clients
        /\ pc' = [pc EXCEPT ![c] = "idle"]
        /\ UNCHANGED <<lock_mode, pending_readers, pending_writers>>

Next ==
    \/ \E c \in Clients:
        \/ FastAcquire(c)
        \/ SlowAcquire(c)
        \/ EnterCS(c)
        \/ Release(c)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in Clients: WF_vars(EnterCS(c))
    /\ \A c \in Clients: WF_vars(Release(c))

WaitingReadersArePendingOrActive ==
    \A r \in Readers:
        pc[r] \in {"wait", "sleep"} => r \in pending_readers \/ r \in active_clients

ActiveClientsCorrect ==
    \/ active_clients = {} /\ (\E cc \in Clients: {c \in Clients: pc[c] = "cs"} = {cc})
    \/ {c \in Clients: pc[c] = "cs"} \subseteq active_clients

TrueActiveClients == active_clients \union {c \in Clients: pc[c] = "cs"}

LockModeCorrect ==
    CASE
        lock_mode = "idle" -> TrueActiveClients = {}
        []
        lock_mode = "read" -> TrueActiveClients \subseteq Readers
        []
        lock_mode = "write" -> \E w \in Writers: TrueActiveClients = {w}

MutualExclusion ==
    \A c \in Clients:
        pc[c] = "cs" => (\A w \in (Writers \ {c}): pc[w] /= "cs")

Liveness ==
    \A c \in Clients: pc[c] \in {"wait", "sleep"} ~> pc[c] = "cs"

P == INSTANCE Phaser WITH
    pending_clients <- {c \in Clients: pc[c] \in {"wait", "sleep"}} \ TrueActiveClients,
    active_clients <- TrueActiveClients

PSpec == P!Spec

====

---- CONFIG FairRWLock ----

SPECIFICATION Spec

CONSTANT Readers = {r1, r2, r3}
CONSTANT Writers = {w1, w2, w3}

INVARIANT TypeOK
INVARIANT WaitingReadersArePendingOrActive
INVARIANT ActiveClientsCorrect
INVARIANT LockModeCorrect
INVARIANT MutualExclusion
PROPERTY Liveness
PROPERTY PSpec

====
