---- MODULE Phaser ----

CONSTANTS
    Readers,
    Writers

ASSUME ReadersAndWritersDisjoint == Readers \intersect Writers = {}
Clients == Readers \union Writers

VARIABLES
    active_clients,
    pending_clients

vars == <<active_clients, pending_clients>>

TypeOK ==
    /\ active_clients \subseteq Clients
    /\ pending_clients \subseteq Clients

Init ==
    /\ active_clients = {}
    /\ pending_clients = {}

Begin(c) ==
    /\ c \notin active_clients
    /\ c \notin pending_clients
    /\ pending_clients' = pending_clients \union {c}
    /\ UNCHANGED active_clients

EnterReadPhase(rs) ==
    /\ active_clients' = rs
    /\ pending_clients' = pending_clients \ rs

EnterWritePhase(w) ==
    /\ active_clients' = {w}
    /\ pending_clients' = pending_clients \ {w}

Finish(c) ==
    /\ c \in active_clients
    /\ active_clients' = active_clients \ {c}
    /\ UNCHANGED pending_clients

Next ==
    \/ \E c \in Clients: Begin(c) \/ Finish(c)
    \/ \E rs \in SUBSET Readers: EnterReadPhase(rs)
    \/ \E w \in Writers: EnterWritePhase(w)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in Clients: WF_vars(Finish(c))
    /\ \A r \in Readers: SF_vars(\E rs \in SUBSET Readers: r \in pending_clients /\ EnterReadPhase(rs \union {r}))
    /\ \A w \in Writers: SF_vars(w \in pending_clients /\ EnterWritePhase(w))

Safety == \A w \in Writers: w \in active_clients => active_clients = {w}
Liveness == \A c \in Clients: (c \in pending_clients) ~> (c \in active_clients)

====

---- CONFIG Phaser ----

SPECIFICATION Spec

CONSTANT Readers = {r1, r2, r3}
CONSTANT Writers = {w1, w2, w3}

INVARIANT TypeOK
INVARIANT Safety
PROPERTY Liveness

====
