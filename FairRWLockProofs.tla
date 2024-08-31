---- MODULE FairRWLockProofs ----

EXTENDS FairRWLock, TLAPS

THEOREM TypeCorrect == Spec => []TypeOK
    <1>a. Init => TypeOK BY DEF Init, TypeOK
    <1>b. (TypeOK /\ [Next]_vars) => TypeOK'
        <2>a. CASE \E c \in Clients: FastAcquire(c) BY <2>a DEF FastAcquire, TypeOK, DesiredMode
        <2>b. CASE \E c \in Clients: SlowAcquire(c) BY <2>b DEF SlowAcquire, TypeOK, Clients
        <2>c. CASE \E c \in Clients: EnterCS(c) BY <2>c DEF EnterCS, TypeOK, DesiredMode, Clients
        <2>d. CASE \E c \in Clients: Release(c) BY <2>d DEF Release, TypeOK, NotifyAll, Clients
        <2>e. CASE UNCHANGED vars BY <2>e DEF vars, TypeOK
        <2> QED BY <2>a, <2>b, <2>c, <2>d, <2>e DEF Next
    <1> QED BY PTL, <1>a, <1>b DEF Spec

LEMMA WaitingReadersCorrect == Spec => []WaitingReadersArePendingOrActive
    <1> SUFFICES ASSUME []TypeOK PROVE Spec => []WaitingReadersArePendingOrActive BY TypeCorrect
    <1>a. Init => WaitingReadersArePendingOrActive BY DEF Init, WaitingReadersArePendingOrActive, Clients
    <1>b. (WaitingReadersArePendingOrActive /\ [Next]_vars) => WaitingReadersArePendingOrActive'
        <2> pc \in [Clients -> {"idle", "wait", "sleep", "cs"}] BY PTL DEF TypeOK
        <2>a. CASE \E c \in Clients: FastAcquire(c) BY <2>a DEF FastAcquire, WaitingReadersArePendingOrActive, DesiredMode, Clients
        <2>b. CASE \E c \in Clients: SlowAcquire(c) BY <2>b DEF SlowAcquire, WaitingReadersArePendingOrActive, Clients
        <2>c. CASE \E c \in Clients: EnterCS(c) BY <2>c DEF EnterCS, WaitingReadersArePendingOrActive, DesiredMode, Clients
        <2>d. CASE \E c \in Clients: Release(c) BY <2>d DEF Release, WaitingReadersArePendingOrActive, NotifyAll, Clients
        <2>e. CASE UNCHANGED vars BY <2>e DEF vars, WaitingReadersArePendingOrActive
        <2> QED BY <2>a, <2>b, <2>c, <2>d, <2>e DEF Next
    <1> QED BY PTL, <1>a, <1>b DEF Spec

LEMMA LockModeCorrect_implies_MutualExclusion == ASSUME LockModeCorrect, TypeOK PROVE MutualExclusion
    <1> SUFFICES ASSUME LockModeCorrect, TypeOK, NEW c \in Clients, pc[c] = "cs", NEW w \in (Writers \ {c}) PROVE pc[w] /= "cs" BY DEF MutualExclusion
    <1>a. CASE lock_mode = "idle" BY <1>a DEF LockModeCorrect, TrueActiveClients
    <1>b. CASE lock_mode = "read" BY <1>b, ReadersAndWritersDisjoint DEF LockModeCorrect, TrueActiveClients, Clients
    <1>c. CASE lock_mode = "write" BY <1>c DEF LockModeCorrect, TrueActiveClients, Clients
    <1> QED BY <1>a, <1>b, <1>c DEF TypeOK

THEOREM Safe == Spec => []MutualExclusion
    <1> SUFFICES ASSUME []TypeOK, []WaitingReadersArePendingOrActive PROVE Spec => []MutualExclusion BY TypeCorrect, WaitingReadersCorrect
    <1> SUFFICES Spec => [](LockModeCorrect /\ ActiveClientsCorrect) BY PTL, LockModeCorrect_implies_MutualExclusion
    <1>a. Init => (LockModeCorrect /\ ActiveClientsCorrect) BY DEF Init, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect
    <1>b. (LockModeCorrect /\ ActiveClientsCorrect /\ [Next]_vars) => (LockModeCorrect /\ ActiveClientsCorrect)'
        <2> /\ pc \in [Clients -> {"idle", "wait", "sleep", "cs"}]
            /\ lock_mode \in {"idle", "read", "write"}
            /\ active_clients \subseteq Clients
            /\ pending_readers \subseteq Readers
            /\ pending_writers \in Seq(Writers)
            BY PTL DEF TypeOK
        <2>a. CASE \E c \in Clients: FastAcquire(c) BY <2>a DEF FastAcquire, DesiredMode, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect, Clients
        <2>b. CASE \E c \in Clients: SlowAcquire(c) BY <2>b DEF SlowAcquire, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect, Clients
        <2>c. CASE \E c \in Clients: EnterCS(c)
            <3> SUFFICES ASSUME NEW c \in Clients, EnterCS(c), LockModeCorrect, ActiveClientsCorrect PROVE LockModeCorrect' /\ ActiveClientsCorrect' BY <2>c
            <3> WaitingReadersArePendingOrActive BY PTL
            <3> LockModeCorrect' BY DEF EnterCS, DesiredMode, LockModeCorrect, TrueActiveClients, Clients
            <3> ActiveClientsCorrect'
                <4>a. CASE lock_mode = "idle"
                    <5>a. CASE DesiredMode(c) = "write" BY <4>a, <5>a DEF EnterCS, DesiredMode, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect, Clients
                    <5>b. CASE DesiredMode(c) /= "write"
                        <6> USE DEF WaitingReadersArePendingOrActive
                        <6>a. CASE active_clients = {} /\ (\E cc \in Clients: {c \in Clients: pc[c] = "cs"} = {cc}) BY <4>a, <5>b DEF EnterCS, DesiredMode, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect, Clients
                        <6>b. CASE {c \in Clients: pc[c] = "cs"} \subseteq active_clients BY <4>a, <5>b DEF EnterCS, DesiredMode, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect, Clients
                        <6> QED BY <6>a, <6>b DEF ActiveClientsCorrect
                    <5> QED BY <5>a, <5>b DEF DesiredMode
                <4>b. CASE lock_mode /= "idle" BY <4>b DEF EnterCS, DesiredMode, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect, Clients
                <4> QED BY <4>a, <4>b
            <3> QED OBVIOUS
        <2>d. CASE \E c \in Clients: Release(c)
            <3> SUFFICES ASSUME NEW c \in Clients, Release(c), LockModeCorrect, ActiveClientsCorrect PROVE LockModeCorrect' /\ ActiveClientsCorrect' BY <2>d
            <3> DEFINE new_active_clients == active_clients \ {c}
            <3>a. CASE new_active_clients = {}  BY <3>a DEF Release, NotifyAll, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect, Clients
            <3>b. CASE new_active_clients /= {} BY <3>b DEF Release, NotifyAll, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect, Clients
            <3> QED BY <3>a, <3>b
        <2>e. CASE UNCHANGED vars BY <2>e DEF vars, LockModeCorrect, TrueActiveClients, ActiveClientsCorrect
        <2> QED BY <2>a, <2>b, <2>c, <2>d, <2>e DEF Next
    <1> QED BY PTL, <1>a, <1>b DEF Spec

====
