---- MODULE FairRWLockProofs ----

EXTENDS FairRWLock, FiniteSets, FiniteSetTheorems, TLAPS

TypeOK_Ind ==
    /\ TypeOK
    /\ IsFiniteSet({c \in Clients: pc[c] = "cs"})
    /\ lock_count = Cardinality({c \in Clients: pc[c] = "cs"})

THEOREM TypeCorrect == Spec => []TypeOK_Ind
    <1>a. Init => TypeOK_Ind BY FS_EmptySet DEF Init, TypeOK_Ind, TypeOK
    <1>b. (TypeOK_Ind /\ [Next]_vars) => TypeOK_Ind'
        <2>a. (TypeOK_Ind /\ \E c \in Clients: BeginAcquire(c)) => TypeOK_Ind'
            <3>a. (\E c \in Clients: BeginAcquire(c)) => ({c \in Clients: pc[c] = "cs"}' = {c \in Clients: pc[c] = "cs"})
                <4> SUFFICES ASSUME NEW c \in Clients, BeginAcquire(c) PROVE {c \in Clients: pc[c] = "cs"}' = {c \in Clients: pc[c] = "cs"} OBVIOUS
                <4> QED BY DEF BeginAcquire
            <3> QED BY <3>a DEF BeginAcquire, TypeOK_Ind, TypeOK
        <2>b. (TypeOK_Ind /\ \E c \in Clients: EnterCS(c)) => TypeOK_Ind'
            <3> SUFFICES ASSUME TypeOK_Ind, NEW c \in Clients, EnterCS(c) PROVE TypeOK_Ind' OBVIOUS
            <3>a. CASE lock_queue[1] = c /\ SafeToEnter(IF c \in Writers THEN "write" ELSE "read")
                <4>a. c \notin {c \in Clients: pc[c] = "cs"} BY DEF EnterCS
                <4>b. {c \in Clients: pc[c] = "cs"}' = {c \in Clients: pc[c] = "cs"} \union {c} BY <3>a DEF EnterCS, TypeOK_Ind, TypeOK
                <4>c. IsFiniteSet({c \in Clients: pc[c] = "cs"})' /\ Cardinality({c \in Clients: pc[c] = "cs"}') = Cardinality({c \in Clients: pc[c] = "cs"}) + 1
                      BY <4>a, <4>b, FS_AddElement DEF TypeOK_Ind
                <4> QED BY <4>c DEF EnterCS, TypeOK_Ind, TypeOK
            <3>b. CASE ~(lock_queue[1] = c /\ SafeToEnter(IF c \in Writers THEN "write" ELSE "read")) BY <3>b DEF EnterCS, TypeOK_Ind, TypeOK
            <3> QED BY <3>a, <3>b
        <2>c. (TypeOK_Ind /\ \E c \in Clients: Release(c)) => TypeOK_Ind'
            <3> SUFFICES ASSUME TypeOK_Ind, NEW c \in Clients, Release(c) PROVE TypeOK_Ind' OBVIOUS
            <3>x. {c \in Clients: pc[c] = "cs"}' = ({c \in Clients: pc[c] = "cs"} \ {c}) BY DEF Release
            <3>y. c \in {c \in Clients: pc[c] = "cs"} BY DEF Release
            <3>a. Cardinality({c \in Clients: pc[c] = "cs"})' = Cardinality({c \in Clients: pc[c] = "cs"}) - 1
                  BY <3>x, <3>y, FS_RemoveElement DEF TypeOK_Ind
            <3>c. IsFiniteSet({c \in Clients: pc[c] = "cs"})'
                  BY <3>x, <3>y, FS_RemoveElement DEF TypeOK_Ind
            <3>b. lock_count' = Cardinality({c \in Clients: pc[c] = "cs"})'
                  BY <3>x, <3>y, <3>a DEF Release, TypeOK_Ind
            <3>f. lock_count' \in Nat BY <3>b, <3>c, FS_CardinalityType
            <3> QED BY <3>a, <3>c, <3>f DEF Release, TypeOK_Ind, TypeOK
        <2>d. (TypeOK_Ind /\ UNCHANGED vars) => TypeOK_Ind' BY DEF vars, TypeOK_Ind, TypeOK
        <2> QED BY <2>a, <2>b, <2>c, <2>d DEF Next
    <1> QED BY PTL, <1>a, <1>b DEF Spec

LEMMA LockModeCorrect_implies_MutualExclusion == ASSUME LockModeCorrect, TypeOK PROVE MutualExclusion
    <1> SUFFICES ASSUME LockModeCorrect, TypeOK, NEW c \in Clients, pc[c] = "cs", NEW w \in (Writers \ {c}) PROVE pc[w] /= "cs" BY DEF MutualExclusion
    <1>a. CASE lock_mode = "idle" BY <1>a DEF LockModeCorrect
    <1>b. CASE lock_mode = "read" BY <1>b, ReadersAndWritersDisjoint DEF LockModeCorrect, Clients
    <1>c. CASE lock_mode = "write" BY <1>c DEF LockModeCorrect, Clients
    <1> QED BY <1>a, <1>b, <1>c DEF TypeOK

THEOREM Safe == Spec => []MutualExclusion
    <1> SUFFICES ASSUME []TypeOK_Ind PROVE Spec => []MutualExclusion BY TypeCorrect
    <1> SUFFICES Spec => []LockModeCorrect BY PTL, LockModeCorrect_implies_MutualExclusion DEF TypeOK_Ind
    <1>a. Init => LockModeCorrect BY DEF Init, LockModeCorrect
    <1>b. (LockModeCorrect /\ [Next]_vars) => LockModeCorrect'
        <2>x. TypeOK_Ind BY PTL
        <2>a. CASE \E c \in Clients: BeginAcquire(c) BY <2>x, <2>a DEF BeginAcquire, LockModeCorrect, TypeOK_Ind, TypeOK
        <2>b. CASE \E c \in Clients: EnterCS(c) \* BY <2>x, <2>b DEF EnterCS, LockModeCorrect, TypeOK_Ind, TypeOK
            <3> SUFFICES ASSUME LockModeCorrect, NEW c \in Clients, EnterCS(c) PROVE LockModeCorrect' BY <2>b
            <3>a. CASE c \in Writers
                <4>a. CASE lock_mode = "idle"
                    <5>a. CASE lock_queue[1] = c \*BY <4>a, <5>a, <3>a, <2>x DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                        <6>a. lock_mode' = "write" BY <4>a, <5>a, <3>a, <2>x DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                        <6> SUFFICES \E w \in Writers: {c \in Clients: pc'[c] = "cs"} = {w} BY <6>a DEF LockModeCorrect
                        <6> WITNESS c \in Writers
                        <6> QED BY <6>a, <4>a, <5>a, <3>a, <2>x DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                    <5>b. CASE lock_queue[1] /= c BY <4>a, <5>b, <3>a, <2>x DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                    <5> QED BY <5>a, <5>b
                <4>b. CASE lock_mode = "read" BY <4>b, <3>a, <2>x DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                <4>c. CASE lock_mode = "write"
                    <5> SUFFICES UNCHANGED {c \in Clients: pc[c] = "cs"} BY <4>c, <3>a, <2>x DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                    <5>a. pc[c] /= "cs" BY <4>c, <3>a, <2>x DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                    <5>b. pc'[c] = "sleep" BY <4>c, <3>a, <2>x DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                    <5> QED BY <4>c, <3>a, <2>x, <5>a, <5>b DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                <4> QED BY <2>x, <4>a, <4>b, <4>c DEF TypeOK_Ind, TypeOK
            <3>b. CASE c \notin Writers
                <4> c \in Readers BY <3>b DEF Clients
                <4>a. CASE lock_mode = "idle" BY <2>x, <3>b, <4>a DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                <4>b. CASE lock_mode = "read" BY <2>x, <3>b, <4>b DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                <4>c. CASE lock_mode = "write"
                    <5>a. UNCHANGED lock_mode BY <2>x, <3>b, <4>c DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                    <5> QED BY <2>x, <3>b, <4>c, <5>a DEF EnterCS, SafeToEnter, LockModeCorrect, TypeOK_Ind, TypeOK
                <4> QED BY <2>x, <4>a, <4>b, <4>c DEF TypeOK_Ind, TypeOK
            <3> QED BY <3>a, <3>b DEF Clients
        <2>c. CASE \E c \in Clients: Release(c)
            <3> SUFFICES ASSUME LockModeCorrect, NEW c \in Clients, Release(c) PROVE LockModeCorrect' BY <2>c
            <3>b. CASE lock_mode = "idle" BY <3>b DEF Release, LockModeCorrect
            <3>c. CASE lock_mode = "read"
                <4>a. CASE lock_count = 1 BY <2>x, <4>a, FS_Singleton DEF Release, LockModeCorrect, TypeOK_Ind, TypeOK
                <4>b. CASE lock_count > 1 BY <2>x, <3>c, <4>b DEF Release, LockModeCorrect, TypeOK_Ind, TypeOK
                <4>c. CASE lock_count < 1 BY <2>x, <4>c, FS_EmptySet DEF Release, TypeOK_Ind, TypeOK
                <4> QED BY <2>x, <4>a, <4>b, <4>c DEF TypeOK_Ind, TypeOK
            <3>d. CASE lock_mode = "write" BY <3>d, <2>x, FS_Singleton DEF Release, LockModeCorrect, TypeOK_Ind, TypeOK
            <3> QED BY <2>x, <3>b, <3>c, <3>d DEF TypeOK_Ind, TypeOK
        <2>d. CASE UNCHANGED vars BY <2>d DEF vars, LockModeCorrect
        <2> QED BY <2>a, <2>b, <2>c, <2>d DEF Next
    <1> QED BY PTL, <1>a, <1>b DEF Spec

====
