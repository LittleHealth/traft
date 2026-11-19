-------------------------- MODULE TRaftLogContextProof -----------------------
EXTENDS TRaftProofState, TRaftLogContextState, TLAPS

THEOREM ContextsSurviveSourceGrowth ==
    ASSUME NEW L, NEW E, NEW F, E \subseteq F, LogContexts(L, E)
    PROVE LogContexts(L, F)
BY SMT DEF LogContexts

THEOREM AppendContextFromObservation ==
    ASSUME NEW L, NEW e, NEW E, NEW F, E \subseteq F,
           LogContexts(L, E), e.part \in Int,
           \A x \in L : x.part \in Int /\ x.part <= e.part,
           [entry |-> e, prefix |-> Prefix(L, e.part - 1)] \in F
    PROVE LogContexts(L \cup {e}, F)
<1>1. \A x \in L \cup {e} : Prefix(L \cup {e}, x.part - 1) = Prefix(L, x.part - 1)
    BY SMT DEF Prefix
<1>2. \A x \in L : \E ctx \in F : ctx.entry = x /\ ctx.prefix = Prefix(L \cup {e}, x.part - 1)
    <2>1. ASSUME NEW x \in L
          PROVE \E ctx \in F : ctx.entry = x /\ ctx.prefix = Prefix(L \cup {e}, x.part - 1)
        <3>1. PICK ctx \in E : ctx.entry = x /\ ctx.prefix = Prefix(L, x.part - 1)
            BY <2>1 DEF LogContexts
        <3>2. ctx \in F /\ ctx.entry = x /\ ctx.prefix = Prefix(L \cup {e}, x.part - 1)
            BY ZenonT(5), <1>1, <2>1, <3>1
        <3> QED BY ONLY ZenonT(5), <3>2
    <2> QED BY <2>1
<1>3. DEFINE ctx == [entry |-> e, prefix |-> Prefix(L, e.part - 1)]
<1>40. ctx \in F /\ ctx.entry = e /\ ctx.prefix = Prefix(L, e.part - 1)
    BY DEF ctx
<1>41. Prefix(L \cup {e}, e.part - 1) = Prefix(L, e.part - 1)
    BY ONLY ZenonT(5), <1>1
<1>4. ctx \in F /\ ctx.entry = e /\ ctx.prefix = Prefix(L \cup {e}, e.part - 1)
    BY ONLY ZenonT(5), <1>40, <1>41
<1>5. \E x \in F : x.entry = e /\ x.prefix = Prefix(L \cup {e}, e.part - 1)
    BY ONLY ZenonT(5), <1>4
<1> QED BY ONLY ZenonT(5), <1>2, <1>5 DEF LogContexts

THEOREM ObservationIncludesLeaderContext ==
    ASSUME Observe, NEW r \in Replicas, NEW e \in formal'[r],
           role'[r] = "Leader", e.term = term'[r]
    PROVE entryContexts \subseteq entryContexts'
       /\ [entry |-> e, prefix |-> Prefix(formal'[r], e.part - 1)] \in entryContexts'
<1>1. entryContexts' = entryContexts \cup
         (UNION { {[entry |-> x, prefix |-> Prefix(formal'[s], x.part - 1)] :
                    x \in {y \in formal'[s] : y.term = term'[s]}} :
                   s \in {n \in Replicas : role'[n] = "Leader"}}) \cup
         {[entry |-> p.first, prefix |-> p.prefix] : p \in proposals'}
    BY DEF Observe
<1>2. r \in {n \in Replicas : role'[n] = "Leader"}
      /\ e \in {y \in formal'[r] : y.term = term'[r]}
    BY ZenonT(5)
<1>3. [entry |-> e, prefix |-> Prefix(formal'[r], e.part - 1)] \in
          {[entry |-> x, prefix |-> Prefix(formal'[r], x.part - 1)] :
               x \in {y \in formal'[r] : y.term = term'[r]}}
    BY ONLY ZenonT(5), <1>2
<1>4. {[entry |-> x, prefix |-> Prefix(formal'[r], x.part - 1)] :
               x \in {y \in formal'[r] : y.term = term'[r]}} \in
         { {[entry |-> x, prefix |-> Prefix(formal'[s], x.part - 1)] :
                    x \in {y \in formal'[s] : y.term = term'[s]}} :
                   s \in {n \in Replicas : role'[n] = "Leader"}}
    BY ONLY ZenonT(5), <1>2
<1>5. [entry |-> e, prefix |-> Prefix(formal'[r], e.part - 1)] \in
         (UNION { {[entry |-> x, prefix |-> Prefix(formal'[s], x.part - 1)] :
                    x \in {y \in formal'[s] : y.term = term'[s]}} :
                   s \in {n \in Replicas : role'[n] = "Leader"}})
    BY ONLY ZenonT(5), <1>3, <1>4
<1> QED BY ONLY ZenonT(5), <1>1, <1>5

THEOREM ObservationIncludesProposalContext ==
    ASSUME Observe, NEW p \in proposals'
    PROVE entryContexts \subseteq entryContexts'
       /\ [entry |-> p.first, prefix |-> p.prefix] \in entryContexts'
BY SMT DEF Observe
=============================================================================
