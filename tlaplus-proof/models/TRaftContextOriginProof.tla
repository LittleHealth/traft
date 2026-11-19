---------------------- MODULE TRaftContextOriginProof ------------------------
EXTENDS TRaftProofState, TRaftContextOriginState, TLAPS

THEOREM ContextOriginsInitially == ProofInit => ContextOrigins(canonical, entryContexts)
BY SMT DEF ProofInit, Init, ContextOrigins

THEOREM ContextOriginsInductiveStep ==
    ASSUME ContextOrigins(canonical, entryContexts), TypeOK', Observe, GhostNext
    PROVE ContextOrigins(canonical', entryContexts')
<1>1. \A t \in Terms : canonical[t] \subseteq canonical'[t]
    BY SMT DEF GhostNext
<1>2. \A ctx \in entryContexts :
          ctx.entry.term \in Terms /\ ctx.entry \in canonical'[ctx.entry.term]
    BY SMT, <1>1 DEF ContextOrigins
<1>3. \A r \in Replicas : role'[r] = "Leader" =>
          \A e \in formal'[r] : e.term = term'[r] =>
            e.term \in Terms /\ e \in canonical'[e.term]
    <2>1. ASSUME NEW r \in Replicas, role'[r] = "Leader", NEW e \in formal'[r], e.term = term'[r]
          PROVE e.term \in Terms /\ e \in canonical'[e.term]
        <3>1. e.term \in Terms
            BY SMT, <2>1 DEF TypeOK
        <3> QED BY SMT, <2>1, <3>1 DEF GhostNext
    <2> QED BY <2>1
<1>4. \A p \in proposals' : p.first.term \in Terms /\ p.first \in canonical'[p.first.term]
    <2>1. ASSUME NEW p \in proposals'
          PROVE p.first.term \in Terms /\ p.first \in canonical'[p.first.term]
        <3>1. p.epoch \in Terms /\ p.first.term = p.epoch
            BY SMT, <2>1 DEF TypeOK
        <3> QED BY SMT, <2>1, <3>1 DEF GhostNext, Result
    <2> QED BY <2>1
<1> QED BY SMT, <1>2, <1>3, <1>4 DEF ContextOrigins, Observe

THEOREM ContextOriginsStuttering ==
    ASSUME ContextOrigins(canonical, entryContexts), UNCHANGED proofVars
    PROVE ContextOrigins(canonical', entryContexts')
BY SMT DEF ContextOrigins, proofVars, vars, protocolVars, observerVars

THEOREM ContextOriginIdentifiesCanonicalPrefix ==
    ASSUME ContextOrigins(canonical, entryContexts), CanonicalShape,
           EntryContextUnique, NEW ctx \in entryContexts
    PROVE ctx.prefix = Prefix(canonical[ctx.entry.term], ctx.entry.part - 1)
<1>1. ctx.entry.term \in Terms /\ ctx.entry \in canonical[ctx.entry.term]
    BY DEF ContextOrigins
<1>2. ContextSound(canonical[ctx.entry.term])
    BY <1>1 DEF CanonicalShape
<1>3. PICK source \in entryContexts : source.entry = ctx.entry
          /\ source.prefix = Prefix(canonical[ctx.entry.term], ctx.entry.part - 1)
    BY SMT, <1>1, <1>2 DEF ContextSound
<1> QED BY SMT, <1>3 DEF EntryContextUnique
=============================================================================
