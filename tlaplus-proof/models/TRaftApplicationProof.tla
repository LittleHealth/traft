------------------------- MODULE TRaftApplicationProof -----------------------
EXTENDS TRaftClientCore, TLAPS

\* These lemmas concern the actual client transition operators. They do not
\* assume application agreement or linearizability, and are not a substitute
\* for the missing temporal application/refinement theorem.
THEOREM IndependentPointEffectsCommute ==
    ASSUME NEW db \in [Keys -> Values \cup {Missing}],
           NEW p \in ClientCommands, NEW q \in ClientCommands,
           p.key # q.key
    PROVE /\ Effect(Effect(db, p), q) = Effect(Effect(db, q), p)
          /\ Reply(Effect(db, p), q) = Reply(db, q)
          /\ Reply(Effect(db, q), p) = Reply(db, p)
<1>1. Effect(Effect(db, p), q) \in [Keys -> Values \cup {Missing}]
      /\ Effect(Effect(db, q), p) \in [Keys -> Values \cup {Missing}]
    BY SMT DEF ClientCommands, Effect
<1>2. \A k \in Keys : Effect(Effect(db, p), q)[k] = Effect(Effect(db, q), p)[k]
    BY SMT DEF ClientCommands, Effect
<1>3. Effect(Effect(db, p), q) = Effect(Effect(db, q), p)
    BY SMT, <1>1, <1>2
<1>4. Reply(Effect(db, p), q) = Reply(db, q)
      /\ Reply(Effect(db, q), p) = Reply(db, p)
    BY SMT DEF ClientCommands, Effect, Reply
<1> QED BY <1>3, <1>4

THEOREM ReadHasNoEffect ==
    ASSUME NEW db, NEW q, q.op = "Get"
    PROVE Effect(db, q) = db /\ Reply(db, q) = db[q.key]
BY SMT DEF Effect, Reply

THEOREM CachedRetryHasNoEffect ==
    ASSUME NEW r \in Replicas, NEW e, e.kind = "data",
           cache[r][e.value.id].ready, ApplyClient(r, e)
    PROVE UNCHANGED <<machine, cache>>
BY SMT DEF ApplyClient

THEOREM FirstApplicationStoresOriginalResult ==
    ASSUME NEW r \in Replicas, NEW e, e.kind = "data",
           ~cache[r][e.value.id].ready, ApplyClient(r, e),
           machine \in [Replicas -> [Keys -> Values \cup {Missing}]],
           cache \in [Replicas -> [RequestIds ->
                          [ready : BOOLEAN, value : Values \cup {Missing, "OK"}]]],
           e.value \in ClientCommands
    PROVE /\ cache'[r][e.value.id] =
                  [ready |-> TRUE, value |-> Reply(machine[r], e.value)]
          /\ machine'[r] = Effect(machine[r], e.value)
BY SMT DEF ApplyClient, ClientCommands

THEOREM CrashAndRecoveryPreserveClientPersistence ==
    ASSUME ~MutLoseDedup, Background,
           cache \in [Replicas -> [RequestIds ->
                          [ready : BOOLEAN, value : Values \cup {Missing, "OK"}]]]
    PROVE UNCHANGED <<machine, cache>>
BY SMT DEF Background

THEOREM ReplyRequiresCachedResult ==
    ASSUME ~MutEarlyReply, NEW r \in Replicas, NEW q \in calls,
           SendReply(r, q)
    PROVE /\ cache[r][q.id].ready
          /\ \A m \in replyMessages' \ replyMessages :
               m.id = q.id /\ m.value = cache[r][q.id].value
BY SMT DEF SendReply

THEOREM ApplyWaitsForEarlierPartitions ==
    ASSUME NEW r \in Replicas, NEW e, ApplyClient(r, e)
    PROVE /\ e \in formal[r] \cap knownCommitted[r]
          /\ Prefix(formal[r], e.part - 1) \subseteq applied[r]
BY SMT DEF ApplyClient, ApplyEntry

=============================================================================
