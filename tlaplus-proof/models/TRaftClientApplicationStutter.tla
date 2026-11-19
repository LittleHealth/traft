---------------------- MODULE TRaftClientApplicationStutter ----------------------
EXTENDS TRaftClientApplicationProof

\* Separate the frame equalities from the application predicate expansion.
\* These facts have no protocol, safety, or type premise.
THEOREM PersistentApplicationComponentsStutter ==
    UNCHANGED <<machine, cache, applied>> =>
      /\ machine' = machine /\ cache' = cache /\ applied' = applied
BY ONLY SMT

THEOREM PersistentApplicationPredicatesStutter ==
    (machine' = machine /\ cache' = cache /\ applied' = applied) =>
      /\ ApplicationTypes' = ApplicationTypes
      /\ ReadyIdsMatchApplied' = ReadyIdsMatchApplied
BY ONLY IsaM("auto") DEF ApplicationTypes, ReadyIdsMatchApplied

THEOREM ClientApplicationFactsStutter ==
    ApplicationTypes /\ ReadyIdsMatchApplied /\ UNCHANGED <<machine, cache, applied>>
      => ApplicationTypes' /\ ReadyIdsMatchApplied'
BY ONLY PersistentApplicationComponentsStutter, PersistentApplicationPredicatesStutter
=============================================================================
