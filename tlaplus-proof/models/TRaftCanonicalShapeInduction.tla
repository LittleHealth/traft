---------------------- MODULE TRaftCanonicalShapeInduction -------------------
EXTENDS TRaftInvariantDefinitions, TRaftCanonicalLogShapeProof,
        TRaftCanonicalContextProof, TRaftCanonicalProposalProof, TRaftFormalSublogProof,
        TRaftReportSublogProof, TRaftFormalTermProof, TRaftFiniteTemporal
USE FormalFaultsDisabled DEF FormalFaultsDisabled

THEOREM CanonicalShapeInductiveStep ==
    ASSUME Inv, ProofNext, TypeOK'
    PROVE CanonicalShape'
<1>1. ProofInvariant /\ ElectionSafety /\ EntryContextUnique
      /\ ProtocolNext /\ Next /\ term' \in [Replicas -> Terms]
    BY DEF Inv, Safety, ProofNext, Next, TypeOK
<1>2. ControlInvariant /\ FiniteLogInvariant /\ ElectionInvariant /\ UniqueProposalEpoch
    BY DEF Inv, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape, UniqueProposalEpoch
<1>3. FiniteLogInvariant'
    BY FiniteLogInductiveStep, <1>1, <1>2
<1>4. CanonicalLogShape(canonical') /\ CanonicalContexts(canonical', entryContexts')
    BY CanonicalLogShapeInductiveStep, CanonicalContextsInductiveStep, <1>1
<1>40. canonical' \in [Terms -> SUBSET Entries]
    BY <1>4 DEF CanonicalLogShape
<1>5. ProposalCanonicalLinks(canonical', proposals')
    BY ProposalCanonicalLinksInductiveStep, <1>1
<1>6. UniqueProposalEpoch'
    BY ProposalIdentityInductiveStep, <1>1, <1>2
<1>7. FormalSublogs(formal', canonical', proposals')
    BY FormalSublogsInductiveStep, <1>1, <1>3
<1>8. FormalTermBounds(formal', term') /\ PostLeaderEqualsCanonical
    BY FormalTermBoundsInductiveStep, LeaderCanonicalEqualityInductiveStep, <1>1
<1>9. ReportSublogs(reportMessages', canonical', proposals')
    BY ReportSublogsInductiveStep, <1>1
<1>10. \A r \in Replicas : formal'[r] \subseteq Entries /\ IsFiniteSet(formal'[r])
    BY <1>3 DEF TypeOK, FiniteLogInvariant, FiniteNodeData
<1>11. \A r \in Replicas : LogContexts(formal'[r], entryContexts')
    BY SublogInheritsCanonicalContexts, <1>4, <1>40, <1>7, <1>10 DEF FormalSublogs
<1>12. \A m \in reportMessages' : m.entries \subseteq Entries /\ IsFiniteSet(m.entries)
    BY NewReportsHaveOldSublogs, <1>1
<1>13. \A m \in reportMessages' : LogContexts(m.entries, entryContexts')
    BY SublogInheritsCanonicalContexts, <1>4, <1>40, <1>9, <1>12 DEF ReportSublogs
<1> QED BY ONLY SMT, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>11, <1>13
    DEF CanonicalShape, CanonicalLogShape, CanonicalContexts, ContextSound, LogContexts,
        BoundedLogCounts, ProposalCanonicalLinks, UniqueProposalEpoch, FormalSublogs,
        Sublog, SublogIn, FormalTermBounds, LogTermBound, PostLeaderEqualsCanonical, ReportSublogs
=============================================================================
