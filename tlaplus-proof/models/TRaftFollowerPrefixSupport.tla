---------------------- MODULE TRaftFollowerPrefixSupport ----------------------
EXTENDS TRaftPrefixContextSupport, TRaftCanonicalTransitionSupport,
        TRaftLogMatchingFromInvariant, TRaftProposalEvidenceProof

NodeFollowerEvidence(r, F, T, R, H) == \A p \in R[r] :
    p.epoch = T[r] /\ p.owner # r =>
        \A e \in F[r] : e.term = T[r] =>
            \A x \in Prefix(F[r], e.part - 1) : KnownBy(H, T[r], x)

THEOREM CurrentEntryHasRetainedEpochAnchor ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW e \in formal[r], e.term = term[r]
    PROVE \E p \in retained[r] : p.epoch = term[r]
<1>1. LastTerm(formal[r]) = term[r]
    BY CurrentTermEntryPinsSublogEpoch
<1> QED BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryOriginFacts

THEOREM UnchangedNodeKeepsFollowerEvidence ==
    ASSUME ProofInvariant, TypeOK', CanonicalShape', NEW r \in Replicas,
           term[r] <= term'[r], formal'[r] = formal[r],
           proposals \subseteq proposals', commitHistory \subseteq commitHistory'
    PROVE NodeFollowerEvidence(r, formal', term', retained', commitHistory')
<1>1. term[r] \in Nat /\ term'[r] \in Nat
      /\ (\A e \in formal[r] : e.term \in Nat /\ e.term <= term[r])
    BY SMT DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant,
       TypeOK, CanonicalShape, Entries, Terms
<1>2. ASSUME NEW p \in retained'[r], p.epoch = term'[r], p.owner # r,
            NEW e \in formal'[r], e.term = term'[r]
      PROVE \A x \in Prefix(formal'[r], e.part - 1) : KnownBy(commitHistory', term'[r], x)
    <2>1. term[r] = term'[r] /\ e \in formal[r] /\ e.term = term[r]
        BY SMT, <1>1, <1>2
    <2>2. PICK q \in retained[r] : q.epoch = term[r]
        BY CurrentEntryHasRetainedEpochAnchor, <2>1
    <2>3. p \in proposals' /\ q \in proposals'
        BY SMT, <1>2, <2>2 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
    <2>4. p = q /\ p \in retained[r]
        BY SMT, <1>2, <2>1, <2>2, <2>3 DEF CanonicalShape
    <2>5. \A x \in Prefix(formal[r], e.part - 1) : KnownBy(commitHistory, term[r], x)
        BY <1>2, <2>1, <2>4 DEF ProofInvariant, PrefixEvidenceInvariant, FollowerPrefixEvidence
    <2> QED BY SMT, KnownBySurvivesHistoryGrowth, <2>1, <2>5
<1> QED BY <1>2 DEF NodeFollowerEvidence

THEOREM OwnerHasNoForeignCurrentAnchor ==
    ASSUME ProofInvariant, NEW r \in Replicas, phase[r] \in {"sync", "commit", "serve"}
    PROVE \A p \in retained[r] : p.epoch = term[r] => p.owner = r
<1>1. current[r] \in proposals /\ current[r].epoch = term[r] /\ current[r].owner = r
      /\ retained[r] \subseteq proposals
    BY DEF ProofInvariant, PreProvenanceInvariant, ControlInvariant, ControlShape, RecoveryInvariant, TypeOK
<1> QED BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape

THEOREM OwnerUpdateHasFollowerEvidence ==
    ASSUME ProofInvariant, NEW r \in Replicas, phase[r] \in {"sync", "commit", "serve"},
           term'[r] = term[r], retained'[r] = retained[r]
    PROVE NodeFollowerEvidence(r, formal', term', retained', commitHistory')
BY OwnerHasNoForeignCurrentAnchor DEF NodeFollowerEvidence

THEOREM ConfirmedProposalEntriesHaveEvidence ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW p \in confirmations
    PROVE \A e \in Result(p) : KnownBy(commitHistory, p.epoch, e)
<1>1. p \in proposals /\ Quorum(ProposalSenders(ackMessages, p))
    BY DEF ProofInvariant, MessageSourceInvariant, ConfirmationSources,
       KnowledgeInvariant, ConfirmationHasQuorum, ProposalSenders
<1>2. p.epoch \in Nat
    BY SMT, <1>1 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, Terms
<1>3. \A e \in Result(p) : [epoch |-> p.epoch, entry |-> e] \in commitHistory
    BY ChosenProposalHasEntryEvidence, <1>1
<1> QED BY EvidenceRecordIsKnown, <1>2, <1>3

THEOREM InstalledConfirmationHasFollowerEvidence ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW r \in Replicas, NEW p \in confirmations,
           formal'[r] = Result(p), term'[r] = p.epoch,
           commitHistory \subseteq commitHistory'
    PROVE NodeFollowerEvidence(r, formal', term', retained', commitHistory')
<1>1. \A e \in Result(p) : KnownBy(commitHistory, p.epoch, e)
    BY ConfirmedProposalEntriesHaveEvidence
<1>2. \A e \in formal'[r] : KnownBy(commitHistory', term'[r], e)
    BY KnownBySurvivesHistoryGrowth, <1>1
<1> QED BY SMT, <1>2 DEF NodeFollowerEvidence, Prefix

THEOREM AlignedOpenPartitionHasCurrentEntry ==
    ASSUME ProofInvariant, NEW r \in Replicas, Aligned(r, term[r])
    PROVE \E e \in formal[r] : e.part = Cur(formal[r]) /\ e.term = term[r]
<1>1. term[r] \in Terms /\ formal[r] \subseteq Entries
      /\ IsFiniteSet(formal[r]) /\ Coherent(formal[r])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, FiniteLogInvariant, FiniteNodeData
<1>2. formal[r] # {} /\ LastTerm(formal[r]) = term[r]
    BY AlignmentIdentifiesSublogEpoch, <1>1
<1>3. Origin(formal[r], Cur(formal[r])) = term[r]
    BY LastIndexBelongsToOpenPartition, <1>1, <1>2
<1>4. Part(formal[r], Cur(formal[r])) # {}
    BY SMT, FiniteLogFrontier, <1>1, <1>2 DEF Part
<1>5. (CHOOSE e \in Part(formal[r], Cur(formal[r])) : TRUE) \in Part(formal[r], Cur(formal[r]))
    BY ZenonT(5), <1>4
<1> QED BY SMT, <1>3, <1>4, <1>5 DEF Origin, Part
=============================================================================
