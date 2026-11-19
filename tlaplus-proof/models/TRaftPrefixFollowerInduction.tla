---------------------- MODULE TRaftPrefixFollowerInduction --------------------
EXTENDS TRaftFollowerReceiveProof, TRaftOriginFrames, TRaftTermAndVoteProof,
        TRaftHistoryRefinementProof
USE FormalFaultsDisabled DEF FormalFaultsDisabled

FollowerFramePremises ==
    /\ ProofInvariant /\ TypeOK' /\ CanonicalShape'
    /\ proposals \subseteq proposals' /\ commitHistory \subseteq commitHistory'
    /\ \A r \in Replicas : term[r] <= term'[r]

THEOREM FollowerEvidenceWithOneChangedNode ==
    ASSUME FollowerFramePremises, NEW c \in Replicas,
           \A r \in Replicas \ {c} : formal'[r] = formal[r],
           NodeFollowerEvidence(c, formal', term', retained', commitHistory')
    PROVE FollowerPrefixEvidence(formal', term', retained', commitHistory')
<1>1. \A r \in Replicas \ {c} : NodeFollowerEvidence(r, formal', term', retained', commitHistory')
    BY UnchangedNodeKeepsFollowerEvidence DEF FollowerFramePremises
<1> QED BY SMT, <1>1 DEF FollowerPrefixEvidence, NodeFollowerEvidence

THEOREM OwnerFormalUpdateKeepsFollowerEvidence ==
    ASSUME FollowerFramePremises, NEW c \in Replicas, NEW v, NEW k,
           CreateEntry(c, v) \/ CreateSuccessor(c, v, k) \/ ConfirmProposal(c)
    PROVE FollowerPrefixEvidence(formal', term', retained', commitHistory')
<1>1. phase[c] \in {"sync", "serve"} /\ UNCHANGED <<term, retained>>
      /\ (\A r \in Replicas \ {c} : formal'[r] = formal[r])
    BY SMT DEF CreateEntry, CreateSuccessor, ConfirmProposal, FollowerFramePremises,
       ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. NodeFollowerEvidence(c, formal', term', retained', commitHistory')
    BY OwnerUpdateHasFollowerEvidence, <1>1 DEF FollowerFramePremises
<1> QED BY FollowerEvidenceWithOneChangedNode, <1>1, <1>2

THEOREM NormalReceiveKeepsFollowerEvidence ==
    ASSUME FollowerFramePremises, EntryContextUnique, NEW c \in Replicas, NEW o, ReceiveEntry(c, o)
    PROVE FollowerPrefixEvidence(formal', term', retained', commitHistory')
<1>1. \A r \in Replicas \ {c} : formal'[r] = formal[r]
    BY SMT DEF ReceiveEntry, FollowerFramePremises, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. NodeFollowerEvidence(c, formal', term', retained', commitHistory')
    BY ReceiveNodeKeepsFollowerEvidence DEF FollowerFramePremises
<1> QED BY FollowerEvidenceWithOneChangedNode, <1>1, <1>2

THEOREM LearnConfirmationKeepsFollowerEvidence ==
    ASSUME FollowerFramePremises, CommitEvidenceSound,
           NEW c \in Replicas, NEW p, LearnConfirmation(c, p)
    PROVE FollowerPrefixEvidence(formal', term', retained', commitHistory')
<1>1. p \in confirmations /\ term'[c] = p.epoch
      /\ formal'[c] = Publish(c, p)
      /\ (\A r \in Replicas \ {c} : formal'[r] = formal[r])
    BY SMT DEF LearnConfirmation, FollowerFramePremises, ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. NodeFollowerEvidence(c, formal', term', retained', commitHistory')
    <2>1. CASE p.first \in formal[c]
        BY UnchangedNodeKeepsFollowerEvidence, <1>1, <2>1 DEF FollowerFramePremises, Publish
    <2>2. CASE p.first \notin formal[c]
        BY InstalledConfirmationHasFollowerEvidence, <1>1, <2>2 DEF FollowerFramePremises, Publish
    <2> QED BY <2>1, <2>2
<1> QED BY FollowerEvidenceWithOneChangedNode, <1>1, <1>2

THEOREM FollowerPrefixEvidenceInductiveStep ==
    ASSUME Inv, ProofNext, RecoveryInvariant'
    PROVE FollowerPrefixEvidence(formal', term', retained', commitHistory')
<1>1. ProofInvariant /\ TypeOK /\ ProtocolNext /\ Observe /\ StepFacts
      /\ EntryContextUnique /\ CommitEvidenceSound
    BY CandidateStepHasMonotonicFacts DEF Inv, Safety, ProofInvariant, PreProvenanceInvariant,
       RecoveryInvariant, ProofNext, Next
<1>2. FollowerFramePremises
    BY SMT, ProposalsNeverShrink, <1>1 DEF FollowerFramePremises, StepFacts, Observe, RecoveryInvariant
<1>3. FormalAnchorChanges \/ UNCHANGED formal
    BY FormalAnchorActionProjection, <1>1
<1>4. UNCHANGED formal => FollowerPrefixEvidence(formal', term', retained', commitHistory')
    BY UnchangedNodeKeepsFollowerEvidence, <1>2
       DEF FollowerFramePremises, FollowerPrefixEvidence, NodeFollowerEvidence
<1>5. FormalAnchorChanges => FollowerPrefixEvidence(formal', term', retained', commitHistory')
    BY SMT, OwnerFormalUpdateKeepsFollowerEvidence, NormalReceiveKeepsFollowerEvidence,
       LearnConfirmationKeepsFollowerEvidence, <1>1, <1>2 DEF FormalAnchorChanges
<1> QED BY <1>3, <1>4, <1>5
=============================================================================
