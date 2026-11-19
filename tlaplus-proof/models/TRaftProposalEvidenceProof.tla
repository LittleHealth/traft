----------------------- MODULE TRaftProposalEvidenceProof --------------------
EXTENDS TRaftProofState, TRaftCommitSupport
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM EvidenceRecordIsKnown ==
    ASSUME NEW H, NEW t \in Nat, NEW e, [epoch |-> t, entry |-> e] \in H
    PROVE KnownBy(H, t, e)
BY SMT DEF KnownBy

THEOREM ChosenProposalHasEntryEvidence ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW p \in proposals,
           Quorum(ProposalSenders(ackMessages, p)), NEW e \in Result(p)
    PROVE [epoch |-> p.epoch, entry |-> e] \in commitHistory
<1>1. p.owner \in Replicas /\ p.epoch \in Terms \ {0}
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. ProposalSenders(ackMessages, p) \subseteq MessageAckers(ackMessages, p.owner, p.epoch, e)
    BY SMT DEF ProposalSenders, MessageAckers, Ack
<1>30. IsFiniteSet(Replicas) /\ Quorum(ProposalSenders(ackMessages, p))
    OBVIOUS
<1>31. MessageAckers(ackMessages, p.owner, p.epoch, e) \subseteq Replicas
    BY ONLY SMT DEF MessageAckers
<1>3. IsFiniteSet(Replicas) /\ Quorum(ProposalSenders(ackMessages, p))
      /\ MessageAckers(ackMessages, p.owner, p.epoch, e) \subseteq Replicas
    BY ONLY <1>30, <1>31
<1>4. Quorum(MessageAckers(ackMessages, p.owner, p.epoch, e))
    BY ONLY MajorityUpward, <1>2, <1>3 DEF Quorum, Majority
<1>5. [epoch |-> p.epoch, entry |-> e] \in Evidence(ackMessages)
    BY QuorumCreatesIndependentEvidence, <1>1, <1>4
<1> QED BY <1>5 DEF CommitEvidenceSound

=============================================================================
