------------------------ MODULE TRaftCommitNoticeProof ------------------------
EXTENDS TRaftInvariantDefinitions, TRaftAgreementFromInvariant,
        TRaftProposalEvidenceProof, TRaftCommitTemporal
USE FormalFaultsDisabled, ParameterAssumptions DEF FormalFaultsDisabled, ParameterAssumptions

THEOREM ProposalQuorumCoversEachEntry ==
    ASSUME NEW p, Quorum(ProposalSenders(ackMessages, p)), NEW e \in Result(p)
    PROVE Quorum(MessageAckers(ackMessages, p.owner, p.epoch, e))
<1>1. ProposalSenders(ackMessages, p) \subseteq MessageAckers(ackMessages, p.owner, p.epoch, e)
    BY SMT DEF ProposalSenders, MessageAckers, Ack
<1>2. IsFiniteSet(Replicas) /\ Majority(Replicas, ProposalSenders(ackMessages, p))
      /\ MessageAckers(ackMessages, p.owner, p.epoch, e) \subseteq Replicas
    BY SMT DEF Quorum, Majority, MessageAckers
<1>3. Majority(Replicas, MessageAckers(ackMessages, p.owner, p.epoch, e))
    BY ONLY MajorityUpward, <1>1, <1>2
<1> QED BY ONLY <1>3 DEF Quorum, Majority

THEOREM EvidenceEpochUsesProposalOwner ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW p \in proposals,
           NEW f \in commitHistory, f.epoch = p.epoch
    PROVE Quorum(MessageAckers(ackMessages, p.owner, p.epoch, f.entry))
<1>1. f \in Evidence(ackMessages)
    BY DEF CommitEvidenceSound
<1>2. PICK c \in Replicas : Quorum(MessageAckers(ackMessages, c, f.epoch, f.entry))
    BY IndependentEvidenceHasActualDistinctSenders, <1>1
<1>3. MessageAckers(ackMessages, c, f.epoch, f.entry) # {}
    BY QuorumIsNonempty, <1>2
<1>4. PICK a \in ackMessages : a.receiver = c /\ a.epoch = f.epoch /\ f.entry \in a.contents
    BY SMT, <1>3 DEF MessageAckers
<1>5. PICK q \in retained[a.sender] : q.epoch = a.epoch /\ q.owner = a.receiver
    BY <1>4 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, AckOrigin
<1>6. a.sender \in Replicas /\ q \in proposals
    BY SMT, <1>4, <1>5 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, AckOrigin, TypeOK
<1>7. p = q /\ c = p.owner
    BY SMT, <1>4, <1>5, <1>6 DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY <1>2, <1>7

THEOREM ActiveKnowledgeHasCurrentOwnerQuorum ==
    ASSUME ProofInvariant, CommitEvidenceSound, NEW c \in Replicas, NEW e \in knownCommitted[c],
           role[c] = "Leader" \/ phase[c] = "commit"
    PROVE Quorum(MessageAckers(ackMessages, c, term[c], e))
<1>1. current[c] \in confirmations /\ current[c] \in proposals
      /\ current[c].epoch = term[c] /\ current[c].owner = c /\ term[c] \in Nat
    BY SMT DEF ProofInvariant, PrefixEvidenceInvariant, ActiveRecoveryCertificates, ActiveControlCertified,
       PreProvenanceInvariant, RecoveryInvariant, TypeOK, ControlInvariant, ControlShape, Terms
<1>2. PICK f \in commitHistory : f.entry = e /\ f.epoch <= term[c]
    BY DEF ProofInvariant, PrefixEvidenceInvariant, EpochKnowledgeInvariant, KnowledgeAt, KnownBy
<1>3. f.epoch \in Terms /\ f.epoch \in Nat /\ f.entry \in IssuedEntries /\ MayChoose(f.epoch, f.entry)
    BY SMT, EvidenceIsPossible, <1>2 DEF Terms
<1>4. CASE f.epoch = term[c]
    BY EvidenceEpochUsesProposalOwner, <1>1, <1>2, <1>4
<1>5. CASE f.epoch < term[c]
    <2>1. e \in current[c].prefix /\ e \in Result(current[c])
        BY SMT, <1>1, <1>2, <1>3, <1>5 DEF ProofInvariant, PreProvenanceInvariant,
           RecoveryInvariant, PotentialPreservation, Result
    <2>2. Quorum(ProposalSenders(ackMessages, current[c]))
        BY <1>1 DEF ProofInvariant, KnowledgeInvariant, ConfirmationHasQuorum, ProposalSenders
    <2> QED BY ProposalQuorumCoversEachEntry, <1>1, <2>1, <2>2
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5

THEOREM OldCommitNoticesSurviveAckGrowth ==
    ASSUME CommitNoticeHasQuorum, ackMessages \subseteq ackMessages'
    PROVE \A m \in commitMessages : Quorum(MessageAckers(ackMessages', m.owner, m.epoch, m.entry))
BY AckQuorumMonotone DEF CommitNoticeHasQuorum

THEOREM NewCommitEntryNoticeHasQuorum ==
    ASSUME ProofInvariant, ~MutNoCommitQuorum, ackMessages \subseteq ackMessages',
           NEW c \in Replicas, NEW e, CommitEntry(c, e)
    PROVE Quorum(MessageAckers(ackMessages', c, term[c], e))
<1>1. Quorum(MessageAckers(ackInbox[c], c, term[c], e)) /\ ackInbox[c] \subseteq ackMessages'
    BY SMT DEF CommitEntry, Ackers, ProofInvariant, KnowledgeInvariant, AckInboxOrigins
<1> QED BY AckQuorumMonotone, <1>1

THEOREM NewAdvertisedNoticeHasQuorum ==
    ASSUME ProofInvariant, CommitEvidenceSound, ackMessages \subseteq ackMessages',
           NEW c \in Replicas, NEW e, AdvertiseCommit(c, e)
    PROVE Quorum(MessageAckers(ackMessages', c, term[c], e))
<1>1. e \in knownCommitted[c] /\ (role[c] = "Leader" \/ phase[c] = "commit")
    BY SMT DEF AdvertiseCommit
<1>2. Quorum(MessageAckers(ackMessages, c, term[c], e))
    BY ActiveKnowledgeHasCurrentOwnerQuorum, <1>1
<1> QED BY AckQuorumMonotone, <1>2

THEOREM CommitNoticeHasQuorumInductiveStep ==
    ASSUME Inv, ProofNext
    PROVE CommitNoticeHasQuorum'
<1>1. ProofInvariant /\ CommitEvidenceSound /\ CommitNoticeHasQuorum /\ ProtocolNext
      /\ ackMessages \subseteq ackMessages'
    BY EveryStepPreservesDurabilityFacts DEF Inv, Safety, ProofNext, Next,
       ProofInvariant, PreProvenanceInvariant, DurabilityInvariant, DurabilityStep
<1>2. \A m \in commitMessages : Quorum(MessageAckers(ackMessages', m.owner, m.epoch, m.entry))
    BY OldCommitNoticesSurviveAckGrowth, <1>1
<1>3. KnowledgeChangingNext \/ UNCHANGED <<knownCommitted, commitMessages, confirmations>>
    BY ProtocolKnowledgeProjection, <1>1
<1>4. \A c \in Replicas : \A e : CommitEntry(c, e) => CommitNoticeHasQuorum'
    <2>1. ASSUME NEW c \in Replicas, NEW e, CommitEntry(c, e)
          PROVE CommitNoticeHasQuorum'
        <3>1. Quorum(MessageAckers(ackMessages', c, term[c], e))
            BY NewCommitEntryNoticeHasQuorum, <1>1, <2>1
        <3>2. commitMessages' = commitMessages \cup {[owner |-> c, epoch |-> term[c], entry |-> e]}
            BY <2>1 DEF CommitEntry
        <3> QED BY ONLY SMT, <1>2, <3>1, <3>2 DEF CommitNoticeHasQuorum
    <2> QED BY <2>1
<1>5. \A c \in Replicas : \A e : AdvertiseCommit(c, e) => CommitNoticeHasQuorum'
    BY SMT, NewAdvertisedNoticeHasQuorum, <1>1, <1>2 DEF AdvertiseCommit, CommitNoticeHasQuorum
<1> QED BY SMT, <1>2, <1>3, <1>4, <1>5 DEF KnowledgeChangingNext,
    LearnCommit, ConfirmProposal, CommitNoticeHasQuorum
=============================================================================
