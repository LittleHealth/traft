--------------------------- MODULE TRaftLogTypeProof -------------------------
EXTENDS TRaftCreatedEntryProof, TRaftTypeFrames, TRaftAgreementFromInvariant

LogStorageTypes ==
    /\ formal \in [Replicas -> SUBSET Entries]
    /\ stored \in [Replicas -> SUBSET Entries]
    /\ knownCommitted \in [Replicas -> SUBSET Entries]
    /\ applied \in [Replicas -> SUBSET Entries]
    /\ retained \in [Replicas -> SUBSET proposals]
    /\ \A r \in Replicas : Coherent(formal[r])
ValidProposalEntry(p) ==
    /\ p \in ProposalRecords /\ p.owner \in Replicas /\ p.epoch \in Terms \ {0}
    /\ p.first \in Entries /\ p.first.term = p.epoch
    /\ p.prefix \subseteq Entries /\ Coherent(Result(p))
    /\ p.first.part = Cur(p.prefix) + 1
    /\ p.first.index = LastIndex(p.prefix) + 1
    /\ p.first.prevSize = Count(p.prefix, Cur(p.prefix))
ProposalEntryTypes == \A p \in proposals : ValidProposalEntry(p)

THEOREM UnchangedProposalTypes ==
    ASSUME ProposalEntryTypes, UNCHANGED proposals
    PROVE ProposalEntryTypes'
BY SMT DEF ProposalEntryTypes

THEOREM AppendedFormalStorageTypes ==
    ASSUME LogStorageTypes, ProposalEntryTypes, NEW r \in Replicas, NEW e \in Entries,
           Coherent(formal[r] \cup {e}),
           formal' = [formal EXCEPT ![r] = @ \cup {e}],
           stored' = [stored EXCEPT ![r] = @ \cup {e}],
           UNCHANGED <<knownCommitted, applied, retained, proposals>>
    PROVE LogStorageTypes' /\ ProposalEntryTypes'
<1>1. formal \in [Replicas -> SUBSET Entries] /\ stored \in [Replicas -> SUBSET Entries]
      /\ (\A s \in Replicas : Coherent(formal[s]))
    BY DEF LogStorageTypes
<1>2. formal' \in [Replicas -> SUBSET Entries] /\ stored' \in [Replicas -> SUBSET Entries]
    BY SMT, <1>1
<1>3. \A s \in Replicas : Coherent(formal'[s])
    BY SMT, <1>1
<1>4. ProposalEntryTypes'
    BY UnchangedProposalTypes
<1> QED BY SMT, <1>2, <1>3, <1>4 DEF LogStorageTypes

THEOREM ReplacedFormalTypes ==
    ASSUME LogStorageTypes, ProposalEntryTypes, NEW r \in Replicas,
           NEW L, L \subseteq Entries, Coherent(L), formal' = [formal EXCEPT ![r] = L],
           UNCHANGED <<stored, knownCommitted, applied, retained, proposals>>
    PROVE LogStorageTypes' /\ ProposalEntryTypes'
<1>1. formal \in [Replicas -> SUBSET Entries] /\ \A s \in Replicas : Coherent(formal[s])
    BY DEF LogStorageTypes
<1>2. formal' \in [Replicas -> SUBSET Entries] /\ \A s \in Replicas : Coherent(formal'[s])
    BY SMT, <1>1
<1>3. ProposalEntryTypes'
    BY UnchangedProposalTypes
<1> QED BY SMT, <1>2, <1>3 DEF LogStorageTypes

THEOREM PublishedLogTypes ==
    ASSUME LogStorageTypes, ProposalEntryTypes, NEW r \in Replicas, NEW p \in proposals
    PROVE Publish(r, p) \subseteq Entries /\ Coherent(Publish(r, p))
<1>1. formal[r] \subseteq Entries /\ Coherent(formal[r]) /\ ValidProposalEntry(p)
    BY DEF LogStorageTypes, ProposalEntryTypes
<1>2. Result(p) \subseteq Entries /\ Coherent(Result(p))
    BY SMT, <1>1 DEF ValidProposalEntry, Result
<1> QED BY SMT, <1>1, <1>2 DEF Publish

THEOREM CandidateHasTypedInputEntries ==
    ASSUME ProofInvariant, CommitEvidenceSound
    PROVE /\ LogStorageTypes /\ ProposalEntryTypes
          /\ \A o \in offers : o.entry \in Entries
          /\ \A m \in commitMessages : m.entry \in Entries
<1>1. LogStorageTypes /\ ProposalEntryTypes
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, LogStorageTypes, ProposalEntryTypes, ValidProposalEntry
<1>2. \A o \in offers : o.entry \in Entries
    BY SMT DEF ProofInvariant, OfferProvenance, CanonicalViewLinks, PreProvenanceInvariant,
       RecoveryInvariant, CanonicalShape
<1>3. \A f \in commitHistory : f.epoch \in Terms /\ f.entry \in canonical[f.epoch]
    BY EvidenceIsPossible, EvidenceHasCanonicalSource
<1>4. \A m \in commitMessages : m.entry \in Entries
    BY SMT, <1>3 DEF ProofInvariant, KnowledgeInvariant, CommitMessageEvidence,
       PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1> QED BY <1>1, <1>2, <1>4

THEOREM ReceivingKeepsFormalCoherent ==
    ASSUME ProofInvariant, NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
    PROVE Coherent(formal[r] \cup {o.entry})
<1>1. o \in offers /\ Aligned(r, term[r]) /\ o.epoch = term[r]
    BY DEF ReceiveEntry, CanReceive
<1>20. term[r] \in Terms /\ Sublog(formal[r])
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, CanonicalShape
<1>21. formal[r] # {} /\ LastTerm(formal[r]) = term[r]
    BY AlignmentIdentifiesSublogEpoch, <1>1, <1>20
<1>2. LastTerm(formal[r]) = term[r] /\ formal[r] \subseteq canonical[term[r]]
    BY ONLY SMT, <1>20, <1>21 DEF Sublog
<1>30. PICK v \in leaderViews : v.epoch = o.epoch /\ o.entry \in v.entries
    BY <1>1 DEF ProofInvariant, OfferProvenance
<1>31. v.entries \subseteq canonical[v.epoch] /\ Coherent(canonical[term[r]])
    BY <1>20, <1>30 DEF ProofInvariant, CanonicalViewLinks, PreProvenanceInvariant, RecoveryInvariant, CanonicalShape
<1>3. o.entry \in canonical[term[r]] /\ term[r] \in Terms /\ Coherent(canonical[term[r]])
    BY ONLY SMT, <1>1, <1>20, <1>30, <1>31
<1>4. formal[r] \cup {o.entry} \subseteq canonical[term[r]]
    BY ONLY <1>2, <1>3
<1> QED BY ONLY CoherenceInheritedBySubset, <1>3, <1>4

THEOREM BuildRecoveryKeepsLogTypes ==
    ASSUME ProofInvariant, NEW c \in Replicas, NEW selected, BuildRecovery(c, selected)
    PROVE LogStorageTypes' /\ ProposalEntryTypes'
<1>1. LogStorageTypes /\ ProposalEntryTypes
    BY DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK, LogStorageTypes, ProposalEntryTypes, ValidProposalEntry
<1>2. CreatedRecoveryProposal(c, selected) \in ProposalRecords
      /\ Coherent(Result(CreatedRecoveryProposal(c, selected)))
    BY RecoveryCreationIsTypedAndCoherent
<1>3. RecoveryCreatedEntry(c, selected) \in Entries
    BY SMT, <1>2 DEF CreatedRecoveryProposal, Proposal, ProposalRecords
<1>4. proposals' = proposals \cup {CreatedRecoveryProposal(c, selected)}
      /\ stored' = [stored EXCEPT ![c] = @ \cup {RecoveryCreatedEntry(c, selected)}]
      /\ UNCHANGED <<formal, knownCommitted, applied, retained>>
    BY DEF BuildRecovery, CreatedRecoveryProposal, RecoveryCreatedEntry
<1>5. LogStorageTypes'
    BY ONLY SMT, <1>1, <1>3, <1>4 DEF LogStorageTypes
<1>60. ValidProposalEntry(CreatedRecoveryProposal(c, selected))
    BY SMT, <1>2 DEF ValidProposalEntry, CreatedRecoveryProposal, RecoveryCreatedEntry,
       Proposal, Entry, ProposalRecords
<1>6. ProposalEntryTypes'
    BY ONLY SMT, <1>1, <1>4, <1>60 DEF ProposalEntryTypes
<1> QED BY <1>5, <1>6

THEOREM LogTypesInductiveStep ==
    ASSUME ProofInvariant, CommitEvidenceSound, ProtocolNext
    PROVE LogStorageTypes' /\ ProposalEntryTypes'
<1>1. LogStorageTypes /\ ProposalEntryTypes
      /\ (\A o \in offers : o.entry \in Entries)
      /\ (\A m \in commitMessages : m.entry \in Entries)
      /\ (\A r \in Replicas : current[r] = NoProposal \/ current[r] \in proposals)
    BY CandidateHasTypedInputEntries DEF ProofInvariant, PreProvenanceInvariant, RecoveryInvariant, TypeOK
<1>2. \A c \in Replicas : \A selected : BuildRecovery(c, selected) =>
          LogStorageTypes' /\ ProposalEntryTypes'
    BY BuildRecoveryKeepsLogTypes
<1>3. \A c \in Replicas : \A v : CreateEntry(c, v) =>
          LogStorageTypes' /\ ProposalEntryTypes'
    <2>1. ASSUME NEW c \in Replicas, NEW v, CreateEntry(c, v)
          PROVE LogStorageTypes' /\ ProposalEntryTypes'
        <3>1. NormalCreatedEntry(c, v, "data", FALSE) \in Entries
              /\ Coherent(formal[c] \cup {NormalCreatedEntry(c, v, "data", FALSE)})
            BY NormalCreationIsTypedAndCoherent, <2>1
        <3>2. formal' = [formal EXCEPT ![c] = @ \cup {NormalCreatedEntry(c, v, "data", FALSE)}]
              /\ stored' = [stored EXCEPT ![c] = @ \cup {NormalCreatedEntry(c, v, "data", FALSE)}]
              /\ UNCHANGED <<knownCommitted, applied, retained, proposals>>
            BY <2>1 DEF CreateEntry, NormalCreatedEntry
        <3> QED BY ONLY AppendedFormalStorageTypes, <1>1, <2>1, <3>1, <3>2
    <2> QED BY <2>1
<1>4. \A c \in Replicas : \A v, k : CreateSuccessor(c, v, k) =>
          LogStorageTypes' /\ ProposalEntryTypes'
    <2>1. ASSUME NEW c \in Replicas, NEW v, NEW k, CreateSuccessor(c, v, k)
          PROVE LogStorageTypes' /\ ProposalEntryTypes'
        <3>1. NormalCreatedEntry(c, v, k, TRUE) \in Entries
              /\ Coherent(formal[c] \cup {NormalCreatedEntry(c, v, k, TRUE)})
            BY NormalCreationIsTypedAndCoherent, <2>1
        <3>2. formal' = [formal EXCEPT ![c] = @ \cup {NormalCreatedEntry(c, v, k, TRUE)}]
              /\ stored' = [stored EXCEPT ![c] = @ \cup {NormalCreatedEntry(c, v, k, TRUE)}]
              /\ UNCHANGED <<knownCommitted, applied, retained, proposals>>
            BY <2>1 DEF CreateSuccessor, NormalCreatedEntry
        <3> QED BY ONLY AppendedFormalStorageTypes, <1>1, <2>1, <3>1, <3>2
    <2> QED BY <2>1
<1>5. \A r \in Replicas : \A o : ReceiveEntry(r, o) => LogStorageTypes' /\ ProposalEntryTypes'
    <2>1. ASSUME NEW r \in Replicas, NEW o, ReceiveEntry(r, o)
          PROVE LogStorageTypes' /\ ProposalEntryTypes'
        <3>1. o.entry \in Entries /\ Coherent(formal[r] \cup {o.entry})
            BY ReceivingKeepsFormalCoherent, <1>1, <2>1 DEF ReceiveEntry
        <3>2. formal' = [formal EXCEPT ![r] = @ \cup {o.entry}]
              /\ stored' = [stored EXCEPT ![r] = @ \cup {o.entry}]
              /\ UNCHANGED <<knownCommitted, applied, retained, proposals>>
            BY <2>1 DEF ReceiveEntry
        <3> QED BY ONLY AppendedFormalStorageTypes, <1>1, <2>1, <3>1, <3>2
    <2> QED BY <2>1
<1>6. \A r, s \in Replicas : \A p, e : CopyProposalEntry(r, s, p, e) => LogStorageTypes' /\ ProposalEntryTypes'
    BY SMT, <1>1 DEF CopyProposalEntry, LogStorageTypes, ProposalEntryTypes
<1>7. \A r \in Replicas : \A p : RetainProposal(r, p) => LogStorageTypes' /\ ProposalEntryTypes'
    BY SMT, <1>1 DEF RetainProposal, LogStorageTypes, ProposalEntryTypes
<1>8. \A c \in Replicas : ConfirmProposal(c) => LogStorageTypes' /\ ProposalEntryTypes'
    <2>1. ASSUME NEW c \in Replicas, ConfirmProposal(c)
          PROVE LogStorageTypes' /\ ProposalEntryTypes'
        <3>1. current[c] \in proposals
            BY SMT, <1>1, <2>1 DEF ConfirmProposal
        <3>2. Publish(c, current[c]) \subseteq Entries /\ Coherent(Publish(c, current[c]))
            BY PublishedLogTypes, <1>1, <2>1, <3>1
        <3>3. formal' = [formal EXCEPT ![c] = Publish(c, current[c])]
              /\ UNCHANGED <<stored, knownCommitted, applied, retained, proposals>>
            BY <2>1 DEF ConfirmProposal
        <3> QED BY ONLY ReplacedFormalTypes, <1>1, <2>1, <3>2, <3>3
    <2> QED BY <2>1
<1>9. \A r \in Replicas : \A p : LearnConfirmation(r, p) => LogStorageTypes' /\ ProposalEntryTypes'
    <2>1. ASSUME NEW r \in Replicas, NEW p, LearnConfirmation(r, p)
          PROVE LogStorageTypes' /\ ProposalEntryTypes'
        <3>1. p \in proposals
            BY SMT, <1>1, <2>1 DEF LearnConfirmation, LogStorageTypes
        <3>2. Publish(r, p) \subseteq Entries /\ Coherent(Publish(r, p))
            BY PublishedLogTypes, <1>1, <2>1, <3>1
        <3>3. formal' = [formal EXCEPT ![r] = Publish(r, p)]
              /\ UNCHANGED <<stored, knownCommitted, applied, retained, proposals>>
            BY <2>1 DEF LearnConfirmation
        <3> QED BY ONLY ReplacedFormalTypes, <1>1, <2>1, <3>2, <3>3
    <2> QED BY <2>1
<1>10. \A c \in Replicas : \A e : CommitEntry(c, e) => LogStorageTypes' /\ ProposalEntryTypes'
    BY SMT, <1>1 DEF CommitEntry, LogStorageTypes, ProposalEntryTypes
<1>11. \A r \in Replicas : \A m : LearnCommit(r, m) => LogStorageTypes' /\ ProposalEntryTypes'
    BY SMT, <1>1 DEF LearnCommit, LogStorageTypes, ProposalEntryTypes
<1>12. \A r \in Replicas : \A e : ApplyEntry(r, e) => LogStorageTypes' /\ ProposalEntryTypes'
    BY SMT, <1>1 DEF ApplyEntry, LogStorageTypes, ProposalEntryTypes
<1>13. UNCHANGED LogTypeVars => LogStorageTypes' /\ ProposalEntryTypes'
    BY SMT, <1>1 DEF LogTypeVars, LogStorageTypes, ProposalEntryTypes
<1>14. LogTypeChanges \/ UNCHANGED LogTypeVars
    BY LogTypeActionProjection
<1> QED BY ONLY SMT, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14 DEF LogTypeChanges
=============================================================================
