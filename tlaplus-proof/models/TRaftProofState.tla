-------------------------- MODULE TRaftProofState ----------------------------
EXTENDS TRaftControlState, TRaftFiniteState, TRaftOfferState, TRaftCommitState,
        TRaftLeaderHistoryState, TRaftHistoryOriginState, TRaftContextOriginState, TRaftClosedHistoryState, TRaftPrefixEvidenceState, TRaftCertifiedSourceState, TRaftAckSourceState

\* Conservative history extension. Neither canonical nor these predicates is
\* consulted by any protocol action. A failed invariant is a failed proof
\* candidate, not permission to discard a protocol behavior.
VARIABLE canonical
proofVars == <<vars, canonical>>
GhostInit == canonical = [t \in Terms |-> {}]
GhostNext == canonical' = [t \in Terms |-> canonical[t] \cup
    (UNION {Result(p) : p \in {q \in proposals' : q.epoch = t}}) \cup
    (UNION {formal'[r] : r \in {s \in Replicas :
                                  role'[s] = "Leader" /\ term'[s] = t}})]
ProofInit == Init /\ GhostInit
ProofNext == Next /\ GhostNext
ProofSpec == ProofInit /\ [][ProofNext]_proofVars

ProposedAt(P, t) == (UNION {Result(p) : p \in {q \in P : q.epoch = t}})
ViewedAt(V, t) == (UNION {v.entries : v \in {w \in V : w.epoch = t}})
DerivedCanonical == [t \in Terms |-> ProposedAt(proposals, t) \cup ViewedAt(leaderViews, t)]
CanonicalDefinition == canonical = DerivedCanonical

IssuedEntries == (UNION {a.contents : a \in ackMessages})
EpochAckers(t, e) == {r \in Replicas : \E a \in ackMessages :
                          a.sender = r /\ a.epoch = t /\ e \in a.contents}
PossibleAckers(t, e) == EpochAckers(t, e) \cup {r \in Replicas : term[r] <= t}
MayChoose(t, e) == Quorum(PossibleAckers(t, e))
ReportContents(m) == m.entries \cup (UNION {Result(p) : p \in m.pending})
RetainedContents(r) == (UNION {Result(p) : p \in retained[r]})

ContextSound(L) == \A e \in L : \E ctx \in entryContexts :
    ctx.entry = e /\ Prefix(L, e.part - 1) = ctx.prefix

Sublog(L) == L = {} \/
    LET t == LastTerm(L)
    IN /\ t \in Terms
       /\ L \subseteq canonical[t]
       /\ \E p \in proposals : p.epoch = t /\ Result(p) \subseteq L
       /\ Prefix(L, Cur(L) - 1) = Prefix(canonical[t], Cur(L) - 1)

CanonicalShape ==
    /\ canonical \in [Terms -> SUBSET Entries]
    /\ \A t \in Terms :
         /\ Coherent(canonical[t]) /\ ContextSound(canonical[t])
         /\ \A e \in canonical[t] : e.term <= t
         /\ \A q \in Partitions : Count(canonical[t], q) <= MaxPartitionSize
         /\ \A p \in proposals : p.epoch = t =>
              /\ Result(p) \subseteq canonical[t]
              /\ Prefix(canonical[t], p.first.part - 1) = p.prefix
              /\ \A e \in canonical[t] \ Result(p) :
                   e.term = t /\ e.index > p.first.index /\ e.part >= p.first.part
    /\ \A p, q \in proposals : p.epoch = q.epoch => p = q
    /\ \A r \in Replicas :
         /\ Sublog(formal[r]) /\ ContextSound(formal[r])
         /\ \A e \in formal[r] : e.term <= term[r]
         /\ role[r] = "Leader" => formal[r] = canonical[term[r]]
    /\ \A m \in reportMessages : Sublog(m.entries) /\ ContextSound(m.entries)

TermAndVoteFacts ==
    /\ \A v \in voteMessages :
         /\ v.sender \in Replicas /\ v.receiver \in Replicas
         /\ v.epoch \in Terms \ {0} /\ v.epoch <= term[v.sender]
         /\ v.epoch = term[v.sender] => vote[v.sender] = v.receiver
    /\ \A a, b \in voteMessages :
         a.sender = b.sender /\ a.epoch = b.epoch => a.receiver = b.receiver
    /\ \A w \in winners :
         Quorum({v.sender : v \in {a \in voteMessages :
                         a.epoch = w.epoch /\ a.receiver = w.node}})
    /\ \A r \in Replicas : role[r] \in {"LeaderCandidate", "Leader"} =>
          [node |-> r, epoch |-> term[r]] \in winners
    /\ \A p \in proposals : [node |-> p.owner, epoch |-> p.epoch] \in winners
    /\ \A m \in reportMessages : m.epoch <= term[m.sender]

AckOrigin == \A a \in ackMessages :
    /\ a.sender \in Replicas /\ a.receiver \in Replicas
    /\ a.epoch \in Terms \ {0} /\ a.epoch <= term[a.sender]
    /\ a.contents \subseteq canonical[a.epoch]
    /\ \E p \in retained[a.sender] :
         /\ p.epoch = a.epoch /\ p.owner = a.receiver
         /\ \/ a.contents = Result(p)
            \/ /\ a.contents = {a.target} /\ a.target.term = a.epoch
               /\ a.target.part >= p.first.part

ReportFences ==
    /\ \A r \in Replicas : \A p \in retained[r] : p.epoch <= term[r]
    /\ \A m \in reportMessages :
         /\ m.sender \in Replicas /\ m.epoch \in Terms \ {0}
         /\ m.pending \subseteq retained[m.sender]
         /\ \A p \in retained[m.sender] : p.epoch < m.epoch => p \in m.pending
    /\ \A c \in Replicas : \A r \in Reporters(c) :
         /\ reports[c][r].sender = r /\ reports[c][r].receiver = c
         /\ reports[c][r].epoch = term[c]
    /\ \A p \in proposals : Quorum({r \in Replicas : term[r] >= p.epoch})

PotentialCoverage ==
    /\ \A a \in ackMessages : \A e \in a.contents :
         MayChoose(a.epoch, e) =>
             e \in formal[a.sender] \cup RetainedContents(a.sender)
    /\ \A m \in reportMessages, a \in ackMessages : \A e \in a.contents :
         (/\ a.sender = m.sender /\ a.epoch < m.epoch /\ MayChoose(a.epoch, e))
         => e \in ReportContents(m)

PotentialPreservation ==
    /\ \A p \in proposals, t \in Terms, e \in IssuedEntries :
         t < p.epoch /\ MayChoose(t, e) => e \in p.prefix
    /\ \A v \in leaderViews, t \in Terms, e \in IssuedEntries :
         t < v.epoch /\ MayChoose(t, e) => e \in v.entries

\* Snapshot/anchor links needed to justify the recovery union. These are
\* candidate induction conjuncts, never protocol enabling conditions.
RecoveryOriginFacts ==
    /\ \A r \in Replicas : formal[r] # {} =>
          \E p \in retained[r] : p.epoch = LastTerm(formal[r]) /\ Result(p) \subseteq formal[r]
    /\ \A m \in reportMessages :
          /\ \A p \in m.pending : p.epoch <= m.epoch
          /\ m.entries # {} =>
                \E p \in m.pending : p.epoch = LastTerm(m.entries) /\ Result(p) \subseteq m.entries
    /\ \A t \in Terms : canonical[t] # {} => \E p \in proposals : p.epoch = t

RecoveryInvariant == /\ TypeOK /\ TermAndVoteFacts /\ CanonicalShape
                  /\ AckOrigin /\ ReportFences /\ PotentialCoverage
                  /\ PotentialPreservation
PreProvenanceInvariant == /\ RecoveryInvariant /\ ElectionInvariant /\ ControlInvariant
                  /\ DurabilityInvariant /\ FiniteLogInvariant /\ RecoveryOriginFacts
CanonicalFinite == \A t \in Terms : IsFiniteSet(canonical[t])
CanonicalViewLinks == \A v \in leaderViews :
    v.epoch \in Terms /\ v.entries \subseteq canonical[v.epoch]
PreBoundaryInvariant == /\ PreProvenanceInvariant /\ CanonicalFinite /\ CanonicalViewLinks
                  /\ OfferProvenance /\ KnowledgeInvariant
\* Counts are metadata from the creator's preceding partition, not arbitrary
\* values in Entries. This is a proof candidate, never a receive/send guard.
EntryBoundaryCounts == \A ctx \in entryContexts :
    ctx.entry.prevSize = Count(ctx.prefix, ctx.entry.part - 1)
PreActivationInvariant == /\ PreProvenanceInvariant /\ CanonicalFinite /\ CanonicalViewLinks
                  /\ OfferProvenance /\ KnowledgeInvariant /\ EntryBoundaryCounts
PreHistoryOriginInvariant == /\ PreProvenanceInvariant /\ CanonicalFinite /\ CanonicalViewLinks
                  /\ OfferProvenance /\ KnowledgeInvariant /\ EntryBoundaryCounts
                  /\ LeaderHistoryInvariant /\ CanonicalDefinition

\* Historical records must have an actual source; these are observer facts,
\* not protocol guards. The legacy predicate is retained for diagnostic replay.
PreClosedHistoryInvariant == /\ PreProvenanceInvariant /\ CanonicalFinite /\ CanonicalViewLinks
                  /\ OfferProvenance /\ KnowledgeInvariant /\ EntryBoundaryCounts
                  /\ LeaderHistoryInvariant /\ CanonicalDefinition
                  /\ HistoryOriginInvariant /\ ContextOrigins(canonical, entryContexts)

PreEvidenceOrderInvariant == /\ PreProvenanceInvariant /\ CanonicalFinite /\ CanonicalViewLinks
                  /\ OfferProvenance /\ KnowledgeInvariant /\ EntryBoundaryCounts
                  /\ LeaderHistoryInvariant /\ CanonicalDefinition
                  /\ HistoryOriginInvariant /\ ContextOrigins(canonical, entryContexts)
                  /\ HistoryPartitionCompleteness

PreCertifiedHistoryInvariant == /\ PreProvenanceInvariant /\ CanonicalFinite /\ CanonicalViewLinks
                  /\ OfferProvenance /\ KnowledgeInvariant /\ EntryBoundaryCounts
                  /\ LeaderHistoryInvariant /\ CanonicalDefinition
                  /\ HistoryOriginInvariant /\ ContextOrigins(canonical, entryContexts)
                  /\ HistoryPartitionCompleteness /\ PrefixEvidenceInvariant

ProofInvariant == /\ PreProvenanceInvariant /\ CanonicalFinite /\ CanonicalViewLinks
                  /\ OfferProvenance /\ KnowledgeInvariant /\ EntryBoundaryCounts
                  /\ LeaderHistoryInvariant /\ CanonicalDefinition
                  /\ HistoryOriginInvariant /\ ContextOrigins(canonical, entryContexts)
                  /\ HistoryPartitionCompleteness
                  /\ PrefixEvidenceInvariant
                  /\ InstalledEntriesHaveSource /\ CertifiedPartitionHistory
                  /\ MessageSourceInvariant
=============================================================================
