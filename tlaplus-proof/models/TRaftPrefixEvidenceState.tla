----------------------- MODULE TRaftPrefixEvidenceState ----------------------
EXTENDS TRaftEpochKnowledgeState

\* Candidate source facts for the partition-order argument. None is a guard.
\* All their Init/Next obligations must be checked before using full Safety.
FollowerPrefixEvidence(F, T, R, H) ==
    \A r \in Replicas : \A p \in R[r] :
        p.epoch = T[r] /\ p.owner # r =>
            \A e \in F[r] : e.term = T[r] =>
                \A x \in Prefix(F[r], e.part - 1) : KnownBy(H, T[r], x)

OfferCountEvidence(O, E, H) ==
    \A o \in O, ctx \in E : ctx.entry = o.entry =>
        \E S \in SUBSET Part(ctx.prefix, o.entry.part - 1) :
            /\ IsFiniteSet(S) /\ Cardinality(S) = o.committed
            /\ \A x \in S : KnownBy(H, o.epoch, x)

AckPrefixEvidence(A, E, H) ==
    \A a \in A, ctx \in E :
        (ctx.entry \in a.contents /\ (a.sender # a.receiver \/ a.contents # {a.target})) =>
            \A x \in ctx.prefix : x \in a.contents \/ KnownBy(H, a.epoch, x)

RecoveryProposalBoundaries(P) == \A p \in P :
    /\ p.first.kind = "noop"
    /\ \A e \in p.prefix : e.term < p.epoch

ActiveControlCertified == \A r \in Replicas :
    (role[r] = "Leader" \/ phase[r] = "commit") => current[r] \in confirmations
LeaderViewsCertified == \A v \in leaderViews : \E p \in confirmations : p.epoch = v.epoch
ActiveRecoveryCertificates == ActiveControlCertified /\ LeaderViewsCertified

PrefixEvidenceInvariant ==
    /\ EpochKnowledgeInvariant
    /\ FollowerPrefixEvidence(formal, term, retained, commitHistory)
    /\ OfferCountEvidence(offers, entryContexts, commitHistory)
    /\ AckPrefixEvidence(ackMessages, entryContexts, commitHistory)
    /\ RecoveryProposalBoundaries(proposals)
    /\ ActiveRecoveryCertificates
=============================================================================
