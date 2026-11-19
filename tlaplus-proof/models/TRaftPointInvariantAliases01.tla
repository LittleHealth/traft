---------------------- MODULE TRaftPointInvariantAliases01 ----------------------
EXTENDS TRaftPointCoreAliases11, TRaftLiftedCoreAliases08b

\* Local definition equalities between the same history substitutions.
\* Each equality and every imported theorem require independent checking.

THEOREM PointInvariantAliasAck ==
    \A r, c, t, e, L : PointLift!Ack(r, c, t, e, L) = LiftedSafety!Ack(r, c, t, e, L)
BY ONLY ZenonT(10), PointCoreAliasAck, LiftedCoreAliasAck

THEOREM PointInvariantAliasAckDurability ==
    PointLift!AckDurability = LiftedSafety!AckDurability
BY ONLY ZenonT(10)
   DEF PointLift!AckDurability, LiftedSafety!AckDurability

THEOREM PointInvariantAliasResult ==
    \A p : PointLift!Result(p) = LiftedSafety!Result(p)
BY ONLY ZenonT(10), PointCoreAliasResult, LiftedCoreAliasResult

THEOREM PointInvariantAliasAckHasSource ==
    \A a, P, O : PointLift!AckHasSource(a, P, O) = LiftedSafety!AckHasSource(a, P, O)
BY ONLY ZenonT(10), PointInvariantAliasAck, PointInvariantAliasResult
   DEF PointLift!AckHasSource, LiftedSafety!AckHasSource

THEOREM PointInvariantAliasAckInboxOrigins ==
    PointLift!AckInboxOrigins = LiftedSafety!AckInboxOrigins
BY ONLY ZenonT(10)
   DEF PointLift!AckInboxOrigins, LiftedSafety!AckInboxOrigins

THEOREM PointInvariantAliasTerms ==
    PointLift!Terms = LiftedSafety!Terms
BY ONLY ZenonT(10), PointCoreAliasTerms, LiftedCoreAliasTerms

THEOREM PointInvariantAliasAckOrigin ==
    PointLift!AckOrigin = LiftedSafety!AckOrigin
BY ONLY ZenonT(10), PointInvariantAliasResult, PointInvariantAliasTerms
   DEF PointLift!AckOrigin, LiftedSafety!AckOrigin

THEOREM PointInvariantAliasKnownBy ==
    \A H, t, e : PointLift!KnownBy(H, t, e) = LiftedSafety!KnownBy(H, t, e)
BY ONLY ZenonT(10)
   DEF PointLift!KnownBy, LiftedSafety!KnownBy

THEOREM PointInvariantAliasAckPrefixEvidence ==
    \A A, E, H : PointLift!AckPrefixEvidence(A, E, H) = LiftedSafety!AckPrefixEvidence(A, E, H)
BY ONLY ZenonT(10), PointInvariantAliasKnownBy
   DEF PointLift!AckPrefixEvidence, LiftedSafety!AckPrefixEvidence

THEOREM PointInvariantAliasAckSendersValid ==
    PointLift!AckSendersValid = LiftedSafety!AckSendersValid
BY ONLY ZenonT(10)
   DEF PointLift!AckSendersValid, LiftedSafety!AckSendersValid

THEOREM PointInvariantAliasAckSourceInvariant ==
    PointLift!AckSourceInvariant = LiftedSafety!AckSourceInvariant
BY ONLY ZenonT(10), PointInvariantAliasAckHasSource
   DEF PointLift!AckSourceInvariant, LiftedSafety!AckSourceInvariant

THEOREM PointInvariantAliasActiveControlCertified ==
    PointLift!ActiveControlCertified = LiftedSafety!ActiveControlCertified
BY ONLY ZenonT(10)
   DEF PointLift!ActiveControlCertified, LiftedSafety!ActiveControlCertified

THEOREM PointInvariantAliasLeaderViewsCertified ==
    PointLift!LeaderViewsCertified = LiftedSafety!LeaderViewsCertified
BY ONLY ZenonT(10)
   DEF PointLift!LeaderViewsCertified, LiftedSafety!LeaderViewsCertified

THEOREM PointInvariantAliasActiveRecoveryCertificates ==
    PointLift!ActiveRecoveryCertificates = LiftedSafety!ActiveRecoveryCertificates
BY ONLY ZenonT(10), PointInvariantAliasActiveControlCertified, PointInvariantAliasLeaderViewsCertified
   DEF PointLift!ActiveRecoveryCertificates, LiftedSafety!ActiveRecoveryCertificates

THEOREM PointInvariantAliasAppliedEvidence ==
    PointLift!AppliedEvidence = LiftedSafety!AppliedEvidence
BY ONLY ZenonT(10)
   DEF PointLift!AppliedEvidence, LiftedSafety!AppliedEvidence

THEOREM PointInvariantAliasAppliedPartitionOrigins ==
    PointLift!AppliedPartitionOrigins = LiftedSafety!AppliedPartitionOrigins
BY ONLY ZenonT(10)
   DEF PointLift!AppliedPartitionOrigins, LiftedSafety!AppliedPartitionOrigins

THEOREM PointInvariantAliasBallotVoters ==
    \A M, t, c : PointLift!BallotVoters(M, t, c) = LiftedSafety!BallotVoters(M, t, c)
BY ONLY ZenonT(10)
   DEF PointLift!BallotVoters, LiftedSafety!BallotVoters

THEOREM PointInvariantAliasCardinality ==
    \A S : PointLift!Cardinality(S) = LiftedSafety!Cardinality(S)
BY ONLY ZenonT(10), PointCoreAliasCardinality, LiftedCoreAliasCardinality

THEOREM PointInvariantAliasQuorum ==
    \A S : PointLift!Quorum(S) = LiftedSafety!Quorum(S)
BY ONLY ZenonT(10), PointCoreAliasQuorum, LiftedCoreAliasQuorum

THEOREM PointInvariantAliasBallotCertificates ==
    \A W, M : PointLift!BallotCertificates(W, M) = LiftedSafety!BallotCertificates(W, M)
BY ONLY ZenonT(10), PointInvariantAliasBallotVoters, PointInvariantAliasQuorum, PointInvariantAliasTerms
   DEF PointLift!BallotCertificates, LiftedSafety!BallotCertificates

THEOREM PointInvariantAliasProposedAt ==
    \A P, t : PointLift!ProposedAt(P, t) = LiftedSafety!ProposedAt(P, t)
BY ONLY ZenonT(10), PointInvariantAliasResult
   DEF PointLift!ProposedAt, LiftedSafety!ProposedAt

THEOREM PointInvariantAliasViewedAt ==
    \A V, t : PointLift!ViewedAt(V, t) = LiftedSafety!ViewedAt(V, t)
BY ONLY ZenonT(10)
   DEF PointLift!ViewedAt, LiftedSafety!ViewedAt

THEOREM PointInvariantAliasDerivedCanonical ==
    PointLift!DerivedCanonical = LiftedSafety!DerivedCanonical
BY ONLY ZenonT(10), PointInvariantAliasProposedAt, PointInvariantAliasTerms, PointInvariantAliasViewedAt
   DEF PointLift!DerivedCanonical, LiftedSafety!DerivedCanonical

THEOREM PointInvariantAliasCanonicalDefinition ==
    PointLift!CanonicalDefinition = LiftedSafety!CanonicalDefinition
BY ONLY ZenonT(10), PointInvariantAliasDerivedCanonical
   DEF PointLift!CanonicalDefinition, LiftedSafety!CanonicalDefinition

THEOREM PointInvariantAliasIsFiniteSet ==
    \A S : PointLift!IsFiniteSet(S) = LiftedSafety!IsFiniteSet(S)
BY ONLY ZenonT(10), PointCoreAliasIsFiniteSet, LiftedCoreAliasIsFiniteSet

THEOREM PointInvariantAliasCanonicalFinite ==
    PointLift!CanonicalFinite = LiftedSafety!CanonicalFinite
BY ONLY ZenonT(10), PointInvariantAliasIsFiniteSet, PointInvariantAliasTerms
   DEF PointLift!CanonicalFinite, LiftedSafety!CanonicalFinite

THEOREM PointInvariantAliasCoherent ==
    \A L : PointLift!Coherent(L) = LiftedSafety!Coherent(L)
BY ONLY ZenonT(10), PointCoreAliasCoherent, LiftedCoreAliasCoherent

THEOREM PointInvariantAliasPrefix ==
    \A L, p : PointLift!Prefix(L, p) = LiftedSafety!Prefix(L, p)
BY ONLY ZenonT(10), PointCoreAliasPrefix, LiftedCoreAliasPrefix

THEOREM PointInvariantAliasContextSound ==
    \A L : PointLift!ContextSound(L) = LiftedSafety!ContextSound(L)
BY ONLY ZenonT(10), PointInvariantAliasPrefix
   DEF PointLift!ContextSound, LiftedSafety!ContextSound

THEOREM PointInvariantAliasPart ==
    \A L, p : PointLift!Part(L, p) = LiftedSafety!Part(L, p)
BY ONLY ZenonT(10), PointCoreAliasPart, LiftedCoreAliasPart

=============================================================================
