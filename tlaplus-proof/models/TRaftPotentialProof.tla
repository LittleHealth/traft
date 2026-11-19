-------------------------- MODULE TRaftPotentialProof ------------------------
EXTENDS TRaftStepProof
USE ParameterAssumptions DEF ParameterAssumptions

\* Conditional transition lemmas. Their premises are exposed explicitly;
\* they do not establish the still-open recovery induction by themselves.
THEOREM PossibleMajoritiesOnlyShrink ==
    ASSUME StepFacts, term \in [Replicas -> Nat], term' \in [Replicas -> Nat],
           NEW t \in Nat, NEW e, MayChoose(t, e)'
    PROVE MayChoose(t, e)
<1>1. Possible(Replicas, ackMessages', term', t, e)
          \subseteq Possible(Replicas, ackMessages, term, t, e)
    BY PossibleAckersShrink DEF StepFacts
<1>2. Majority(Replicas, Possible(Replicas, ackMessages', term', t, e))
    BY DEF MayChoose, Quorum, PossibleAckers, EpochAckers, Possible, Senders, Majority
<1>3. IsFiniteSet(Replicas) /\
      Possible(Replicas, ackMessages, term, t, e) \subseteq Replicas
    BY SMT DEF ParameterAssumptions, Possible, Senders
<1>4. Majority(Replicas, Possible(Replicas, ackMessages, term, t, e))
    BY ONLY MajorityUpward, <1>1, <1>2, <1>3
<1> QED BY ONLY <1>4
    DEF MayChoose, Quorum, PossibleAckers, EpochAckers, Possible, Senders, Majority

THEOREM OldPotentialEntryAlreadyIssued ==
    ASSUME term \in [Replicas -> Nat], NEW t \in Nat, NEW e,
           NEW later \in Nat, t < later,
           Quorum({r \in Replicas : term[r] >= later}), MayChoose(t, e)
    PROVE e \in IssuedEntries
<1>1. Majority(Replicas, {r \in Replicas : term[r] >= later})
      /\ Majority(Replicas, Possible(Replicas, ackMessages, term, t, e))
    BY DEF Quorum, MayChoose, PossibleAckers, EpochAckers, Majority, Possible, Senders
<1>2. \A r \in {s \in Replicas : term[s] >= later} : term[r] > t
    BY SMT
<1>3. \E r \in {s \in Replicas : term[s] >= later} :
              r \in Senders(Replicas, ackMessages, t, e)
    BY ReportQuorumHasOldAck, <1>1, <1>2
<1> QED BY SMT, <1>3 DEF Senders, IssuedEntries

THEOREM ExistingProposalsKeepPotentialEntries ==
    ASSUME PotentialPreservation, ReportFences, StepFacts,
           term \in [Replicas -> Nat], term' \in [Replicas -> Nat], Terms \subseteq Nat,
           \A p \in proposals : p.epoch \in Nat
    PROVE \A p \in proposals, t \in Terms, e \in IssuedEntries' :
              t < p.epoch /\ MayChoose(t, e)' => e \in p.prefix
<1>1. ASSUME NEW p \in proposals, NEW t \in Terms, NEW e \in IssuedEntries',
            t < p.epoch, MayChoose(t, e)'
      PROVE e \in p.prefix
    <2>1. MayChoose(t, e)
        BY PossibleMajoritiesOnlyShrink, <1>1
    <2>2. p.epoch \in Nat
        BY <1>1
    <2>3. Quorum({r \in Replicas : term[r] >= p.epoch})
        BY <1>1 DEF ReportFences
    <2>4. e \in IssuedEntries
        BY OldPotentialEntryAlreadyIssued, <1>1, <2>1, <2>2, <2>3
    <2> QED BY <1>1, <2>1, <2>4 DEF PotentialPreservation
<1> QED BY <1>1
=============================================================================
