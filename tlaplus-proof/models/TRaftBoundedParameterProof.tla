----------------------- MODULE TRaftBoundedParameterProof --------------------
EXTENDS TRaftBoundedObserverState

THEOREM MappedFiniteSetIdentity ==
    \A S : MappedCore!IsFiniteSet(S) = IsFiniteSet(S)
BY ONLY ZenonT(10) DEF MappedCore!IsFiniteSet, IsFiniteSet

THEOREM MappedCardinalityIdentity ==
    \A S : MappedCore!Cardinality(S) = Cardinality(S)
BY ONLY ZenonT(10), MappedFiniteSetIdentity
   DEF MappedCore!Cardinality, Cardinality

THEOREM MappedIdentifierDomains ==
    /\ MappedCore!Terms = Nat
    /\ MappedCore!Indices = Nat \ {0}
    /\ MappedCore!Partitions = Nat
BY ONLY SMT DEF MappedCore!Terms, MappedCore!Indices, MappedCore!Partitions

\* A sentinel distinct from bounded records need not be distinct from all
\* unbounded records. State that constant-domain compatibility explicitly;
\* the TLC model-value sentinel satisfies it without a protocol guard.
THEOREM BoundedParametersAdmitUnboundedCore ==
    ASSUME Absent \notin Infinite!ProposalRecords
    PROVE MappedCore!ParameterAssumptions /\ MappedCore!SentinelSeparation
<1>0. Absent \notin Infinite!ProposalRecords
    OBVIOUS
<1>1. MappedCore!NoNode = NoNode
    BY ONLY DEF MappedCore!NoNode, NoNode
<1>2. MappedCore!ParameterAssumptions
    BY ONLY SMT, ParameterAssumptions, MappedFiniteSetIdentity,
       MappedCardinalityIdentity, MappedIdentifierDomains, <1>1
       DEF ParameterAssumptions, MappedCore!ParameterAssumptions
<1>3. MappedCore!ProposalRecords = Infinite!ProposalRecords
    BY ONLY ZenonT(10)
       DEF MappedCore!ProposalRecords, Infinite!ProposalRecords,
           MappedCore!Entries, Infinite!Entries, MappedCore!Terms, Infinite!Terms,
           MappedCore!Indices, Infinite!Indices, MappedCore!Partitions, Infinite!Partitions
<1>4. MappedCore!SentinelSeparation
    BY ONLY <1>0, <1>3 DEF MappedCore!SentinelSeparation
<1> QED BY ONLY <1>2, <1>4
=============================================================================
