-------------------- MODULE TRaftApplicationPrefixTemporal -------------------
EXTENDS TRaftApplicationPrefixProof, TRaftProtocolSafety, TRaftPointLiftInvariant


THEOREM PrefixLiftParameters ==
    /\ PointLift!ParameterAssumptions
    /\ PointLift!SentinelSeparation
    /\ PointLift!ClientParameters
BY ONLY PointLiftParameters

THEOREM PrefixLiftStateIdentity ==
    PointLift!ProofInvariant <=> LiftedSafety!ProofInvariant
BY ONLY PointLiftStateIdentities

THEOREM PrefixLiftInterfaceIdentities ==
    /\ PointLift!AppliedPrefixClosure = AppliedPrefixClosure
    /\ PointLift!AppliedEntriesPreserved = AppliedEntriesPreserved
    /\ PointLift!EntryContextUnique = EntryContextUnique
BY ONLY
   DEF PointLift!AppliedEntriesPreserved, AppliedEntriesPreserved,
       PointLift!AppliedPrefixClosure, AppliedPrefixClosure, PointLift!EntryContextUnique,
       EntryContextUnique, PointLift!Prefix, Prefix, PointLift!PrefixClosed, PrefixClosed,
       PointLift!IsFiniteSet, IsFiniteSet, PointLift!Cardinality, Cardinality

THEOREM PrefixLiftNextIdentity ==
    /\ PointLift!Next = Next
BY ONLY PointCoreAliasNext

THEOREM ApplicationPrefixesAlwaysClosed == Spec => []AppliedPrefixClosure
<1>1. Spec => []LiftedSafety!Inv
    BY ProtocolInvariant
<1>2. Init => AppliedPrefixClosure
    BY AppliedPrefixClosureInitially
<1>3. AppliedPrefixClosure /\ LiftedSafety!Inv /\ LiftedSafety!Inv'
      /\ [Next]_vars => AppliedPrefixClosure'
    <2>1. ASSUME AppliedPrefixClosure, LiftedSafety!Inv, LiftedSafety!Inv', Next
          PROVE AppliedPrefixClosure'
        <3>1. PrefixLiftStateIdentity' /\ PrefixLiftInterfaceIdentities'
            BY ONLY PTL, PrefixLiftStateIdentity, PrefixLiftInterfaceIdentities
        <3>2. LiftedSafetyPredicateIdentity'
            BY ONLY PTL, LiftedSafetyPredicateIdentity
        <3> QED BY PointLift!AppliedPrefixClosureInductiveStep, PrefixLiftParameters,
             PrefixLiftStateIdentity, PrefixLiftInterfaceIdentities, PrefixLiftNextIdentity,
             LiftedSafetyPredicateIdentity, <2>1, <3>1, <3>2
             DEF LiftedSafety!Inv, Safety, PointLift!ParameterAssumptions,
                 PointLift!SentinelSeparation, PointLift!ClientParameters
    <2>2. AppliedPrefixClosure /\ UNCHANGED vars => AppliedPrefixClosure'
        BY SMT DEF AppliedPrefixClosure, PrefixClosed, vars, protocolVars
    <2> QED BY <2>1, <2>2
<1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
=============================================================================
