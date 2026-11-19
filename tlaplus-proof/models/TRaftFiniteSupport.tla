------------------------- MODULE TRaftFiniteSupport --------------------------
EXTENDS TRaftFiniteState, TRaftFiniteLogProof, TRaftControlState, TRaftFunctionProof
USE ParameterAssumptions DEF ParameterAssumptions

THEOREM FiniteBinaryUnion ==
    ASSUME NEW S, NEW T, IsFiniteSet(S), IsFiniteSet(T)
    PROVE IsFiniteSet(S \cup T)
BY FS_Union, ZenonT(5)

THEOREM FiniteInsert ==
    ASSUME NEW S, NEW x, IsFiniteSet(S)
    PROVE IsFiniteSet(S \cup {x})
BY FS_AddElement, ZenonT(5)

THEOREM FiniteSubset ==
    ASSUME NEW S, NEW T, IsFiniteSet(S), T \subseteq S
    PROVE IsFiniteSet(T)
BY FS_Subset, ZenonT(5)

FiniteMap(F) == F = [r \in Replicas |-> F[r]] /\ \A r \in Replicas : IsFiniteSet(F[r])

THEOREM FiniteMapReplace ==
    ASSUME NEW F, FiniteMap(F), NEW r \in Replicas, NEW S, IsFiniteSet(S),
           NEW G, G = [F EXCEPT ![r] = S]
    PROVE FiniteMap(G)
<1>1. G = [x \in Replicas |-> G[x]]
    BY SMT, FunctionUpdatePreservesDomainShape DEF FiniteMap
<1>2. \A x \in Replicas : IsFiniteSet(G[x])
    BY SMT DEF FiniteMap
<1> QED BY <1>1, <1>2 DEF FiniteMap

THEOREM FiniteMapInsert ==
    ASSUME NEW F, FiniteMap(F), NEW r \in Replicas, NEW e,
           NEW G, G = [F EXCEPT ![r] = @ \cup {e}]
    PROVE FiniteMap(G)
<1>0. IsFiniteSet(F[r])
    BY DEF FiniteMap
<1>1. IsFiniteSet(F[r] \cup {e})
    BY FiniteInsert, <1>0
<1> QED BY FiniteMapReplace, <1>1

THEOREM FiniteImageUnion ==
    ASSUME NEW S, IsFiniteSet(S), NEW Op(_), \A x \in S : IsFiniteSet(Op(x))
    PROVE IsFiniteSet(UNION {Op(x) : x \in S})
<1>0. IsFiniteSet(S)
    OBVIOUS
<1>01. \A x \in S : IsFiniteSet(Op(x))
    OBVIOUS
<1>1. IsFiniteSet({Op(x) : x \in S})
    BY ONLY <1>0, FS_Image, IsaM("blast")
<1>2. \A T \in {Op(x) : x \in S} : IsFiniteSet(T)
    BY ONLY SMT, <1>01
<1> QED BY ONLY FS_UNION, <1>1, <1>2

THEOREM ReportedProposalsFiniteAndActual ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas
    PROVE IsFiniteSet(ReportedProposals(c)) /\ ReportedProposals(c) \subseteq proposals
<1>1. IsFiniteSet(Reporters(c))
    BY SMT, FS_Subset DEF Reporters
<1>2. \A r \in Reporters(c) :
          IsFiniteSet(reports[c][r].pending) /\ reports[c][r].pending \subseteq proposals
    BY SMT DEF ControlInvariant, CollectedReportProvenance, FiniteLogInvariant, FiniteSnapshots
<1>3. IsFiniteSet(ReportedProposals(c))
    BY ONLY <1>1, <1>2, FiniteImageUnion, IsaM("blast") DEF ReportedProposals
<1> QED BY SMT, <1>2, <1>3 DEF ReportedProposals

THEOREM ReportedEntriesFinite ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas
    PROVE IsFiniteSet(ReportedEntries(c))
<1>1. IsFiniteSet(Reporters(c))
    BY SMT, FS_Subset DEF Reporters
<1>2. ASSUME NEW r \in Reporters(c)
      PROVE IsFiniteSet(reports[c][r].entries \cup
                           (UNION {Result(p) : p \in reports[c][r].pending}))
    <2>1. IsFiniteSet(reports[c][r].entries) /\ IsFiniteSet(reports[c][r].pending)
          /\ \A p \in reports[c][r].pending : IsFiniteSet(Result(p))
        BY SMT, <1>2 DEF ControlInvariant, CollectedReportProvenance,
                   FiniteLogInvariant, FiniteSnapshots, FiniteProposals
    <2>2. IsFiniteSet(UNION {Result(p) : p \in reports[c][r].pending})
        BY ONLY <2>1, FiniteImageUnion, IsaM("blast")
    <2> QED BY <2>1, <2>2, FiniteBinaryUnion
<1> QED BY ONLY <1>1, <1>2, FiniteImageUnion, IsaM("blast") DEF ReportedEntries

THEOREM RecoveryResultFinite ==
    ASSUME ControlInvariant, FiniteLogInvariant, NEW c \in Replicas,
           NEW p \in Latest(ReportedProposals(c)) \cup {NoProposal}
    PROVE IsFiniteSet(Recovered(c, p))
<1>1. CASE p = NoProposal
    BY SMT, <1>1, FS_EmptySet DEF Recovered
<1>2. CASE p # NoProposal
    <2>1. p \in proposals
        BY SMT, <1>2, ReportedProposalsFiniteAndActual DEF Latest
    <2>2. IsFiniteSet(Result(p)) /\ IsFiniteSet(ReportedEntries(c))
        BY SMT, <2>1, ReportedEntriesFinite DEF FiniteLogInvariant, FiniteProposals
    <2>3. IsFiniteSet({e \in (IF MutSkipRecoveryUnion THEN {} ELSE ReportedEntries(c)) :
                         e.term = p.first.term /\ e.part >= p.first.part})
        BY SMT, <2>2, FS_Subset, FS_EmptySet
    <2> QED BY <2>2, <2>3, FiniteBinaryUnion, <1>2 DEF Recovered
<1> QED BY <1>1, <1>2

THEOREM FiniteLogInitially == Init => FiniteLogInvariant
BY SMT, FS_EmptySet DEF Init, FiniteLogInvariant, FiniteChannels,
    FiniteNodeData, StorageShape, FiniteProposals, FiniteSnapshots

THEOREM FiniteLogStuttering ==
    ASSUME FiniteLogInvariant, UNCHANGED FiniteLogVars
    PROVE FiniteLogInvariant'
BY SMT DEF FiniteLogInvariant, FiniteChannels, FiniteNodeData,
    FiniteProposals, FiniteSnapshots, StorageShape, FiniteLogVars

THEOREM FiniteChannelsFrame ==
    ASSUME FiniteChannels, UNCHANGED FiniteChannelVars
    PROVE FiniteChannels'
BY SMT DEF FiniteChannels, FiniteChannelVars

THEOREM FiniteNodeDataFrame ==
    ASSUME FiniteNodeData, UNCHANGED FiniteNodeVars
    PROVE FiniteNodeData'
BY SMT DEF FiniteNodeData, FiniteNodeVars, StorageShape

THEOREM FiniteProposalsFrame ==
    ASSUME FiniteProposals, UNCHANGED proposals
    PROVE FiniteProposals'
BY SMT DEF FiniteProposals

THEOREM FiniteSnapshotsFrame ==
    ASSUME FiniteSnapshots, UNCHANGED FiniteSnapshotVars
    PROVE FiniteSnapshots'
BY SMT DEF FiniteSnapshots, FiniteSnapshotVars
=============================================================================
