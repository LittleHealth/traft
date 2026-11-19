----------------------- MODULE TRaftFoldClientScenarios ----------------------
EXTENDS TRaftApplicationScenarios, TRaftClientLinearizationState

VARIABLE foldObserverAgreement
\* A passive failure flag: disagreement is recorded, never used to enable
\* or disable a protocol/client step. Compare the actual incremental batch.
ObserveFoldAgreement ==
    LET entries == {f.entry : f \in commitHistory'}
        added == {e \in entries : e.kind = "data" /\ e.value.id \notin Ids(witness)}
    IN foldObserverAgreement' = (foldObserverAgreement /\
         SortedIncorporation(added, witness, abstractMachine, abstractAnswers)
           = Incorporate(added, witness, abstractMachine, abstractAnswers))
FoldScenarioSpec ==
    /\ ScenarioInit /\ foldObserverAgreement = TRUE
    /\ [][ScenarioNext /\ ObserveFoldAgreement]_<<scenarioClientVars, foldObserverAgreement>>
FoldObserverAgreement == foldObserverAgreement

\* These are finite equivalence probes, not a theorem connecting the two
\* observer definitions for arbitrary executions.
FoldAndRecursiveHistoryAgree == FoldHistoryLinearizable = HistoryLinearizable
FoldAndRecursiveExecutionAgree ==
    FoldExecuteOrder(witness, EmptyMachine, EmptyAnswers)
      = ExecuteOrder(witness, EmptyMachine, EmptyAnswers)
FoldAndRecursiveBatchAgree ==
    LET entries == {e \in EvidenceEntries : e.kind = "data"}
    IN SortedIncorporation(entries, <<>>, EmptyMachine, EmptyAnswers)
         = Incorporate(entries, <<>>, EmptyMachine, EmptyAnswers)
=============================================================================
