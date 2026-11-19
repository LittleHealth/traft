------------------------ MODULE TRaftPaperSuffix ------------------------
EXTENDS TRaftPaperScenarios
CONSTANT SuffixSteps
VARIABLE suffixStep
suffixVars == <<scenarioVars, suffixStep>>
ForkAt == 55

SuffixInit == ScenarioInit /\ suffixStep = 0
SuffixNext ==
    \/ /\ pc < ForkAt /\ ScenarioStep /\ Observe /\ pc' = pc + 1
       /\ UNCHANGED suffixStep
    \/ /\ pc = ForkAt /\ suffixStep < SuffixSteps /\ Next
       /\ UNCHANGED pc /\ suffixStep' = suffixStep + 1
    \/ /\ pc = ForkAt /\ suffixStep = SuffixSteps /\ UNCHANGED suffixVars
SuffixSpec == SuffixInit /\ [][SuffixNext]_suffixVars
SuffixTypeOK == /\ pc \in 0..ForkAt /\ suffixStep \in 0..SuffixSteps
=============================================================================
