------------------------------ MODULE TRaftPaper ------------------------------
EXTENDS TRaftCore, TLC

\* Finite compatibility instance; all protocol actions come from TRaftCore.
ASSUME /\ MaxTerm \in Nat \ {0} /\ MaxIndex \in Nat \ {0}
       /\ MaxPartition \in Nat /\ IsFiniteSet(DataValues)
Symmetry == Permutations(Replicas)
=============================================================================
