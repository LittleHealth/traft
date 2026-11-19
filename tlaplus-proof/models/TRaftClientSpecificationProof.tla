---------------------- MODULE TRaftClientSpecificationProof ------------------
EXTENDS TRaftSharedClientSpecification, TRaftClientRefinementProof

THEOREM SharedClientSpecificationIdentity == ClientSpec <=> ProofClientSpec
BY DEF ClientSpec, ProofClientSpec, ObserveLinearization

THEOREM SharedClientStepIdentity ==
    ClientNext <=> ClientAction /\ Observe /\ ProofObserveLinearization
BY DEF ClientNext, ObserveLinearization

THEOREM SharedClientProtocolRefinement == ClientSpec => Spec
BY ClientTemporalRefinement DEF ClientSpec
=============================================================================
