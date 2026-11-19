------------------------- MODULE TRaftElectionFrames -------------------------
EXTENDS TRaftElectionSupport

THEOREM ProtocolElectionProjection ==
    ProtocolNext => ElectionChangingNext \/ UNCHANGED ElectionCoreVars
<1>1. \A c : ConfirmProposal(c) => UNCHANGED ElectionCoreVars
    BY SMT DEF ConfirmProposal, ElectionCoreVars
<1>2. \A r, req : MakeReport(r, req) => UNCHANGED ElectionCoreVars
    BY SMT DEF MakeReport, ElectionCoreVars
<1>3. \A c, m : DeliverReport(c, m) => UNCHANGED ElectionCoreVars
    BY SMT DEF DeliverReport, ElectionCoreVars
<1>4. \A c, p : BuildRecovery(c, p) => UNCHANGED ElectionCoreVars
    BY SMT DEF BuildRecovery, ElectionCoreVars
<1>5. \A c, v : CreateEntry(c, v) => UNCHANGED ElectionCoreVars
    BY SMT DEF CreateEntry, ElectionCoreVars
<1>6. \A c, v, k : CreateSuccessor(c, v, k) => UNCHANGED ElectionCoreVars
    BY SMT DEF CreateSuccessor, ElectionCoreVars
<1>7. \A c, e : SendEntry(c, e) => UNCHANGED ElectionCoreVars
    BY SMT DEF SendEntry, ElectionCoreVars
<1>8. \A r, o : ReceiveEntry(r, o) => UNCHANGED ElectionCoreVars
    BY SMT DEF ReceiveEntry, ElectionCoreVars
<1>9. \A r, o : AckEntry(r, o) => UNCHANGED ElectionCoreVars
    BY SMT DEF AckEntry, ElectionCoreVars
<1>10. \A r, source, p, e : CopyProposalEntry(r, source, p, e) => UNCHANGED ElectionCoreVars
    BY SMT DEF CopyProposalEntry, ElectionCoreVars
<1>11. \A r, p : RetainProposal(r, p) => UNCHANGED ElectionCoreVars
    BY SMT DEF RetainProposal, ElectionCoreVars
<1>12. \A r, p : AckProposal(r, p) => UNCHANGED ElectionCoreVars
    BY SMT DEF AckProposal, ElectionCoreVars
<1>13. \A c, m : DeliverAck(c, m) => UNCHANGED ElectionCoreVars
    BY SMT DEF DeliverAck, ElectionCoreVars
<1>14. \A r, p : LearnConfirmation(r, p) => UNCHANGED ElectionCoreVars
    BY SMT DEF LearnConfirmation, ElectionCoreVars
<1>15. \A c, e : CommitEntry(c, e) => UNCHANGED ElectionCoreVars
    BY SMT DEF CommitEntry, ElectionCoreVars
<1>16. \A c, e : AdvertiseCommit(c, e) => UNCHANGED ElectionCoreVars
    BY SMT DEF AdvertiseCommit, ElectionCoreVars
<1>17. \A r, m : LearnCommit(r, m) => UNCHANGED ElectionCoreVars
    BY SMT DEF LearnCommit, ElectionCoreVars
<1>18. \A r, e : ApplyEntry(r, e) => UNCHANGED ElectionCoreVars
    BY SMT DEF ApplyEntry, ElectionCoreVars
<1>19. \A r : Restart(r) => UNCHANGED ElectionCoreVars
    BY SMT DEF Restart, ElectionCoreVars
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19
    DEF ProtocolNext, AdministrativeNext, ElectionChangingNext

THEOREM ElectionFramePreserves ==
    ASSUME ElectionInvariant, ObserveWinners, UNCHANGED ElectionCoreVars
    PROVE ElectionInvariant'
<1>1. winners' = winners
    BY SMT DEF ElectionInvariant, ElectionWinnerFacts, ElectionCoreVars, ObserveWinners
<1>2. UNCHANGED ElectionVars
    BY SMT, <1>1 DEF ElectionVars
<1> QED BY ElectionStuttering, <1>2

THEOREM ProtocolStutterProjectsToElection ==
    UNCHANGED vars => UNCHANGED ElectionVars
BY SMT DEF vars, protocolVars, observerVars, ElectionVars, ElectionCoreVars
=============================================================================
