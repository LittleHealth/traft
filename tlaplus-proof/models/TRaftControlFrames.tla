------------------------- MODULE TRaftControlFrames -------------------------
EXTENDS TRaftControlSupport

THEOREM ProtocolControlProjection ==
    ProtocolNext => ControlChangingNext \/ UNCHANGED ControlCoreVars
<1>1. \A r, req : GrantVote(r, req) => UNCHANGED ControlCoreVars
    BY SMT DEF GrantVote, ControlCoreVars
<1>2. \A c, m : DeliverVote(c, m) => UNCHANGED ControlCoreVars
    BY SMT DEF DeliverVote, ControlCoreVars
<1>3. \A c, v : CreateEntry(c, v) => UNCHANGED ControlCoreVars
    BY SMT DEF CreateEntry, ControlCoreVars
<1>4. \A c, v, k : CreateSuccessor(c, v, k) => UNCHANGED ControlCoreVars
    BY SMT DEF CreateSuccessor, ControlCoreVars
<1>5. \A c, e : SendEntry(c, e) => UNCHANGED ControlCoreVars
    BY SMT DEF SendEntry, ControlCoreVars
<1>6. \A r, o : ReceiveEntry(r, o) => UNCHANGED ControlCoreVars
    BY SMT DEF ReceiveEntry, ControlCoreVars
<1>7. \A r, o : AckEntry(r, o) => UNCHANGED ControlCoreVars
    BY SMT DEF AckEntry, ControlCoreVars
<1>8. \A r, source, p, e : CopyProposalEntry(r, source, p, e) => UNCHANGED ControlCoreVars
    BY SMT DEF CopyProposalEntry, ControlCoreVars
<1>9. \A r, p : RetainProposal(r, p) => UNCHANGED ControlCoreVars
    BY SMT DEF RetainProposal, ControlCoreVars
<1>10. \A r, p : AckProposal(r, p) => UNCHANGED ControlCoreVars
    BY SMT DEF AckProposal, ControlCoreVars
<1>11. \A c, m : DeliverAck(c, m) => UNCHANGED ControlCoreVars
    BY SMT DEF DeliverAck, ControlCoreVars
<1>12. \A r, p : LearnConfirmation(r, p) => UNCHANGED ControlCoreVars
    BY SMT DEF LearnConfirmation, ControlCoreVars
<1>13. \A c, e : CommitEntry(c, e) => UNCHANGED ControlCoreVars
    BY SMT DEF CommitEntry, ControlCoreVars
<1>14. \A c, e : AdvertiseCommit(c, e) => UNCHANGED ControlCoreVars
    BY SMT DEF AdvertiseCommit, ControlCoreVars
<1>15. \A r, m : LearnCommit(r, m) => UNCHANGED ControlCoreVars
    BY SMT DEF LearnCommit, ControlCoreVars
<1>16. \A r, e : ApplyEntry(r, e) => UNCHANGED ControlCoreVars
    BY SMT DEF ApplyEntry, ControlCoreVars
<1>17. \A r : Restart(r) => UNCHANGED ControlCoreVars
    BY SMT DEF Restart, ControlCoreVars
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17
    DEF ProtocolNext, AdministrativeNext, ControlChangingNext

THEOREM ProtocolStutterProjectsToControl ==
    UNCHANGED vars => UNCHANGED ControlVars
BY SMT DEF vars, protocolVars, observerVars, ControlVars, ControlCoreVars
=============================================================================
