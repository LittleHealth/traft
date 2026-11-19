--------------------------- MODULE TRaftOfferProof ---------------------------
EXTENDS TRaftOfferState, TLAPS

THEOREM OfferProvenanceInitially == Init => OfferProvenance
<1>1. Init => offers = {}
    BY ONLY DEF Init
<1> QED BY ONLY <1>1 DEF OfferProvenance

THEOREM OfferProvenanceFrame ==
    ASSUME OfferProvenance, UNCHANGED offers, leaderViews \subseteq leaderViews'
    PROVE OfferProvenance'
BY SMT DEF OfferProvenance

THEOREM SendEntryRecordsOfferSource ==
    ASSUME OfferProvenance, NEW c \in Replicas, NEW e, SendEntry(c, e), Observe
    PROVE OfferProvenance'
<1>0. SendEntry(c, e) /\ Observe /\ c \in Replicas
    OBVIOUS
<1>10. role'[c] = "Leader" /\ term'[c] = term[c] /\ formal'[c] = formal[c]
    BY ONLY <1>0 DEF SendEntry
<1>11. leaderViews' = leaderViews \cup
           {[node |-> r, epoch |-> term'[r], entries |-> formal'[r]] :
                r \in {x \in Replicas : role'[x] = "Leader"}}
    BY ONLY <1>0 DEF Observe
<1>1. leaderViews \subseteq leaderViews'
      /\ [node |-> c, epoch |-> term[c], entries |-> formal[c]] \in leaderViews'
    BY ONLY SMT, <1>0, <1>10, <1>11
<1>2. e \in formal[c] /\ e.term = term[c]
      /\ offers' = offers \cup {NormalMessage(c, e)}
    BY DEF SendEntry
<1> QED BY SMT, <1>1, <1>2 DEF OfferProvenance, NormalMessage

THEOREM OnlySendEntryCreatesOffer ==
    ProtocolNext => ((\E offerCreator \in Replicas : \E offerEntry : SendEntry(offerCreator, offerEntry)) \/ UNCHANGED offers)
<1>1. \A c \in Replicas : StartElection(c) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF StartElection
<1>2. \A r \in Replicas : \A t : AdoptTerm(r, t) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF AdoptTerm
<1>3. \A r \in Replicas : \A req : GrantVote(r, req) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF GrantVote
<1>4. \A c \in Replicas : \A m : DeliverVote(c, m) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF DeliverVote
<1>5. \A c \in Replicas : WinElection(c) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF WinElection
<1>6. \A r \in Replicas : \A req : MakeReport(r, req) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF MakeReport
<1>7. \A c \in Replicas : \A m : DeliverReport(c, m) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF DeliverReport
<1>8. \A c \in Replicas : \A p : BuildRecovery(c, p) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF BuildRecovery
<1>9. \A c \in Replicas : \A v : CreateEntry(c, v) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF CreateEntry
<1>10. \A c \in Replicas : \A v, k : CreateSuccessor(c, v, k) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF CreateSuccessor
<1>11. \A c \in Replicas : \A e : SendEntry(c, e) => ((\E offerCreator \in Replicas : \E offerEntry : SendEntry(offerCreator, offerEntry)) \/ UNCHANGED offers)
    BY SMT
<1>12. \A r \in Replicas : \A o : ReceiveEntry(r, o) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF ReceiveEntry
<1>13. \A r \in Replicas : \A o : AckEntry(r, o) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF AckEntry
<1>14. \A r, s \in Replicas : \A p, e : CopyProposalEntry(r, s, p, e) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF CopyProposalEntry
<1>15. \A r \in Replicas : \A p : RetainProposal(r, p) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF RetainProposal
<1>16. \A r \in Replicas : \A p : AckProposal(r, p) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF AckProposal
<1>17. \A c \in Replicas : \A m : DeliverAck(c, m) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF DeliverAck
<1>18. \A c \in Replicas : ConfirmProposal(c) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF ConfirmProposal
<1>19. \A r \in Replicas : \A p : LearnConfirmation(r, p) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF LearnConfirmation
<1>20. \A c \in Replicas : \A e : CommitEntry(c, e) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF CommitEntry
<1>21. \A c \in Replicas : \A e : AdvertiseCommit(c, e) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF AdvertiseCommit
<1>22. \A r \in Replicas : \A m : LearnCommit(r, m) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF LearnCommit
<1>23. \A c \in Replicas : Activate(c) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF Activate
<1>24. \A r \in Replicas : \A e : ApplyEntry(r, e) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF ApplyEntry
<1>25. \A r \in Replicas : Crash(r) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF Crash
<1>26. \A r \in Replicas : Restart(r) => UNCHANGED offers
    BY ONLY ZenonT(5) DEF Restart
<1>27. AdministrativeNext => ((\E offerCreator \in Replicas : \E offerEntry : SendEntry(offerCreator, offerEntry)) \/ UNCHANGED offers)
    BY ONLY ZenonT(10), <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>25, <1>26
       DEF AdministrativeNext
<1> QED BY ONLY ZenonT(10), <1>9, <1>10, <1>24, <1>27 DEF ProtocolNext


THEOREM OfferInductiveStep ==
    ASSUME OfferProvenance, Next
    PROVE OfferProvenance'
<1>1. (\E offerCreator \in Replicas : \E offerEntry : SendEntry(offerCreator, offerEntry)) \/ UNCHANGED offers
    BY OnlySendEntryCreatesOffer DEF Next
<1>2. leaderViews \subseteq leaderViews' /\ Observe
    <2>1. Observe
        BY DEF Next
    <2>2. leaderViews' = leaderViews \cup
              {[node |-> r, epoch |-> term'[r], entries |-> formal'[r]] :
                  r \in {x \in Replicas : role'[x] = "Leader"}}
        BY <2>1 DEF Observe
    <2> QED BY ONLY SMT, <2>1, <2>2
<1> QED BY SMT, <1>1, <1>2, SendEntryRecordsOfferSource, OfferProvenanceFrame

THEOREM OfferStuttering ==
    ASSUME OfferProvenance, UNCHANGED OfferVars
    PROVE OfferProvenance'
BY SMT DEF OfferVars, OfferProvenance

THEOREM ProtocolOfferProvenance == Spec => []OfferProvenance
<1>1. Init => OfferProvenance
    BY OfferProvenanceInitially
<1>2. OfferProvenance /\ [Next]_vars => OfferProvenance'
    BY SMT, OfferInductiveStep, OfferStuttering DEF vars, protocolVars, observerVars, OfferVars
<1> QED BY PTL, <1>1, <1>2 DEF Spec
=============================================================================
