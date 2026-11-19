------------------------- MODULE TRaftProjectionProof ------------------------
EXTENDS TRaftClientCore, TLAPS

\* Physical protocol projection: forget the client variables and the history
\* observers. Full temporal refinement (including observer closure and the
\* finite/unbounded mapping) is tracked separately in proof-obligations.json.
THEOREM ClientInitializationProjects == ClientInit => Init
BY SMT DEF ClientInit

THEOREM ClientActionProjects ==
    ClientAction => [ProtocolNext]_protocolVars
<1>1. Background => ProtocolNext
    BY SMT DEF Background, ProtocolNext
<1>2. \A q \in ClientCommands : Invoke(q) => UNCHANGED protocolVars
    BY SMT DEF Invoke
<1>3. \A r \in Replicas, q \in calls : Admit(r, q) => ProtocolNext
    BY SMT DEF Admit, ProtocolNext, CreateEntry, CreateSuccessor
<1>4. \A r \in Replicas, q \in calls :
          (SendReply(r, q) \/ ReadWithoutBarrier(r, q)) => UNCHANGED protocolVars
    BY SMT DEF SendReply, ReadWithoutBarrier
<1>5. \A r \in Replicas : ClosePartition(r) => ProtocolNext
    BY SMT DEF ClosePartition, ProtocolNext
<1>6. \A r \in Replicas : \A e \in formal[r] : ApplyClient(r, e) => ProtocolNext
    BY SMT DEF ApplyClient, ProtocolNext
<1>7. \A m \in replyMessages : ReceiveReply(m) => UNCHANGED protocolVars
    BY SMT DEF ReceiveReply
<1> QED BY SMT, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF ClientAction

=============================================================================
