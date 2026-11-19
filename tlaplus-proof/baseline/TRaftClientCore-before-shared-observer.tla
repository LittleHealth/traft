---------------------------- MODULE TRaftClientCore -----------------------------
EXTENDS TRaftCore, Sequences

CONSTANTS Clients, Series, Times, Values, Missing, MaxSequence,
          MutEarlyReply, MutReadWithoutBarrier, MutLoseDedup
SeqDomain == IF MaxSequence \in Nat THEN 1..MaxSequence ELSE Nat \ {0}
RequestIds == Clients \X SeqDomain
Keys == Series \X Times
ClientCommands == {q \in [id : RequestIds, op : {"Put", "Delete", "Get"},
                          key : Keys, value : Values \cup {Missing}] :
                      IF q.op = "Put" THEN q.value \in Values ELSE q.value = Missing}
ASSUME ClientParameters == /\ Clients # {} /\ Series # {} /\ Times \subseteq Nat /\ Times # {}
       /\ Values # {} /\ Missing \notin Values /\ DataValues = ClientCommands
       /\ MutEarlyReply \in BOOLEAN /\ MutReadWithoutBarrier \in BOOLEAN
       /\ MutLoseDedup \in BOOLEAN

VARIABLES calls, nextSequence, machine, cache, replyMessages, returned, history,
          witness, abstractMachine, abstractAnswers
localClientVars == <<calls, nextSequence, machine, cache, replyMessages, returned, history>>
witnessVars == <<witness, abstractMachine, abstractAnswers>>
clientVars == <<vars, localClientVars, witnessVars>>

EmptyMachine == [k \in Keys |-> Missing]
EmptyCache == [id \in RequestIds |-> [ready |-> FALSE, value |-> Missing]]
EmptyAnswers == [id \in RequestIds |-> Missing]
CalledIds == {q.id : q \in calls}
ReturnedIds == {m.id : m \in returned}
Command(id) == CHOOSE q \in calls : q.id = id
Ids(order) == {order[i] : i \in 1..Len(order)}
Position(order, id) == CHOOSE i \in 1..Len(order) : order[i] = id
Reply(db, q) == IF q.op = "Get" THEN db[q.key] ELSE "OK"
Effect(db, q) == CASE q.op = "Put" -> [db EXCEPT ![q.key] = q.value]
                  [] q.op = "Delete" -> [db EXCEPT ![q.key] = Missing]
                  [] q.op = "Get" -> db

ClientInit ==
    /\ Init /\ calls = {} /\ nextSequence = [c \in Clients |-> 1]
    /\ machine = [r \in Replicas |-> EmptyMachine]
    /\ cache = [r \in Replicas |-> EmptyCache]
    /\ replyMessages = {} /\ returned = {} /\ history = <<>>
    /\ witness = <<>> /\ abstractMachine = EmptyMachine /\ abstractAnswers = EmptyAnswers

Invoke(q) ==
    /\ q \in ClientCommands /\ q.id[2] = nextSequence[q.id[1]]
    /\ ~\E old \in calls : old.id[1] = q.id[1] /\ old.id \notin ReturnedIds
    /\ calls' = calls \cup {q}
    /\ nextSequence' = [nextSequence EXCEPT ![q.id[1]] = @ + 1]
    /\ history' = Append(history, [kind |-> "call", id |-> q.id, value |-> Missing])
    /\ UNCHANGED <<protocolVars, machine, cache, replyMessages, returned>>

Timestamp(q) == q.key[2]
Timed(L) == {e \in L : e.kind = "data" /\ e.value.op # "Get"}
MaxTimestamp(L) == MaxOr({Timestamp(e.value) : e \in Timed(L)}, -1)
HasRead(L) == \E e \in Part(L, Cur(L)) : e.kind = "data" /\ e.value.op = "Get"
MustSeparate(L, q) == q.op = "Get" \/ HasRead(L) \/ Timestamp(q) <= MaxTimestamp(L)

Admit(r, q) ==
    /\ q \in calls
    /\ IF MustSeparate(formal[r], q)
          THEN CreateSuccessor(r, q, "data")
          ELSE /\ Count(formal[r], Cur(formal[r])) < MaxPartitionSize
               /\ CreateEntry(r, q)
    /\ UNCHANGED localClientVars

\* Size/time boundaries use the paper's existing no-op action. Get is the
\* explicit client extension: its partition contains only that read command.
ClosePartition(r) ==
    /\ CreateSuccessor(r, NoValue, "noop")
    /\ UNCHANGED localClientVars

ApplyClient(r, e) ==
    /\ ApplyEntry(r, e)
    /\ IF e.kind = "noop" THEN UNCHANGED <<machine, cache>>
          ELSE LET q == e.value IN
            IF cache[r][q.id].ready THEN UNCHANGED <<machine, cache>>
            ELSE /\ machine' = [machine EXCEPT ![r] = Effect(@, q)]
                 /\ cache' = [cache EXCEPT ![r][q.id] =
                                      [ready |-> TRUE, value |-> Reply(machine[r], q)]]
    /\ UNCHANGED <<calls, nextSequence, replyMessages, returned, history>>

Background ==
    /\ AdministrativeNext
    /\ cache' = [r \in Replicas |->
          IF MutLoseDedup /\ alive[r] /\ ~alive'[r] THEN EmptyCache ELSE cache[r]]
    /\ UNCHANGED <<calls, nextSequence, machine, replyMessages, returned, history>>

SendReply(r, q) ==
    /\ alive[r] /\ q \in calls
    /\ cache[r][q.id].ready \/
          (MutEarlyReply /\ \E e \in formal[r] : e.kind = "data" /\ e.value = q)
    /\ replyMessages' = replyMessages \cup
           {[sender |-> r, id |-> q.id,
             value |-> IF cache[r][q.id].ready THEN cache[r][q.id].value
                       ELSE Reply(machine[r], q)]}
    /\ UNCHANGED <<protocolVars, calls, nextSequence, machine, cache, returned, history>>

ReadWithoutBarrier(r, q) ==
    /\ MutReadWithoutBarrier /\ alive[r] /\ q \in calls /\ q.op = "Get"
    /\ replyMessages' = replyMessages \cup
           {[sender |-> r, id |-> q.id, value |-> machine[r][q.key]]}
    /\ UNCHANGED <<protocolVars, calls, nextSequence, machine, cache, returned, history>>

ReceiveReply(m) ==
    /\ m \in replyMessages /\ m.id \notin ReturnedIds
    /\ returned' = returned \cup {m}
    /\ history' = Append(history, [kind |-> "return", id |-> m.id, value |-> m.value])
    /\ UNCHANGED <<protocolVars, calls, nextSequence, machine, cache, replyMessages>>

ClientAction ==
    \/ Background
    \/ \E q \in ClientCommands : Invoke(q)
    \/ \E r \in Replicas, q \in calls : Admit(r, q) \/ SendReply(r, q) \/ ReadWithoutBarrier(r, q)
    \/ \E r \in Replicas : ClosePartition(r) \/ (\E e \in formal[r] : ApplyClient(r, e))
    \/ \E m \in replyMessages : ReceiveReply(m)

\* Uniform specification used by the temporal projection theorem. The extra
\* observer is instantiated by ObserveLinearization in the TLC client module.
ClientSpecification(Extra) ==
    ClientInit /\ [][ClientAction /\ Observe /\ Extra]_clientVars

ClientTypeOK ==
    /\ calls \subseteq ClientCommands
    /\ \A q, p \in calls : q.id = p.id => q = p
    /\ nextSequence \in [Clients -> Nat]
    /\ machine \in [Replicas -> [Keys -> Values \cup {Missing}]]
    /\ history \in Seq([kind : {"call", "return"}, id : RequestIds,
                        value : Values \cup {Missing, "OK"}])
    /\ \A r \in Replicas : cache[r] \in
          [RequestIds -> [ready : BOOLEAN, value : Values \cup {Missing, "OK"}]]

ReadIsolation == \A r \in Replicas : \A e \in formal[r] :
    e.kind = "data" /\ e.value.op = "Get" => Part(formal[r], e.part) = {e}
PartitionCommandsIndependent == \A r \in Replicas : \A e, f \in formal[r] :
    (/\ e # f /\ e.part = f.part /\ e.kind = "data" /\ f.kind = "data") =>
      /\ e.value.op # "Get" /\ f.value.op # "Get" /\ e.value.key # f.value.key
CacheHasAppliedRequest == \A r \in Replicas : \A q \in calls :
    cache[r][q.id].ready => \E e \in applied[r] : e.kind = "data" /\ e.value = q

=============================================================================
