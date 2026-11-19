------------------------------ MODULE TRaftCore ------------------------------
EXTENDS Naturals, Integers, FiniteSets

(***************************************************************************
 Current-paper model, 2026-11-16. Normal replication follows main.tex's
 committed-count boundary rule, NOT the historical staged-boundary protocol.
 The Leader installs newly assigned normal entries immediately. Followers
 advance one partition when previous total = committed = local distinct count.
 Only election recovery uses an exact-prefix proposal and quorum confirmation.

 Recovery interpretation: inherit the latest durable recovery result, then
 union reported normal extensions from that result's creation term. A report
 containing a later normal partition supplies its complete preceding prefix;
 the remaining open-partition entries are merged by identity. This makes the
 paper's "merge the same open partition" operational; see README's mapping.
 No global safety oracle or exact-prefix equality guard protects normal receipt.

 Independent evidence: commitHistory is derived ONLY from issued ACKs of
 distinct replicas for the same owner and authorizing epoch. Commit messages,
 local commitment, and confirmations never create evidence. All protocol
 decisions use local state/inboxes; observers never enable an action.

 Durable state survives crash; control and ordinary data messages may outlive
 senders, repeat, or be omitted. Recovery copies require a live source and are
 interruptible entry by entry. Complete reports and installation are atomic.
 No fairness, dynamic membership, snapshots/GC, client responses/reads/retries,
 numerical timestamps, or concrete application execution are modeled.
 Same-partition command independence is an external assumption, not a theorem
 established by representing applied identities as a set.
 ***************************************************************************
*)

CONSTANTS Replicas, DataValues, MaxTerm, MaxIndex, MaxPartition,
          MaxPartitionSize, Absent, NoValue, MutDropPending, MutSkipRecoveryUnion, MutEarlyPublish,
          MutNoCommitQuorum, MutSkipBoundaryCommit

NoNode == "NoNode"
NoProposal == Absent
NoReport == Absent
Roles == {"Follower", "Candidate", "LeaderCandidate", "Leader"}
Phases == {"idle", "collect", "sync", "commit", "serve"}
NoBound == "Unbounded"
Terms == IF MaxTerm \in Nat THEN 0..MaxTerm ELSE Nat
Indices == IF MaxIndex \in Nat THEN 1..MaxIndex ELSE Nat \ {0}
Partitions == IF MaxPartition \in Nat THEN 0..MaxPartition ELSE Nat

ASSUME ParameterAssumptions == /\ IsFiniteSet(Replicas) /\ Cardinality(Replicas) >= 3
       /\ DataValues # {}
       /\ Terms \subseteq Nat /\ {0, 1} \subseteq Terms
       /\ Indices \subseteq (Nat \ {0}) /\ 1 \in Indices
       /\ Partitions \subseteq Nat /\ 0 \in Partitions
       /\ MaxPartitionSize \in Nat \ {0}
       /\ MutDropPending \in BOOLEAN /\ MutSkipRecoveryUnion \in BOOLEAN
       /\ MutEarlyPublish \in BOOLEAN
       /\ MutNoCommitQuorum \in BOOLEAN /\ MutSkipBoundaryCommit \in BOOLEAN
       /\ NoNode \notin Replicas /\ NoValue \notin DataValues

Entries == [index : Indices, term : (Terms \ {0}), part : Partitions,
            value : DataValues \cup {NoValue}, kind : {"data", "noop"},
            prevSize : 0..MaxPartitionSize]

\* The absence marker is a separate protocol variant, never a real proposal.
\* TLC configurations use a model value; the parameterized theorem states
\* this ordinary data-type separation explicitly.
ProposalRecords == [owner : Replicas, epoch : Terms \ {0}, prefix : SUBSET Entries,
                    first : Entries, recovering : BOOLEAN]
ASSUME SentinelSeparation == Absent \notin ProposalRecords

MaxOr(S, empty) == IF S = {} THEN empty
                  ELSE CHOOSE x \in S : \A y \in S : y <= x
Cur(L) == MaxOr({e.part : e \in L}, -1)
LastIndex(L) == MaxOr({e.index : e \in L}, 0)
Part(L, p) == {e \in L : e.part = p}
Prefix(L, p) == {e \in L : e.part <= p}
Count(L, p) == Cardinality(Part(L, p))
ClosedPrefix(L) == Prefix(L, Cur(L) - 1)
LastTerm(L) == IF L = {} THEN 0
               ELSE (CHOOSE e \in L : e.index = LastIndex(L)).term
Origin(L, p) == IF Part(L, p) = {} THEN 0
                ELSE (CHOOSE e \in Part(L, p) : TRUE).term
Rank(L) == <<LastTerm(L), Cur(L), Count(L, Cur(L))>>
AtLeast(a, b) == \/ a[1] > b[1]
                 \/ /\ a[1] = b[1] /\ a[2] > b[2]
                 \/ /\ a[1] = b[1] /\ a[2] = b[2] /\ a[3] >= b[3]
Quorum(S) == S \subseteq Replicas /\ 2 * Cardinality(S) > Cardinality(Replicas)
Coherent(L) ==
    /\ \A e, f \in L : e.index = f.index => e = f
    /\ \A e, f \in L : e.part = f.part => e.term = f.term
    /\ \A e, f \in L : e.index < f.index => e.part <= f.part
    /\ \A e \in L : (e.kind = "noop") <=> (e.value = NoValue)

Entry(i, t, p, v, k, n) ==
    [index |-> i, term |-> t, part |-> p, value |-> v,
     kind |-> k, prevSize |-> n]
Proposal(c, t, L, e, recovery) ==
    [owner |-> c, epoch |-> t, prefix |-> L, first |-> e,
     recovering |-> recovery]
Result(p) == p.prefix \cup {p.first}
Later(p, q) == \/ p.first.term > q.first.term
                \/ /\ p.first.term = q.first.term
                   /\ p.first.part > q.first.part
Latest(Ps) == {p \in Ps : ~\E q \in Ps : Later(q, p)}
Ack(r, c, t, e, L) ==
    [sender |-> r, receiver |-> c, epoch |-> t, target |-> e,
     contents |-> L]

VARIABLES term, vote, alive, role, phase, formal, stored, retained,
          current, reports, voteInbox, ackInbox, knownCommitted, applied,
          voteRequests, voteMessages, recoveryRequests, reportMessages,
          offers, proposals, ackMessages, confirmations, commitMessages,
          winners, leaderViews, commitHistory, partitionHistory,
          appendOnlyOK, appliedPartitionHistory, applicationOrderOK, entryContexts

protocolVars == <<term, vote, alive, role, phase, formal, stored, retained,
                 current, reports, voteInbox, ackInbox, knownCommitted,
                 applied, voteRequests, voteMessages, recoveryRequests,
                 reportMessages, offers, proposals, ackMessages,
                 confirmations, commitMessages>>
observerVars == <<winners, leaderViews, commitHistory, partitionHistory,
                 appendOnlyOK, appliedPartitionHistory, applicationOrderOK, entryContexts>>
vars == <<protocolVars, observerVars>>

EmptyReports == [r \in Replicas |-> NoReport]
Reporters(c) == {r \in Replicas : reports[c][r] # NoReport}
ReportedProposals(c) == (UNION {reports[c][r].pending : r \in Reporters(c)})
ReportedEntries(c) ==
    (UNION {reports[c][r].entries \cup
           (UNION {Result(p) : p \in reports[c][r].pending}) :
           r \in Reporters(c)})
Recovered(c, p) ==
    IF p = NoProposal THEN {}
    ELSE Result(p) \cup
         {e \in (IF MutSkipRecoveryUnion THEN {} ELSE ReportedEntries(c)) :
             /\ e.term = p.first.term /\ e.part >= p.first.part}
Aligned(r, t) ==
    \E p \in retained[r] : /\ p.epoch = t /\ p.first \in formal[r]

MessageAckers(messages, c, t, e) ==
    {r \in Replicas : \E a \in messages : /\ a.sender = r
                                         /\ a.receiver = c
                                         /\ a.epoch = t
                                         /\ e \in a.contents}
Ackers(c, t, e) == MessageAckers(ackInbox[c], c, t, e)
ProposalAckers(c, p) ==
    {r \in Replicas : Ack(r, c, p.epoch, p.first, Result(p)) \in ackInbox[c]}
\* Replaying a confirmation must not erase later normal entries.
Publish(r, p) == IF p.first \in formal[r] THEN formal[r] ELSE Result(p)

NormalMessage(c, e) ==
    [owner |-> c, epoch |-> term[c], entry |-> e,
     committed |-> Count(formal[c] \cap knownCommitted[c], e.part - 1)]

\* Only locally available term, identity and count checks occur here.
CanReceive(r, o) ==
    /\ alive[r] /\ term[r] = o.epoch /\ o.entry.term = o.epoch
    /\ Aligned(r, o.epoch)
    /\ IF o.entry.part = Cur(formal[r])
          THEN Origin(formal[r], Cur(formal[r])) = o.entry.term
          ELSE /\ o.entry.part = Cur(formal[r]) + 1
               /\ o.entry.prevSize = Count(formal[r], Cur(formal[r]))
               /\ MutSkipBoundaryCommit \/ o.committed = o.entry.prevSize
    /\ \A e \in formal[r] : e.index = o.entry.index => e = o.entry

Init ==
    /\ term = [r \in Replicas |-> 0]
    /\ vote = [r \in Replicas |-> NoNode]
    /\ alive = [r \in Replicas |-> TRUE]
    /\ role = [r \in Replicas |-> "Follower"]
    /\ phase = [r \in Replicas |-> "idle"]
    /\ formal = [r \in Replicas |-> {}]
    /\ stored = [r \in Replicas |-> {}]
    /\ retained = [r \in Replicas |-> {}]
    /\ current = [r \in Replicas |-> NoProposal]
    /\ reports = [r \in Replicas |-> EmptyReports]
    /\ voteInbox = [r \in Replicas |-> {}]
    /\ ackInbox = [r \in Replicas |-> {}]
    /\ knownCommitted = [r \in Replicas |-> {}]
    /\ applied = [r \in Replicas |-> {}]
    /\ voteRequests = {} /\ voteMessages = {} /\ recoveryRequests = {}
    /\ reportMessages = {} /\ offers = {} /\ proposals = {}
    /\ ackMessages = {} /\ confirmations = {} /\ commitMessages = {}
    /\ winners = {} /\ leaderViews = {} /\ commitHistory = {}
    /\ partitionHistory = {} /\ appendOnlyOK = TRUE
    /\ appliedPartitionHistory = {} /\ applicationOrderOK = TRUE
    /\ entryContexts = {}

StartElection(c) ==
    LET t == term[c] + 1
        req == [candidate |-> c, epoch |-> t, entries |-> formal[c]]
        selfVote == [sender |-> c, receiver |-> c, epoch |-> t]
    IN /\ alive[c] /\ term[c] + 1 \in Terms
       /\ role[c] # "Leader"
       /\ term' = [term EXCEPT ![c] = t]
       /\ vote' = [vote EXCEPT ![c] = c]
       /\ role' = [role EXCEPT ![c] = "Candidate"]
       /\ phase' = [phase EXCEPT ![c] = "idle"]
       /\ current' = [current EXCEPT ![c] = NoProposal]
       /\ reports' = [reports EXCEPT ![c] = EmptyReports]
       /\ voteInbox' = [voteInbox EXCEPT ![c] = {selfVote}]
       /\ ackInbox' = [ackInbox EXCEPT ![c] = {}]
       /\ voteRequests' = voteRequests \cup {req}
       /\ voteMessages' = voteMessages \cup {selfVote}
       /\ UNCHANGED <<alive, formal, stored, retained, knownCommitted,
                      applied, recoveryRequests, reportMessages, offers,
                      proposals, ackMessages, confirmations, commitMessages>>

AdoptTerm(r, t) ==
    \* Every created term leaves a durable-in-channel vote request. A delayed
    \* RPC can carry a historical term even after all its senders advanced.
    /\ alive[r] /\ t \in {req.epoch : req \in voteRequests} /\ t > term[r]
    /\ term' = [term EXCEPT ![r] = t]
    /\ vote' = [vote EXCEPT ![r] = NoNode]
    /\ role' = [role EXCEPT ![r] = "Follower"]
    /\ phase' = [phase EXCEPT ![r] = "idle"]
    /\ current' = [current EXCEPT ![r] = NoProposal]
    /\ reports' = [reports EXCEPT ![r] = EmptyReports]
    /\ voteInbox' = [voteInbox EXCEPT ![r] = {}]
    /\ ackInbox' = [ackInbox EXCEPT ![r] = {}]
    /\ UNCHANGED <<alive, formal, stored, retained, knownCommitted, applied,
                   voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages,
                   confirmations, commitMessages>>

GrantVote(r, req) ==
    /\ req \in voteRequests /\ alive[r] /\ term[r] = req.epoch
    /\ vote[r] \in {NoNode, req.candidate}
    /\ AtLeast(Rank(req.entries), Rank(formal[r]))
    /\ vote' = [vote EXCEPT ![r] = req.candidate]
    /\ voteMessages' = voteMessages \cup
         {[sender |-> r, receiver |-> req.candidate, epoch |-> req.epoch]}
    /\ UNCHANGED <<term, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   applied, voteRequests, recoveryRequests, reportMessages,
                   offers, proposals, ackMessages, confirmations, commitMessages>>

DeliverVote(c, m) ==
    /\ m \in voteMessages /\ m.receiver = c /\ alive[c]
    /\ role[c] = "Candidate" /\ term[c] = m.epoch
    /\ voteInbox' = [voteInbox EXCEPT ![c] = @ \cup {m}]
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, ackInbox, knownCommitted, applied,
                   voteRequests, voteMessages, recoveryRequests, reportMessages,
                   offers, proposals, ackMessages, confirmations, commitMessages>>

WinElection(c) ==
    /\ alive[c] /\ role[c] = "Candidate"
    /\ Quorum({m.sender : m \in {v \in voteInbox[c] : v.epoch = term[c]}})
    /\ role' = [role EXCEPT ![c] = "LeaderCandidate"]
    /\ phase' = [phase EXCEPT ![c] = "collect"]
    /\ recoveryRequests' = recoveryRequests \cup
         {[owner |-> c, epoch |-> term[c]]}
    /\ UNCHANGED <<term, vote, alive, formal, stored, retained, current,
                   reports, voteInbox, ackInbox, knownCommitted, applied,
                   voteRequests, voteMessages, reportMessages, offers,
                   proposals, ackMessages, confirmations, commitMessages>>

MakeReport(r, req) ==
    /\ req \in recoveryRequests /\ alive[r] /\ term[r] = req.epoch
    /\ reportMessages' = reportMessages \cup
         {[sender |-> r, receiver |-> req.owner, epoch |-> req.epoch,
           entries |-> formal[r], pending |-> IF MutDropPending THEN {} ELSE retained[r]]}
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   applied, voteRequests, voteMessages, recoveryRequests,
                   offers, proposals, ackMessages, confirmations, commitMessages>>

DeliverReport(c, m) ==
    /\ m \in reportMessages /\ m.receiver = c /\ alive[c]
    /\ role[c] = "LeaderCandidate" /\ phase[c] = "collect"
    /\ term[c] = m.epoch /\ reports[c][m.sender] = NoReport
    /\ reports' = [reports EXCEPT ![c][m.sender] = m]
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, voteInbox, ackInbox, knownCommitted, applied,
                   voteRequests, voteMessages, recoveryRequests, reportMessages,
                   offers, proposals, ackMessages, confirmations, commitMessages>>

BuildRecovery(c, selected) ==
    LET L == Recovered(c, selected)
        e == Entry(LastIndex(L) + 1, term[c], Cur(L) + 1,
                   NoValue, "noop", Count(L, Cur(L)))
        p == Proposal(c, term[c], L, e, TRUE)
    IN /\ alive[c] /\ role[c] = "LeaderCandidate" /\ phase[c] = "collect"
       /\ c \in Reporters(c) /\ Quorum(Reporters(c))
       /\ IF ReportedProposals(c) = {}
             THEN /\ selected = NoProposal /\ ReportedEntries(c) = {}
             ELSE selected \in Latest(ReportedProposals(c))
       /\ LastIndex(L) + 1 \in Indices /\ Cur(L) + 1 \in Partitions
       /\ Count(L, Cur(L)) <= MaxPartitionSize
       /\ current' = [current EXCEPT ![c] = p]
       /\ phase' = [phase EXCEPT ![c] = "sync"]
       /\ stored' = [stored EXCEPT ![c] = @ \cup {e}]
       /\ proposals' = proposals \cup {p}
       /\ UNCHANGED <<term, vote, alive, role, formal, retained, reports,
                      voteInbox, ackInbox, knownCommitted, applied,
                      voteRequests, voteMessages, recoveryRequests,
                      reportMessages, offers, ackMessages, confirmations,
                      commitMessages>>

\* Normal ingestion has no boundary proposal or confirmation round.
CreateEntry(c, v) ==
    LET L == formal[c]
        e == Entry(LastIndex(L) + 1, term[c], Cur(L), v, "data",
                   Count(L, Cur(L) - 1))
    IN /\ alive[c] /\ role[c] = "Leader" /\ phase[c] = "serve"
       /\ v \in DataValues /\ Aligned(c, term[c])
       /\ Origin(L, Cur(L)) = term[c]
       /\ Count(L, Cur(L)) < MaxPartitionSize /\ LastIndex(L) + 1 \in Indices
       /\ formal' = [formal EXCEPT ![c] = @ \cup {e}]
       /\ stored' = [stored EXCEPT ![c] = @ \cup {e}]
       /\ UNCHANGED <<term, vote, alive, role, phase, retained, current,
                      reports, voteInbox, ackInbox, knownCommitted, applied,
                      voteRequests, voteMessages, recoveryRequests,
                      reportMessages, offers, proposals, ackMessages,
                      confirmations, commitMessages>>

CreateSuccessor(c, v, k) ==
    LET L == formal[c]
        e == Entry(LastIndex(L) + 1, term[c], Cur(L) + 1, v, k,
                   Count(L, Cur(L)))
    IN /\ alive[c] /\ role[c] = "Leader" /\ phase[c] = "serve"
       /\ Aligned(c, term[c])
       /\ LastIndex(L) + 1 \in Indices /\ Cur(L) + 1 \in Partitions
       /\ \/ /\ k = "data" /\ v \in DataValues
          \/ /\ k = "noop" /\ v = NoValue
             /\ \E x \in Part(L, Cur(L)) : x.kind = "data"
       /\ formal' = [formal EXCEPT ![c] = @ \cup {e}]
       /\ stored' = [stored EXCEPT ![c] = @ \cup {e}]
       /\ UNCHANGED <<term, vote, alive, role, phase, retained, current,
                      reports, voteInbox, ackInbox, knownCommitted, applied,
                      voteRequests, voteMessages, recoveryRequests,
                      reportMessages, offers, proposals, ackMessages,
                      confirmations, commitMessages>>

\* Reissuing an entry transmits the current committed count. Old packets stay.
SendEntry(c, e) ==
    /\ alive[c] /\ role[c] = "Leader" /\ phase[c] = "serve"
    /\ e \in formal[c] /\ e.term = term[c]
    /\ offers' = offers \cup {NormalMessage(c, e)}
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   applied, voteRequests, voteMessages, recoveryRequests,
                   reportMessages, proposals, ackMessages, confirmations,
                   commitMessages>>

ReceiveEntry(r, o) ==
    /\ o \in offers /\ CanReceive(r, o)
    /\ formal' = [formal EXCEPT ![r] = @ \cup {o.entry}]
    /\ stored' = [stored EXCEPT ![r] = @ \cup {o.entry}]
    /\ UNCHANGED <<term, vote, alive, role, phase, retained, current,
                   reports, voteInbox, ackInbox, knownCommitted, applied,
                   voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages,
                   confirmations, commitMessages>>

AckEntry(r, o) ==
    /\ o \in offers /\ alive[r] /\ term[r] = o.epoch
    /\ o.entry \in formal[r]
    /\ ackMessages' = ackMessages \cup
         {Ack(r, o.owner, o.epoch, o.entry, {o.entry})}
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   applied, voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, confirmations,
                   commitMessages>>

\* Copy one missing entry at a time. A crash or new term can occur between
\* any copies. Copying never changes the installed log or open/closed status.
CopyProposalEntry(r, source, p, e) ==
    /\ p \in proposals /\ alive[r] /\ alive[source]
    /\ term[r] = p.epoch /\ e \in Result(p) \cap stored[source]
    /\ stored' = [stored EXCEPT ![r] = @ \cup {e}]
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, retained,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   applied, voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages,
                   confirmations, commitMessages>>

\* Only recovery retains an exact prefix. Partial copies cannot be ACKed.
RetainProposal(r, p) ==
    /\ p \in proposals /\ alive[r] /\ term[r] = p.epoch
    /\ Result(p) \subseteq stored[r]
    /\ retained' = [retained EXCEPT ![r] = @ \cup {p}]
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   applied, voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages,
                   confirmations, commitMessages>>

AckProposal(r, p) ==
    /\ p \in retained[r] /\ alive[r] /\ term[r] = p.epoch
    /\ Result(p) \subseteq stored[r]
    /\ ackMessages' = ackMessages \cup
         {Ack(r, p.owner, p.epoch, p.first, Result(p))}
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   applied, voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, confirmations,
                   commitMessages>>

DeliverAck(c, m) ==
    /\ m \in ackMessages /\ m.receiver = c /\ alive[c]
    /\ role[c] \in {"LeaderCandidate", "Leader"} /\ term[c] = m.epoch
    /\ ackInbox' = [ackInbox EXCEPT ![c] = @ \cup {m}]
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, knownCommitted, applied,
                   voteRequests, voteMessages, recoveryRequests, reportMessages,
                   offers, proposals, ackMessages, confirmations, commitMessages>>

ConfirmProposal(c) ==
    LET p == current[c]
    IN /\ alive[c] /\ role[c] = "LeaderCandidate"
       /\ phase[c] = "sync" /\ p # NoProposal /\ p.epoch = term[c]
       /\ p \in retained[c]
       /\ c \in ProposalAckers(c, p)
       /\ MutEarlyPublish \/ Quorum(ProposalAckers(c, p))
       /\ formal' = [formal EXCEPT ![c] = Publish(c, p)]
       /\ phase' = [phase EXCEPT ![c] = "commit"]
       /\ confirmations' = confirmations \cup {p}
       /\ UNCHANGED <<term, vote, alive, role, stored, retained, current,
                      reports, voteInbox, ackInbox, knownCommitted, applied,
                      voteRequests, voteMessages, recoveryRequests,
                      reportMessages, offers, proposals, ackMessages,
                      commitMessages>>

LearnConfirmation(r, p) ==
    /\ p \in confirmations /\ alive[r] /\ term[r] = p.epoch
    /\ p \in retained[r] /\ Result(p) \subseteq stored[r]
    /\ formal' = [formal EXCEPT ![r] =
         Publish(r, p)]
    /\ UNCHANGED <<term, vote, alive, role, phase, stored, retained, current,
                   reports, voteInbox, ackInbox, knownCommitted, applied,
                   voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages,
                   confirmations, commitMessages>>

\* All commitment uses the receiver's LOCAL ACK inbox and commitment
\* knowledge. Historical observers below never enable protocol actions.
CommitEntry(c, e) ==
    /\ alive[c]
    /\ \/ /\ role[c] = "Leader" /\ phase[c] \in {"serve", "sync"}
       \/ /\ role[c] = "LeaderCandidate" /\ phase[c] = "commit"
    /\ e \in formal[c] \ knownCommitted[c]
    /\ Prefix(formal[c], e.part - 1) \subseteq knownCommitted[c]
    /\ MutNoCommitQuorum \/ Quorum(Ackers(c, term[c], e))
    /\ knownCommitted' = [knownCommitted EXCEPT ![c] = @ \cup {e}]
    /\ commitMessages' = commitMessages \cup
         {[owner |-> c, epoch |-> term[c], entry |-> e]}
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, applied,
                   voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages, confirmations>>

\* Heartbeats re-advertise known commitment in the current authorizing term.
\* This can deliver old committed identities to a follower that missed the
\* original term's notification, including before its data arrive.
AdvertiseCommit(c, e) ==
    /\ alive[c] /\ e \in formal[c] \cap knownCommitted[c]
    /\ \/ /\ role[c] = "Leader" /\ phase[c] \in {"serve", "sync"}
       \/ /\ role[c] = "LeaderCandidate" /\ phase[c] = "commit"
    /\ commitMessages' = commitMessages \cup
         {[owner |-> c, epoch |-> term[c], entry |-> e]}
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   applied, voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages, confirmations>>

LearnCommit(r, m) ==
    /\ m \in commitMessages /\ alive[r] /\ term[r] = m.epoch
    /\ knownCommitted' = [knownCommitted EXCEPT ![r] = @ \cup {m.entry}]
    \* The identity remains known even when its data have not arrived.
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, applied,
                   voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages,
                   confirmations, commitMessages>>

Activate(c) ==
    LET p == current[c]
    IN /\ alive[c] /\ role[c] = "LeaderCandidate" /\ phase[c] = "commit"
       /\ p # NoProposal /\ p.epoch = term[c] /\ p.recovering
       /\ Result(p) \subseteq formal[c] \cap knownCommitted[c]
       /\ role' = [role EXCEPT ![c] = "Leader"]
       /\ phase' = [phase EXCEPT ![c] = "serve"]
       /\ UNCHANGED <<term, vote, alive, formal, stored, retained, current,
                      reports, voteInbox, ackInbox, knownCommitted, applied,
                      voteRequests, voteMessages, recoveryRequests,
                      reportMessages, offers, proposals, ackMessages,
                      confirmations, commitMessages>>

ApplyEntry(r, e) ==
    /\ alive[r] /\ e \in (formal[r] \cap knownCommitted[r]) \ applied[r]
    /\ Prefix(formal[r], e.part - 1) \subseteq applied[r]
    /\ applied' = [applied EXCEPT ![r] = @ \cup {e}]
    /\ UNCHANGED <<term, vote, alive, role, phase, formal, stored, retained,
                   current, reports, voteInbox, ackInbox, knownCommitted,
                   voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages,
                   confirmations, commitMessages>>

Crash(r) ==
    /\ alive[r]
    /\ alive' = [alive EXCEPT ![r] = FALSE]
    /\ role' = [role EXCEPT ![r] = "Follower"]
    /\ phase' = [phase EXCEPT ![r] = "idle"]
    /\ current' = [current EXCEPT ![r] = NoProposal]
    /\ reports' = [reports EXCEPT ![r] = EmptyReports]
    /\ voteInbox' = [voteInbox EXCEPT ![r] = {}]
    /\ ackInbox' = [ackInbox EXCEPT ![r] = {}]
    /\ UNCHANGED <<term, vote, formal, stored, retained, knownCommitted,
                   applied, voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages,
                   confirmations, commitMessages>>

Restart(r) ==
    /\ ~alive[r] /\ alive' = [alive EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<term, vote, role, phase, formal, stored, retained, current,
                   reports, voteInbox, ackInbox, knownCommitted, applied,
                   voteRequests, voteMessages, recoveryRequests,
                   reportMessages, offers, proposals, ackMessages,
                   confirmations, commitMessages>>

AdministrativeNext ==
    \/ \E c \in Replicas : StartElection(c) \/ WinElection(c) \/
                              ConfirmProposal(c) \/ Activate(c)
    \/ \E r \in Replicas, t \in Terms : AdoptTerm(r, t)
    \/ \E r \in Replicas, req \in voteRequests : GrantVote(r, req)
    \/ \E c \in Replicas, m \in voteMessages : DeliverVote(c, m)
    \/ \E r \in Replicas, req \in recoveryRequests : MakeReport(r, req)
    \/ \E c \in Replicas, m \in reportMessages : DeliverReport(c, m)
    \/ \E c \in Replicas :
         \E p \in Latest(ReportedProposals(c)) \cup {NoProposal} :
             BuildRecovery(c, p)
    \/ \E c \in Replicas : \E e \in formal[c] : SendEntry(c, e)
    \/ \E r \in Replicas, o \in offers : ReceiveEntry(r, o) \/ AckEntry(r, o)
    \/ \E r, source \in Replicas, p \in proposals :
         \E e \in Result(p) \cap stored[source] : CopyProposalEntry(r, source, p, e)
    \/ \E r \in Replicas, p \in proposals : RetainProposal(r, p) \/ AckProposal(r, p)
    \/ \E c \in Replicas, m \in ackMessages : DeliverAck(c, m)
    \/ \E r \in Replicas, p \in confirmations : LearnConfirmation(r, p)
    \/ \E c \in Replicas : \E e \in formal[c] : CommitEntry(c, e) \/ AdvertiseCommit(c, e)
    \/ \E r \in Replicas, m \in commitMessages : LearnCommit(r, m)
    \/ \E r \in Replicas : Crash(r) \/ Restart(r)

ProtocolNext ==
    \/ AdministrativeNext
    \/ \E c \in Replicas, v \in DataValues : CreateEntry(c, v)
    \/ \E c \in Replicas, v \in DataValues \cup {NoValue},
          k \in {"data", "noop"} : CreateSuccessor(c, v, k)
    \/ \E r \in Replicas : \E e \in formal[r] : ApplyEntry(r, e)

\* Independent certificates are computed from issued ACKs, never notices.
Evidence(messages) ==
    (UNION { {[epoch |-> t, entry |-> e] :
                e \in {x \in (UNION {a.contents : a \in messages}) :
                    \E c \in Replicas : Quorum(MessageAckers(messages, c, t, x))}}
            : t \in (Terms \ {0}) })
EvidenceEntries == {f.entry : f \in commitHistory}

\* Ghost context records the creator's exact preceding partitions. Protocol
\* actions never read it; it tests, rather than assumes, count completeness.
\* Majority-backed recovery results may be logically chosen before the owner
\* receives ACKs. Per-partition ordering is checked separately below.

Observe ==
    /\ winners' = winners \cup
         {[node |-> r, epoch |-> term'[r]] :
          r \in {x \in Replicas : role'[x] = "LeaderCandidate"}}
    /\ leaderViews' = leaderViews \cup
         {[node |-> r, epoch |-> term'[r], entries |-> formal'[r]] :
          r \in {x \in Replicas : role'[x] = "Leader"}}
    /\ entryContexts' = entryContexts \cup
         (UNION { {[entry |-> e, prefix |-> Prefix(formal'[r], e.part - 1)] :
                    e \in {x \in formal'[r] : x.term = term'[r]}} :
                   r \in {n \in Replicas : role'[n] = "Leader"}}) \cup
         {[entry |-> p.first, prefix |-> p.prefix] : p \in proposals'}
    /\ commitHistory' = commitHistory \cup Evidence(ackMessages')
    /\ partitionHistory' =
         LET closed == (UNION {
               {[epoch |-> term'[r], part |-> q, entries |-> Part(formal'[r], q)] :
                  q \in {j \in Partitions : /\ j < Cur(formal'[r])
                                            /\ Part(formal'[r], j) # {}}} :
                 r \in Replicas })
         IN partitionHistory \cup (UNION {
              {[epoch |-> t, part |-> v.part, entries |-> v.entries] :
                 t \in {u \in (Terms \ {0}) : /\ u >= v.epoch
                    /\ \A e \in v.entries : \E f \in commitHistory' :
                         /\ f.entry = e /\ f.epoch <= u}} : v \in closed })

    /\ appliedPartitionHistory' = appliedPartitionHistory \cup
         (UNION { {[node |-> r, part |-> q, entries |-> Part(formal'[r], q)] :
                    q \in {j \in 0..(Cur(formal'[r]) - 1) :
                        /\ Part(formal'[r], j) # {}
                        /\ Part(formal'[r], j) \subseteq applied'[r]}} :
                  r \in Replicas })
    /\ applicationOrderOK' = (applicationOrderOK /\
         (\A r \in Replicas :
             /\ applied[r] \subseteq applied'[r]
             /\ \A e \in applied'[r] \ applied[r] :
                  /\ e \in formal[r] \cap knownCommitted[r]
                  /\ Prefix(formal[r], e.part - 1) \subseteq applied[r]))
    /\ appendOnlyOK' =
         (appendOnlyOK /\ \A r \in Replicas :
            (role[r] = "Leader" /\ role'[r] = "Leader" /\ term[r] = term'[r])
            => formal[r] \subseteq formal'[r])

Next == ProtocolNext /\ Observe
Spec == Init /\ [][Next]_vars

\* Safety targets. No protocol action reads the history observers.
\* TLC results are bounded checks, not an unbounded TLAPS proof.
TypeOK ==
    /\ term \in [Replicas -> Terms]
    /\ vote \in [Replicas -> Replicas \cup {NoNode}]
    /\ alive \in [Replicas -> BOOLEAN]
    /\ role \in [Replicas -> Roles] /\ phase \in [Replicas -> Phases]
    /\ formal \in [Replicas -> SUBSET Entries]
    /\ stored \in [Replicas -> SUBSET Entries]
    /\ knownCommitted \in [Replicas -> SUBSET Entries]
    /\ applied \in [Replicas -> SUBSET Entries]
    /\ retained \in [Replicas -> SUBSET proposals]
    /\ \A r \in Replicas :
         /\ formal[r] \subseteq stored[r] /\ Coherent(formal[r])
         /\ current[r] = NoProposal \/ current[r] \in proposals
         /\ voteInbox[r] \subseteq voteMessages /\ ackInbox[r] \subseteq ackMessages
         /\ \A p \in retained[r] : Result(p) \subseteq stored[r]
         /\ \A s \in Replicas : reports[r][s] = NoReport \/
                                  reports[r][s] \in reportMessages
    /\ \A p \in proposals :
         /\ p \in ProposalRecords
         /\ p.owner \in Replicas /\ p.epoch \in (Terms \ {0})
         /\ p.first \in Entries /\ p.first.term = p.epoch
         /\ p.prefix \subseteq Entries /\ Coherent(Result(p))
         /\ p.first.part = Cur(p.prefix) + 1
         /\ p.first.index = LastIndex(p.prefix) + 1
         /\ p.first.prevSize = Count(p.prefix, Cur(p.prefix))
    /\ appendOnlyOK \in BOOLEAN /\ applicationOrderOK \in BOOLEAN

ElectionSafety ==
    \A a, b \in winners : a.epoch = b.epoch => a.node = b.node
LeaderAppendOnly == appendOnlyOK
\* Paper Property 1 includes open/open and open/closed copies. "Up to"
\* means strictly preceding partitions, and matching entries need not be
\* identical. This also checks the partition formulation of the property.
LogMatching ==
    \A r, s \in Replicas, p \in Partitions :
        (/\ Part(formal[r], p) # {} /\ Part(formal[s], p) # {}
         /\ Origin(formal[r], p) = Origin(formal[s], p))
        => Prefix(formal[r], p - 1) = Prefix(formal[s], p - 1)
\* A leader may close an UNCOMMITTED normal partition before any follower
\* receives its successor. Recovery may discard that uncommitted membership.
\* Therefore the historical staged model's unconditional closed/closed
\* equality is not a property of this protocol. Check committed histories.
CommittedPartitionAgreement ==
    \A a, b \in partitionHistory : a.part = b.part => a.entries = b.entries

IntraPartitionRankEquivalence ==
    \A r, s \in Replicas :
        (/\ Cur(formal[r]) >= 0 /\ Cur(formal[r]) = Cur(formal[s])
         /\ Origin(formal[r], Cur(formal[r])) = Origin(formal[s], Cur(formal[s]))
         /\ Count(formal[r], Cur(formal[r])) = Count(formal[s], Cur(formal[s])))
        => /\ ClosedPrefix(formal[r]) = ClosedPrefix(formal[s])
           /\ Rank(formal[r]) = Rank(formal[s])
PartitionLeaderCompleteness ==
    \A fact \in partitionHistory, view \in leaderViews :
        view.epoch > fact.epoch => Part(view.entries, fact.part) = fact.entries
EntryLeaderCompleteness ==
    \A fact \in commitHistory, view \in leaderViews :
        view.epoch > fact.epoch => fact.entry \in view.entries
StateMachineSafety ==
    \A r, s \in Replicas : \A e \in applied[r], f \in applied[s] :
        e.index = f.index => e = f
PartitionStateMachineSafety ==
    \A a, b \in appliedPartitionHistory :
        a.part = b.part => a.entries = b.entries
ApplicationOrder == applicationOrderOK
CommittedKnowledgeSound ==
    \A r \in Replicas : \A e \in knownCommitted[r] :
        \E fact \in commitHistory : fact.entry = e
AppliedEntriesPreserved ==
    \A r \in Replicas : applied[r] \subseteq formal[r]
\* Diagnostics make guards below observable: incoherent recovery is a
\* specification error, rather than silently disabling BuildRecovery.
QuorumProposalPreservation ==
    \A p \in proposals :
      Quorum({r \in Replicas :
                Ack(r, p.owner, p.epoch, p.first, Result(p)) \in ackMessages}) =>
        /\ \A q \in proposals :
             (q.recovering /\ q.epoch > p.epoch) => Result(p) \subseteq q.prefix
        /\ \A v \in leaderViews :
             v.epoch > p.epoch => Result(p) \subseteq v.entries
RecoveryPreservesCommitted ==
    \A q \in proposals, fact \in commitHistory :
        (q.recovering /\ q.epoch > fact.epoch) => fact.entry \in q.prefix
RecoveryReportsHaveOrigin ==
    \A c \in Replicas :
      (/\ role[c] = "LeaderCandidate" /\ phase[c] = "collect"
       /\ c \in Reporters(c) /\ Quorum(Reporters(c))) =>
        (ReportedEntries(c) # {} => ReportedProposals(c) # {})
RecoveryUnionCoherent ==
    \A c \in Replicas :
      (/\ role[c] = "LeaderCandidate" /\ phase[c] = "collect"
       /\ c \in Reporters(c) /\ Quorum(Reporters(c))) =>
        \A p \in Latest(ReportedProposals(c)) : Coherent(Recovered(c, p))
RecoveryCandidatesPreserveEvidence ==
    \A c \in Replicas :
      (/\ role[c] = "LeaderCandidate" /\ phase[c] = "collect"
       /\ c \in Reporters(c) /\ Quorum(Reporters(c))) =>
        \A p \in Latest(ReportedProposals(c)), f \in commitHistory :
            f.epoch < term[c] => f.entry \in Recovered(c, p)

CommitEvidenceSound == commitHistory = Evidence(ackMessages)
CommitEvidenceAgreement ==
    \A a, b \in commitHistory : a.entry.index = b.entry.index => a.entry = b.entry
CommitNoticeHasQuorum ==
    \A m \in commitMessages :
        Quorum(MessageAckers(ackMessages, m.owner, m.epoch, m.entry))
ConfirmationHasQuorum ==
    \A p \in confirmations :
        Quorum({r \in Replicas :
            Ack(r, p.owner, p.epoch, p.first, Result(p)) \in ackMessages})
AckDurability == \A a \in ackMessages : a.contents \subseteq stored[a.sender]
EvidenceRespectsPartitionOrder ==
    \A f \in commitHistory, ctx \in entryContexts :
        ctx.entry = f.entry =>
            \A e \in ctx.prefix : \E prior \in commitHistory :
                /\ prior.entry = e /\ prior.epoch <= f.epoch
NormalCountCheckSound ==
    \A r \in Replicas, o \in offers, ctx \in entryContexts :
        (CanReceive(r, o) /\ ctx.entry = o.entry) =>
            Prefix(formal[r], o.entry.part - 1) = ctx.prefix
EntryContextUnique ==
    /\ \A a, b \in entryContexts : a.entry = b.entry => a.prefix = b.prefix
    /\ \A f \in commitHistory : \E ctx \in entryContexts : ctx.entry = f.entry

\* Non-vacuity predicates are deliberately negated in witness configs.
NoLeader == ~\E r \in Replicas : role[r] = "Leader"
NoDataCommit == ~\E f \in commitHistory : f.entry.kind = "data"
NoAppliedData == ~\E r \in Replicas : \E e \in applied[r] : e.kind = "data"
NoSecondTermLeader == ~\E v \in leaderViews : v.epoch >= 2
NoRecoveredData == ~\E v \in leaderViews :
                       \E e \in v.entries : e.kind = "data" /\ e.term < v.epoch
NoOpenHole == ~\E r \in Replicas : \E e, f \in offers :
                 /\ e.entry.index < f.entry.index
                 /\ e.entry.part = f.entry.part
                 /\ f.entry \in formal[r] /\ e.entry \notin formal[r]
NoInterruptedRecovery == ~\E p, q \in proposals :
                 /\ p.recovering /\ q.recovering /\ p.epoch < q.epoch
                 /\ p \notin confirmations /\ Result(p) \subseteq q.prefix
Safety == /\ TypeOK /\ ElectionSafety /\ LeaderAppendOnly
          /\ LogMatching /\ CommittedPartitionAgreement
          /\ IntraPartitionRankEquivalence
          /\ PartitionLeaderCompleteness /\ EntryLeaderCompleteness
          /\ StateMachineSafety /\ PartitionStateMachineSafety
          /\ ApplicationOrder /\ CommittedKnowledgeSound
          /\ AppliedEntriesPreserved /\ RecoveryUnionCoherent
          /\ RecoveryCandidatesPreserveEvidence /\ RecoveryReportsHaveOrigin
          /\ QuorumProposalPreservation /\ RecoveryPreservesCommitted
          /\ CommitEvidenceSound /\ CommitEvidenceAgreement
          /\ CommitNoticeHasQuorum /\ ConfirmationHasQuorum
          /\ AckDurability /\ EvidenceRespectsPartitionOrder
          /\ NormalCountCheckSound /\ EntryContextUnique

=============================================================================
