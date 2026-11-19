------------------------- MODULE TRaftEpochClosureProof ----------------------
EXTENDS Integers, TLAPS

\* Only the observer's authorization-epoch field is extended. Physical
\* replica state, entry identity and application state are left untouched.
EpochClosure(H) == (UNION {
    {[epoch |-> t, part |-> h.part, entries |-> h.entries] :
       t \in {u \in Nat \ {0} : u >= h.epoch}} : h \in H})
CertifiedClosed(D, C, U) == (UNION {
    {[epoch |-> t, part |-> v.part, entries |-> v.entries] :
       t \in {u \in U : u >= v.epoch /\
         \A e \in v.entries : \E f \in C : f.entry = e /\ f.epoch <= u}} : v \in D})

THEOREM EpochClosureOfEmpty == EpochClosure({}) = {}
BY ZenonT(5) DEF EpochClosure

THEOREM EpochClosureMember ==
    ASSUME NEW H, NEW x
    PROVE x \in EpochClosure(H) <=>
      \E h \in H : \E t \in Nat \ {0} :
        t >= h.epoch /\ x = [epoch |-> t, part |-> h.part, entries |-> h.entries]
BY IsaM("auto") DEF EpochClosure

THEOREM EpochClosureOfUnion ==
    ASSUME NEW A, NEW B
    PROVE EpochClosure(A \cup B) = EpochClosure(A) \cup EpochClosure(B)
<1>1. \A x : x \in EpochClosure(A \cup B) <=>
          x \in EpochClosure(A) \/ x \in EpochClosure(B)
    BY EpochClosureMember
<1> QED BY <1>1

THEOREM CertifiedClosedMember ==
    ASSUME NEW D, NEW C, NEW U, NEW x
    PROVE x \in CertifiedClosed(D, C, U) <=>
      \E v \in D : \E t \in U :
        /\ t >= v.epoch
        /\ \A e \in v.entries : \E f \in C : f.entry = e /\ f.epoch <= t
        /\ x = [epoch |-> t, part |-> v.part, entries |-> v.entries]
BY SMT DEF CertifiedClosed

THEOREM BoundedCertificateExtendsToLaterEpoch ==
    ASSUME NEW T \in Nat \ {0}, NEW D, NEW C,
           \A v \in D : v.epoch \in Nat,
           \A f \in C : f.epoch \in Nat,
           NEW x \in EpochClosure(CertifiedClosed(D, C, 1..T))
    PROVE x \in CertifiedClosed(D, C, Nat \ {0})
<1>1. PICK h \in CertifiedClosed(D, C, 1..T), t \in Nat \ {0} :
          t >= h.epoch /\ x = [epoch |-> t, part |-> h.part, entries |-> h.entries]
    BY EpochClosureMember
<1>2. PICK v \in D, u \in 1..T :
          u >= v.epoch /\ (\A e \in v.entries : \E f \in C : f.entry = e /\ f.epoch <= u)
          /\ h = [epoch |-> u, part |-> v.part, entries |-> v.entries]
    BY CertifiedClosedMember, <1>1
<1>3. t >= v.epoch
      /\ \A e \in v.entries : \E f \in C : f.entry = e /\ f.epoch <= t
    BY SMT, <1>1, <1>2
<1> QED BY CertifiedClosedMember, <1>1, <1>2, <1>3

THEOREM LaterCertificateHasBoundedRepresentative ==
    ASSUME NEW T \in Nat \ {0}, NEW D, NEW C,
           \A v \in D : v.epoch \in 0..T,
           \A f \in C : f.epoch \in 0..T,
           NEW x \in CertifiedClosed(D, C, Nat \ {0})
    PROVE x \in EpochClosure(CertifiedClosed(D, C, 1..T))
<1>1. PICK v \in D, t \in Nat \ {0} :
          t >= v.epoch /\ (\A e \in v.entries : \E f \in C : f.entry = e /\ f.epoch <= t)
          /\ x = [epoch |-> t, part |-> v.part, entries |-> v.entries]
    BY CertifiedClosedMember
<1>2. DEFINE u == IF t <= T THEN t ELSE T
            h == [epoch |-> u, part |-> v.part, entries |-> v.entries]
<1>3. u \in 1..T /\ u >= v.epoch /\ t >= u
    BY SMT, <1>1 DEF u
<1>4. \A e \in v.entries : \E f \in C : f.entry = e /\ f.epoch <= u
    BY SMT, <1>1 DEF u
<1>5. h \in CertifiedClosed(D, C, 1..T)
    BY CertifiedClosedMember, <1>1, <1>3, <1>4 DEF h
<1> QED BY EpochClosureMember, <1>1, <1>3, <1>5 DEF h

THEOREM EpochClosureCommutesWithCertification ==
    ASSUME NEW T \in Nat \ {0}, NEW D, NEW C,
           \A v \in D : v.epoch \in 0..T,
           \A f \in C : f.epoch \in 0..T
    PROVE EpochClosure(CertifiedClosed(D, C, 1..T)) = CertifiedClosed(D, C, Nat \ {0})
<1>1. (\A v \in D : v.epoch \in Nat) /\ (\A f \in C : f.epoch \in Nat)
    BY SMT
<1>2. EpochClosure(CertifiedClosed(D, C, 1..T)) \subseteq CertifiedClosed(D, C, Nat \ {0})
    BY BoundedCertificateExtendsToLaterEpoch, <1>1
<1>3. CertifiedClosed(D, C, Nat \ {0}) \subseteq EpochClosure(CertifiedClosed(D, C, 1..T))
    BY LaterCertificateHasBoundedRepresentative
<1> QED BY <1>2, <1>3

THEOREM EpochClosureCommutesWithHistoryGrowth ==
    ASSUME NEW T \in Nat \ {0}, NEW D, NEW C, NEW H,
           \A v \in D : v.epoch \in 0..T,
           \A f \in C : f.epoch \in 0..T
    PROVE EpochClosure(H \cup CertifiedClosed(D, C, 1..T))
            = EpochClosure(H) \cup CertifiedClosed(D, C, Nat \ {0})
BY EpochClosureOfUnion, EpochClosureCommutesWithCertification
=============================================================================
