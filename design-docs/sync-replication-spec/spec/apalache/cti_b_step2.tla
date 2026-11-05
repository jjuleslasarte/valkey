---------------------------- MODULE counterexample ----------------------------

EXTENDS CoreApalache

(* Constant initialization state *)
ConstInit == EarlyDrop = FALSE/\ MaxLen = 2/\ MaxVer = 6/\ ReconcileFirst = TRUE

(* Initial state [_transition(0)] *)
State0 ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 2>>, <<"n2", 0>>, <<"n3", 1>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {}, prim |-> "n3", ver |-> 5]
    /\ commit = SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 2>> })
    /\ hist = <<6, 0>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n3", ver |-> 3]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 2]>>,
        <<"n3", [elig |-> {}, prim |-> "n3", ver |-> 5]>> })
    /\ log
      = SetAsFun({ <<"n1", <<6>>>>, <<"n2", <<6, 0>>>>, <<"n3", <<6, 0>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 2>>, <<"n3", 1>> })
    /\ sync = SetAsFun({ <<"n1", {}>>, <<"n2", {}>>, <<"n3", {"n1"}>> })
    /\ term = SetAsFun({ <<"n1", 4>>, <<"n2", 0>>, <<"n3", 1>> })

(* State1 [_transition(8)] *)
State1 ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 2>>, <<"n2", 0>>, <<"n3", 1>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {"n1"}, prim |-> "n3", ver |-> 6]
    /\ commit = SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 2>> })
    /\ hist = <<6, 0>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n3", ver |-> 3]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 2]>>,
        <<"n3", [elig |-> {"n1"}, prim |-> "n3", ver |-> 6]>> })
    /\ log
      = SetAsFun({ <<"n1", <<6>>>>, <<"n2", <<6, 0>>>>, <<"n3", <<6, 0>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 2>>, <<"n3", 1>> })
    /\ sync = SetAsFun({ <<"n1", {}>>, <<"n2", {}>>, <<"n3", {"n1"}>> })
    /\ term = SetAsFun({ <<"n1", 4>>, <<"n2", 0>>, <<"n3", 1>> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Skolem((\E n_44 \in cfg["elig"] \union {cfg["prim"]}:
    Len(hist) > Len(log[n_44])))

================================================================================
(* Created by Apalache on Wed Nov 04 17:12:18 UTC 2026 *)
(* https://github.com/apalache-mc/apalache *)
