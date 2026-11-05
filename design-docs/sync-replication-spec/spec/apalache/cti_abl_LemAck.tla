---------------------------- MODULE counterexample ----------------------------

EXTENDS CoreApalache

(* Constant initialization state *)
ConstInit ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ReconcileFirst = TRUE

(* Initial state [_transition(0)] *)
State0 ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 2>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 2>>, <<"n3", 2>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 2>> }))>> })
    /\ cfg = [elig |-> { "n2", "n3" }, prim |-> "n1", ver |-> 6]
    /\ commit = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<3>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> { "n2", "n3" }, prim |-> "n1", ver |-> 6]>>,
        <<"n2", [elig |-> {"n3"}, prim |-> "n1", ver |-> 3]>>,
        <<"n3", [elig |-> {"n3"}, prim |-> "n2", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<3, 6>>>>, <<"n2", <<3>>>>, <<"n3", <<3>>>> })
    /\ recon = SetAsFun({ <<"n1", 2>>, <<"n2", 1>>, <<"n3", 1>> })
    /\ sync
      = SetAsFun({ <<"n1", { "n2", "n3" }>>,
        <<"n2", { "n1", "n3" }>>,
        <<"n3", {"n2"}>> })
    /\ term = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })

(* State1 [_transition(3)] *)
State1 ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 2>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 2>>, <<"n3", 2>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 2>> }))>> })
    /\ cfg = [elig |-> { "n2", "n3" }, prim |-> "n1", ver |-> 6]
    /\ commit = SetAsFun({ <<"n1", 2>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<3, 6>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> { "n2", "n3" }, prim |-> "n1", ver |-> 6]>>,
        <<"n2", [elig |-> {"n3"}, prim |-> "n1", ver |-> 3]>>,
        <<"n3", [elig |-> {"n3"}, prim |-> "n2", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<3, 6>>>>, <<"n2", <<3>>>>, <<"n3", <<3>>>> })
    /\ recon = SetAsFun({ <<"n1", 2>>, <<"n2", 1>>, <<"n3", 1>> })
    /\ sync
      = SetAsFun({ <<"n1", { "n2", "n3" }>>,
        <<"n2", { "n1", "n3" }>>,
        <<"n3", {"n2"}>> })
    /\ term = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Skolem((\E n_41 \in cfg["elig"] \union {cfg["prim"]}:
    Len(hist) > Len(log[n_41])))

================================================================================
(* Created by Apalache on Wed Nov 04 18:24:31 UTC 2026 *)
(* https://github.com/apalache-mc/apalache *)
