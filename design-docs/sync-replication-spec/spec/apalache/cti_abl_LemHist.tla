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
          "n1", (SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 1>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 1>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 2>> }))>> })
    /\ cfg = [elig |-> {}, prim |-> "n2", ver |-> 4]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 1>>, <<"n3", 0>> })
    /\ hist = <<1, 4>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n3", ver |-> 3]>>,
        <<"n2", [elig |-> {}, prim |-> "n2", ver |-> 4]>>,
        <<"n3", [elig |-> {}, prim |-> "n2", ver |-> 2]>> })
    /\ log = SetAsFun({ <<"n1", <<3>>>>, <<"n2", <<1, 4>>>>, <<"n3", <<1>>>> })
    /\ recon = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 1>> })
    /\ sync = SetAsFun({ <<"n1", {"n2"}>>, <<"n2", {"n3"}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 4>>, <<"n2", 4>>, <<"n3", 0>> })

(* State1 [_transition(8)] *)
State1 ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 1>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 1>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 2>> }))>> })
    /\ cfg = [elig |-> {"n3"}, prim |-> "n2", ver |-> 5]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 1>>, <<"n3", 0>> })
    /\ hist = <<1, 4>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n3", ver |-> 3]>>,
        <<"n2", [elig |-> {"n3"}, prim |-> "n2", ver |-> 5]>>,
        <<"n3", [elig |-> {}, prim |-> "n2", ver |-> 2]>> })
    /\ log = SetAsFun({ <<"n1", <<3>>>>, <<"n2", <<1, 4>>>>, <<"n3", <<1>>>> })
    /\ recon = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 1>> })
    /\ sync = SetAsFun({ <<"n1", {"n2"}>>, <<"n2", {"n3"}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 4>>, <<"n2", 4>>, <<"n3", 0>> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Skolem((\E n_41 \in cfg["elig"] \union {cfg["prim"]}:
    Len(hist) > Len(log[n_41])))

================================================================================
(* Created by Apalache on Wed Nov 04 18:09:10 UTC 2026 *)
(* https://github.com/apalache-mc/apalache *)
