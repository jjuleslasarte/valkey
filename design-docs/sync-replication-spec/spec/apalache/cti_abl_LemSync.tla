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
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 2>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 2>> }))>> })
    /\ cfg = [elig |-> {}, prim |-> "n2", ver |-> 4]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n2", ver |-> 4]>>,
        <<"n2", [elig |-> {}, prim |-> "n2", ver |-> 4]>>,
        <<"n3", [elig |-> {"n1"}, prim |-> "n3", ver |-> 3]>> })
    /\ log
      = SetAsFun({ <<"n1", <<0, 0>>>>, <<"n2", <<>>>>, <<"n3", <<3, 5>>>> })
    /\ recon = SetAsFun({ <<"n1", 2>>, <<"n2", 0>>, <<"n3", 1>> })
    /\ sync = SetAsFun({ <<"n1", {}>>, <<"n2", {"n2"}>>, <<"n3", {"n1"}>> })
    /\ term = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 5>> })

(* State1 [_transition(8)] *)
State1 ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 2>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 2>> }))>> })
    /\ cfg = [elig |-> {"n2"}, prim |-> "n2", ver |-> 5]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n2", ver |-> 4]>>,
        <<"n2", [elig |-> {"n2"}, prim |-> "n2", ver |-> 5]>>,
        <<"n3", [elig |-> {"n1"}, prim |-> "n3", ver |-> 3]>> })
    /\ log
      = SetAsFun({ <<"n1", <<0, 0>>>>, <<"n2", <<>>>>, <<"n3", <<3, 5>>>> })
    /\ recon = SetAsFun({ <<"n1", 2>>, <<"n2", 0>>, <<"n3", 1>> })
    /\ sync = SetAsFun({ <<"n1", {}>>, <<"n2", {"n2"}>>, <<"n3", {"n1"}>> })
    /\ term = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 5>> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == cfg["prim"] \in cfg["elig"]

================================================================================
(* Created by Apalache on Wed Nov 04 18:09:14 UTC 2026 *)
(* https://github.com/apalache-mc/apalache *)
