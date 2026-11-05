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
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 1>>, <<"n3", 2>> }))>> })
    /\ cfg = [elig |-> {}, prim |-> "n2", ver |-> 5]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 1>>, <<"n3", 1>> })
    /\ hist = <<5>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n1"}, prim |-> "n1", ver |-> 4]>>,
        <<"n2", [elig |-> {}, prim |-> "n2", ver |-> 5]>>,
        <<"n3", [elig |-> { "n1", "n2" }, prim |-> "n3", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<6>>>>, <<"n2", <<5>>>>, <<"n3", <<5, 6>>>> })
    /\ recon = SetAsFun({ <<"n1", 2>>, <<"n2", 1>>, <<"n3", 2>> })
    /\ sync = SetAsFun({ <<"n1", {"n3"}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 6>>, <<"n2", 2>>, <<"n3", 6>> })

(* State1 [_transition(3)] *)
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
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 1>>, <<"n3", 2>> }))>> })
    /\ cfg = [elig |-> {}, prim |-> "n2", ver |-> 5]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 1>>, <<"n3", 2>> })
    /\ hist = <<5, 6>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n1"}, prim |-> "n1", ver |-> 4]>>,
        <<"n2", [elig |-> {}, prim |-> "n2", ver |-> 5]>>,
        <<"n3", [elig |-> { "n1", "n2" }, prim |-> "n3", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<6>>>>, <<"n2", <<5>>>>, <<"n3", <<5, 6>>>> })
    /\ recon = SetAsFun({ <<"n1", 2>>, <<"n2", 1>>, <<"n3", 2>> })
    /\ sync = SetAsFun({ <<"n1", {"n3"}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 6>>, <<"n2", 2>>, <<"n3", 6>> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Len(hist)
    > (IF commit[cfg["prim"]] >= recon[cfg["prim"]]
    THEN commit[cfg["prim"]]
    ELSE recon[cfg["prim"]])

================================================================================
(* Created by Apalache on Wed Nov 04 18:23:52 UTC 2026 *)
(* https://github.com/apalache-mc/apalache *)
