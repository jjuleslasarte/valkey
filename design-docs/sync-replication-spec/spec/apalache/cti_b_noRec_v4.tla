---------------------------- MODULE counterexample ----------------------------

EXTENDS CoreApalache

(* Constant initialization state *)
ConstInit ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ReconcileFirst = FALSE

(* Initial state [_transition(0)] *)
State0 ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ReconcileFirst = FALSE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 1>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 1>>, <<"n3", 2>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 1>> }))>> })
    /\ cfg = [elig |-> {}, prim |-> "n3", ver |-> 4]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n3", [elig |-> {}, prim |-> "n3", ver |-> 4]>> })
    /\ log = SetAsFun({ <<"n1", <<6>>>>, <<"n2", <<1>>>>, <<"n3", <<6>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 2>>, <<"n3", 1>> })
    /\ sync = SetAsFun({ <<"n1", {"n3"}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })

(* State1 [_transition(3)] *)
State1 ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ReconcileFirst = FALSE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 1>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 1>>, <<"n3", 2>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 1>> }))>> })
    /\ cfg = [elig |-> {}, prim |-> "n3", ver |-> 4]
    /\ commit = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<6>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n3", [elig |-> {}, prim |-> "n3", ver |-> 4]>> })
    /\ log = SetAsFun({ <<"n1", <<6>>>>, <<"n2", <<1>>>>, <<"n3", <<6>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 2>>, <<"n3", 1>> })
    /\ sync = SetAsFun({ <<"n1", {"n3"}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == Len(hist) > commit[cfg["prim"]]

================================================================================
(* Created by Apalache on Wed Nov 04 18:22:25 UTC 2026 *)
(* https://github.com/apalache-mc/apalache *)
