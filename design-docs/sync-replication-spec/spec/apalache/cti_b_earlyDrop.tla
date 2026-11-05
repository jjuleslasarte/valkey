---------------------------- MODULE counterexample ----------------------------

EXTENDS CoreApalache

(* Constant initialization state *)
ConstInit == EarlyDrop = TRUE/\ MaxLen = 2/\ MaxVer = 6/\ ReconcileFirst = TRUE

(* Initial state [_transition(0)] *)
State0 ==
  EarlyDrop = TRUE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 2>>, <<"n2", 1>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 1>>, <<"n2", 1>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {"n1"}, prim |-> "n2", ver |-> 2]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n2", ver |-> 1]>>,
        <<"n2", [elig |-> {"n1"}, prim |-> "n2", ver |-> 2]>>,
        <<"n3", [elig |-> {"n1"}, prim |-> "n1", ver |-> 1]>> })
    /\ log
      = SetAsFun({ <<"n1", <<1, 1>>>>, <<"n2", <<1, 1>>>>, <<"n3", <<1, 1>>>> })
    /\ recon = SetAsFun({ <<"n1", 2>>, <<"n2", 2>>, <<"n3", 2>> })
    /\ sync = SetAsFun({ <<"n1", {}>>, <<"n2", {"n1"}>>, <<"n3", {"n2"}>> })
    /\ term = SetAsFun({ <<"n1", 5>>, <<"n2", 2>>, <<"n3", 4>> })

(* State1 [_transition(10)] *)
State1 ==
  EarlyDrop = TRUE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 2>>, <<"n2", 1>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 1>>, <<"n2", 1>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {"n1"}, prim |-> "n2", ver |-> 2]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n2", ver |-> 1]>>,
        <<"n2", [elig |-> {"n1"}, prim |-> "n2", ver |-> 2]>>,
        <<"n3", [elig |-> {"n1"}, prim |-> "n1", ver |-> 1]>> })
    /\ log
      = SetAsFun({ <<"n1", <<1, 1>>>>, <<"n2", <<1, 1>>>>, <<"n3", <<1, 1>>>> })
    /\ recon = SetAsFun({ <<"n1", 2>>, <<"n2", 2>>, <<"n3", 2>> })
    /\ sync = SetAsFun({ <<"n1", {}>>, <<"n2", {}>>, <<"n3", {"n2"}>> })
    /\ term = SetAsFun({ <<"n1", 5>>, <<"n2", 2>>, <<"n3", 4>> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation == ~(\A t_1u_1 \in cfg["elig"]: t_1u_1 \in sync[cfg["prim"]])

================================================================================
(* Created by Apalache on Wed Nov 04 17:17:49 UTC 2026 *)
(* https://github.com/apalache-mc/apalache *)
