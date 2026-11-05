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
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {}, prim |-> "n1", ver |-> 1]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n3", [elig |-> {}, prim |-> "n1", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<>>>>, <<"n2", <<>>>>, <<"n3", <<>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ sync = SetAsFun({ <<"n1", {}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> })

(* State1 [_transition(7)] *)
State1 ==
  EarlyDrop = TRUE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {}, prim |-> "n1", ver |-> 1]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n3", [elig |-> {}, prim |-> "n1", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<>>>>, <<"n2", <<>>>>, <<"n3", <<>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ sync = SetAsFun({ <<"n1", {"n2"}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> })

(* State2 [_transition(8)] *)
State2 ==
  EarlyDrop = TRUE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n3", [elig |-> {}, prim |-> "n1", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<>>>>, <<"n2", <<>>>>, <<"n3", <<>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ sync = SetAsFun({ <<"n1", {"n2"}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> })

(* State3 [_transition(0)] *)
State3 ==
  EarlyDrop = TRUE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n3", [elig |-> {}, prim |-> "n1", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<1>>>>, <<"n2", <<>>>>, <<"n3", <<>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ sync = SetAsFun({ <<"n1", {"n2"}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> })

(* State4 [_transition(10)] *)
State4 ==
  EarlyDrop = TRUE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n3", [elig |-> {}, prim |-> "n1", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<1>>>>, <<"n2", <<>>>>, <<"n3", <<>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ sync = SetAsFun({ <<"n1", {}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> })

(* State5 [_transition(3)] *)
State5 ==
  EarlyDrop = TRUE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))>> })
    /\ cfg = [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]
    /\ commit = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<1>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n2"}, prim |-> "n1", ver |-> 2]>>,
        <<"n2", [elig |-> {}, prim |-> "n1", ver |-> 1]>>,
        <<"n3", [elig |-> {}, prim |-> "n1", ver |-> 1]>> })
    /\ log = SetAsFun({ <<"n1", <<1>>>>, <<"n2", <<>>>>, <<"n3", <<>>>> })
    /\ recon = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ sync = SetAsFun({ <<"n1", {}>>, <<"n2", {}>>, <<"n3", {}>> })
    /\ term = SetAsFun({ <<"n1", 1>>, <<"n2", 0>>, <<"n3", 0>> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Skolem((\E n_16 \in cfg["elig"] \union {cfg["prim"]}:
    Len(hist) > Len(log[n_16])))

================================================================================
(* Created by Apalache on Wed Nov 04 17:15:34 UTC 2026 *)
(* https://github.com/apalache-mc/apalache *)
