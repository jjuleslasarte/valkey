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
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 1>>, <<"n2", 1>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 2>>, <<"n2", 0>>, <<"n3", 1>> }))>> })
    /\ cfg = [elig |-> {"n3"}, prim |-> "n1", ver |-> 1]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<1>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n2"}, prim |-> "n2", ver |-> 2]>>,
        <<"n2", [elig |-> { "n1", "n3" }, prim |-> "n2", ver |-> 5]>>,
        <<"n3", [elig |-> { "n1", "n2" }, prim |-> "n2", ver |-> 5]>> })
    /\ log
      = SetAsFun({ <<"n1", <<1, 3>>>>, <<"n2", <<1, 3>>>>, <<"n3", <<1, 4>>>> })
    /\ recon = SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 2>> })
    /\ sync
      = SetAsFun({ <<"n1", {"n3"}>>,
        <<"n2", { "n1", "n3" }>>,
        <<"n3", { "n1", "n2" }>> })
    /\ term = SetAsFun({ <<"n1", 5>>, <<"n2", 3>>, <<"n3", 5>> })

(* State1 [_transition(2)] *)
State1 ==
  EarlyDrop = FALSE
    /\ MaxLen = 2
    /\ MaxVer = 6
    /\ Nodes = { "n1", "n2", "n3" }
    /\ ReconcileFirst = TRUE
    /\ acked
      = SetAsFun({ <<
          "n1", (SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> }))
        >>,
        <<"n2", (SetAsFun({ <<"n1", 2>>, <<"n2", 1>>, <<"n3", 0>> }))>>,
        <<"n3", (SetAsFun({ <<"n1", 2>>, <<"n2", 0>>, <<"n3", 1>> }))>> })
    /\ cfg = [elig |-> {"n3"}, prim |-> "n1", ver |-> 1]
    /\ commit = SetAsFun({ <<"n1", 0>>, <<"n2", 0>>, <<"n3", 0>> })
    /\ hist = <<1>>
    /\ known
      = SetAsFun({ <<"n1", [elig |-> {"n2"}, prim |-> "n2", ver |-> 2]>>,
        <<"n2", [elig |-> { "n1", "n3" }, prim |-> "n2", ver |-> 5]>>,
        <<"n3", [elig |-> { "n1", "n2" }, prim |-> "n2", ver |-> 5]>> })
    /\ log
      = SetAsFun({ <<"n1", <<1, 3>>>>, <<"n2", <<1, 3>>>>, <<"n3", <<1, 4>>>> })
    /\ recon = SetAsFun({ <<"n1", 1>>, <<"n2", 2>>, <<"n3", 2>> })
    /\ sync
      = SetAsFun({ <<"n1", {"n3"}>>,
        <<"n2", { "n1", "n3" }>>,
        <<"n3", { "n1", "n2" }>> })
    /\ term = SetAsFun({ <<"n1", 5>>, <<"n2", 3>>, <<"n3", 5>> })

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  Skolem((\E q_3 \in Nodes:
    (known[q_3]["prim"] = q_3 /\ ~(q_3 = cfg["prim"]))
      /\ (q_3 \in cfg["elig"]
        \/ ((Skolem((\E h_3 \in cfg["elig"] \union {cfg["prim"]}:
              ~(h_3 \in sync[q_3])
                \/ ((acked[q_3][h_3] > Len(log[q_3])
                    \/ acked[q_3][h_3] > Len(log[h_3]))
                  \/ ~(SubSeq(log[q_3], 1, acked[q_3][h_3])
                    = SubSeq(log[h_3], 1, acked[q_3][h_3])))))
            \/ acked[q_3][cfg["prim"]] > recon[cfg["prim"]])
          /\ (\A s_3 \in sync[q_3]:
            known[s_3]["prim"] = q_3
              \/ acked[q_3][s_3] > Len(log[q_3])
              \/ (Len((SubSeq(log[q_3], 1, acked[q_3][s_3]))) > Len(hist)
                \/ ~(SubSeq(hist, 1, (Len((SubSeq(log[q_3], 1, acked[q_3][s_3])))))
                  = SubSeq(log[q_3], 1, acked[q_3][s_3]))))))))

================================================================================
(* Created by Apalache on Wed Nov 04 18:24:37 UTC 2026 *)
(* https://github.com/apalache-mc/apalache *)
