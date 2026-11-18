import CommitGolfCandidate.TwoPermutationRootBytes

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure)
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000
attribute [local irreducible] checkEvaluation leavesTrace fullParents rootPrefix parentSetup readyState

private theorem eval_finish (oracle : Oracle) (p : OracleComp World MachineState)
    (f : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (p >>= fun s => f s >>= fun t => pure (finish t))).1 =
      finish (checkEvaluation oracle (f (checkEvaluation oracle p).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

private theorem eval_body_at (oracle : Oracle) (s : MachineState) (count : Nat) :
    (checkEvaluation oracle (do
      let leaves ← leavesTrace count 0 s
      let parents ← fullParents (parentSetup leaves 5)
      return rootPrefix parents 10)).1 =
      rootPrefix (checkEvaluation oracle (fullParents (parentSetup
        (checkEvaluation oracle (leavesTrace count 0 s)).1 5))).1 10 :=
  eval_finish oracle (leavesTrace count 0 s)
    (fun leaves => fullParents (parentSetup leaves 5)) (fun parents => rootPrefix parents 10)

private theorem body_expansion (s : MachineState) {bits : Nat} (packed : BitVec bits) :
    commitBody s packed =
      (do let leaves ← leavesTrace (2^20) 0 (readyState s packed)
          let parents ← fullParents (parentSetup leaves 5)
          return rootPrefix parents 10) := rfl

private theorem packed_mk (s : MachineState) (oracle : Oracle) {bits : Nat} (packed : BitVec bits) :
    packedOutput s oracle packed=⟨.success,(checkEvaluation oracle (commitBody s packed)).1,691142677,50331647⟩ := rfl

private theorem mk_state (st : MachineState) : (⟨.success,st,691142677,50331647⟩ : Execution).state=st := rfl

theorem packed_state_eq (s : MachineState) (oracle : Oracle) {bits : Nat} (packed : BitVec bits) :
    (packedOutput s oracle packed).state = (checkEvaluation oracle (commitBody s packed)).1 :=
  (congrArg Execution.state (packed_mk s oracle packed)).trans (mk_state _)

attribute [local irreducible] commitBody

theorem state_of_body (s : MachineState) (oracle : Oracle) {bits : Nat} (packed : BitVec bits) :
    (packedOutput s oracle packed).state =
      rootPrefix (checkEvaluation oracle (fullParents (parentSetup
        (checkEvaluation oracle (leavesTrace (2^20) 0 (readyState s packed))).1 5))).1 10 :=
  (packed_state_eq s oracle packed).trans ((congrArg (fun p : OracleComp World MachineState => (checkEvaluation oracle p).1) (body_expansion s packed)).trans
    (eval_body_at oracle (readyState s packed) (2^20)))

end TwoPermutationPrototype.RV64
