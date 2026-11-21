import CommitGolfCandidate.ChainedLevelState

/-! Native node-count induction through an entire descending heap level. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def levelTrace (h : Height) : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | remaining+1,s => do
    let next ← nodeTrace h s
    levelTrace h remaining next

theorem level_trace_ready (remaining : Nat) (s out : MachineState) (h : Height)
    (ready : LevelReady s h remaining) (reached : out ∈ support (levelTrace h remaining s)) :
    LevelReady out h 0 := by
  induction remaining generalizing s with
  | zero =>
    simp only [levelTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ready
  | succ remaining ih =>
    simp only [levelTrace,mem_support_bind_iff] at reached
    obtain ⟨next,first,last⟩ := reached
    exact ih next (ready.node next first) last

theorem level_execution (remaining : Nat) (s : MachineState) (h : Height)
    (ready : LevelReady s h remaining) (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (parentNodeSteps h*remaining+fuel) s coins =
      (do let out ← levelTrace h remaining s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (parentNodeCycles h*remaining) (calls h*remaining)) := by
  induction remaining generalizing s with
  | zero => simp [levelTrace,Execution.charge]
  | succ remaining ih =>
    have pc : s.pc = bodyPC h := by simpa only [Nat.add_one_ne_zero,ite_false] using ready.pc
    have inputs : ∀ k : Fin 8, accessValid (s.getReg .x6+BitVec.ofNat 64 (8*k.val)) 8 = true := by
      simpa only [cursor_at_zero] using ready.inputs 0 (by omega)
    have outputs : ∀ k : Fin 4, accessValid (s.getReg .x7+BitVec.ofNat 64 (8*k.val)) 8 = true := by
      simpa only [cursor_at_zero] using ready.outputs 0 (by omega)
    rw [show parentNodeSteps h*(remaining+1)+fuel =
      parentNodeSteps h+(parentNodeSteps h*remaining+fuel) by rw [Nat.mul_succ]; omega,
      node_execution s h ready.args pc inputs outputs]
    simp only [levelTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (ready.node next reached)]
    have cycles : parentNodeCycles h+parentNodeCycles h*remaining = parentNodeCycles h*(remaining+1) := by
      rw [Nat.mul_succ]
      omega
    have queries : calls h+calls h*remaining = calls h*(remaining+1) := by
      rw [Nat.mul_succ]
      omega
    simp [Execution.charge,←Nat.add_assoc,cycles,queries]

theorem level_query_bound (remaining : Nat) (s : MachineState) (h : Height) :
    PublicQueryBound (levelTrace h remaining s) (calls h*remaining) := by
  induction remaining generalizing s with
  | zero => trivial
  | succ remaining ih =>
    have bounded : PublicQueryBound (levelTrace h (remaining+1) s) (calls h+calls h*remaining) :=
      public_query_bound_bind (node_query_bound s h) (fun next => ih next)
    exact bounded.mono (by rw [Nat.mul_succ]; omega)

theorem level_trace_register (remaining : Nat) (s out : MachineState) (h : Height)
    (reached : out ∈ support (levelTrace h remaining s)) (reg : Reg)
    (kept : reg ∉ ([.x1,.x6,.x7,.x14,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30] : List Reg)) :
    out.getReg reg = s.getReg reg := by
  induction remaining generalizing s with
  | zero =>
    simp only [levelTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    rfl
  | succ remaining ih =>
    simp only [levelTrace,mem_support_bind_iff] at reached
    obtain ⟨next,first,last⟩ := reached
    exact (ih next last).trans (node_register s next h first reg kept)

end CommitGolfCandidate.Chained.Native
