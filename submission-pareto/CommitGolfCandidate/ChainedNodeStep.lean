import CommitGolfCandidate.ChainedBranch

/-! A delivered parent-node step, composed across separate decrement and BNE lemmas. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute cursorPrefix branchState

def nodeTrace (h : Height) (s : MachineState) : OracleComp World MachineState := do
  let stored ← storeTrace h s
  return branchState (cursorPrefix stored 2)

theorem node_execution (s : MachineState) (h : Height) (args : LoopArgs s 256)
    (pc : s.pc = bodyPC h)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x6+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (outputs : ∀ k : Fin 4, accessValid (s.getReg .x7+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (parentNodeSteps h+fuel) s coins =
      (do let out ← nodeTrace h s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (parentNodeCycles h) (calls h)) := by
  rw [show parentNodeSteps h+fuel =
    46+continuationInstructions (calls h-1)+(2+(fuel+1)) by unfold parentNodeSteps; omega,
    store_execution s h args pc inputs outputs]
  simp only [nodeTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro stored reached
  have here : stored.pc = cursorPC h := (store_pc s stored h pc reached).trans (cursor_pc_eq h).symm
  rw [cursor_execution stored h here,parent_branch_execution _ h (cursor_branch_pc stored h here)]
  simp [parentNodeCycles,Execution.charge,←Nat.add_assoc,
    show 53+continuationCycles (calls h-1)+2+1 = 56+continuationCycles (calls h-1) by omega]

theorem node_pc (s out : MachineState) (h : Height) (pc : s.pc = bodyPC h)
    (reached : out ∈ support (nodeTrace h s)) :
    out.pc = if s.getReg .x7-32 != s.getReg .x15 then bodyPC h else shiftPC h := by
  simp only [nodeTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨stored,last,rfl⟩ := reached
  have here : stored.pc = cursorPC h := (store_pc s stored h pc last).trans (cursor_pc_eq h).symm
  rw [parent_branch_pc _ h (cursor_branch_pc stored h here),cursor_target,
    cursor_register _ .x15 (by decide) (by decide),
    store_register s stored h last .x7 (by decide),store_register s stored h last .x15 (by decide)]

theorem node_query_bound (s : MachineState) (h : Height) : PublicQueryBound (nodeTrace h s) (calls h) := by
  have stored : PublicQueryBound (storeTrace h s) (calls h-1+1+0) :=
    public_query_bound_bind (hash_trace_bounded (calls h-1) (bodyPrefix s h 3)) (fun _ => by trivial)
  have bounded : PublicQueryBound (nodeTrace h s) (calls h-1+1+0+0) :=
    public_query_bound_bind (second := 0) stored (fun _ => by trivial)
  exact bounded.mono (by have := calls_positive h; omega)

end CommitGolfCandidate.Chained.Native
