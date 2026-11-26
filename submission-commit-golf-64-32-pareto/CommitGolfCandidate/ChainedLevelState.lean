import CommitGolfCandidate.ChainedNodeFrame

/-! The descending cursor span and predictable last-node test for one parent level. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def cursorAt (base : Word) (stride index : Nat) : Word := base-BitVec.ofNat 64 (stride*index)

theorem cursor_at_zero (base : Word) (stride : Nat) : cursorAt base stride 0 = base := by
  simp [cursorAt]

theorem cursor_at_next (base : Word) (stride index : Nat) :
    cursorAt (base-BitVec.ofNat 64 stride) stride index = cursorAt base stride (index+1) := by
  have arithmetic : stride+stride*index = stride*(index+1) := by
    rw [Nat.mul_succ]
    exact Nat.add_comm _ _
  unfold cursorAt
  rw [BitVec.sub_sub,←BitVec.ofNat_add,arithmetic]

theorem boundary_after (s : MachineState) (remaining : Nat)
    (boundary : s.getReg .x7 = s.getReg .x15+BitVec.ofNat 64 (32*(remaining+1))) :
    s.getReg .x7-32 = s.getReg .x15+BitVec.ofNat 64 (32*remaining) := by
  rw [boundary,show 32*(remaining+1) = 32*remaining+32 by omega,BitVec.ofNat_add,
    show BitVec.ofNat 64 32 = (32 : Word) from rfl,←BitVec.add_assoc,BitVec.add_sub_cancel]

private theorem count_offset_nonzero (remaining : Nat) (small : remaining ≤ 2^23)
    (nonzero : remaining ≠ 0) : BitVec.ofNat 64 (32*remaining) ≠ 0 := by
  intro equal
  have numeric := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat,show (0 : Word).toNat = 0 from rfl,
    Nat.mod_eq_of_lt (show 32*remaining < 2^64 by omega)] at numeric
  omega

theorem node_loop_pc (s out : MachineState) (h : Height) (remaining : Nat)
    (small : remaining ≤ 2^23) (pc : s.pc = bodyPC h)
    (boundary : s.getReg .x7 = s.getReg .x15+BitVec.ofNat 64 (32*(remaining+1)))
    (reached : out ∈ support (nodeTrace h s)) :
    out.pc = if remaining = 0 then shiftPC h else bodyPC h := by
  rw [node_pc s out h pc reached,boundary_after s remaining boundary]
  by_cases empty : remaining = 0
  · simp [empty]
  · have different : s.getReg .x15+BitVec.ofNat 64 (32*remaining) ≠ s.getReg .x15 := by
      intro equal
      apply count_offset_nonzero remaining small empty
      exact (BitVec.add_right_inj _).mp (equal.trans (BitVec.add_zero _).symm)
    simp only [bne_iff_ne,ite_eq_left different,ite_eq_right empty]

structure LevelReady (s : MachineState) (h : Height) (remaining : Nat) : Prop where
  args : LoopArgs s 256
  pc : s.pc = if remaining = 0 then shiftPC h else bodyPC h
  small : remaining ≤ 2^23
  boundary : s.getReg .x7 = s.getReg .x15+BitVec.ofNat 64 (32*remaining)
  inputs : ∀ i, i < remaining → ∀ k : Fin 8,
    accessValid (cursorAt (s.getReg .x6) 64 i+BitVec.ofNat 64 (8*k.val)) 8 = true
  outputs : ∀ i, i < remaining → ∀ k : Fin 4,
    accessValid (cursorAt (s.getReg .x7) 32 i+BitVec.ofNat 64 (8*k.val)) 8 = true

theorem LevelReady.node {s : MachineState} {h : Height} {remaining : Nat}
    (ready : LevelReady s h (remaining+1)) (out : MachineState)
    (reached : out ∈ support (nodeTrace h s)) : LevelReady out h remaining := by
  have pc : s.pc = bodyPC h := by simpa only [Nat.add_one_ne_zero,ite_false] using ready.pc
  refine ⟨ready.args.node h reached,node_loop_pc s out h remaining (by have := ready.small; omega)
    pc ready.boundary reached,by have := ready.small; omega,?_,?_,?_⟩
  · rw [node_target s out h reached,node_register s out h reached .x15 (by decide)]
    exact boundary_after s remaining ready.boundary
  · intro i inside k
    rw [node_source s out h reached]
    have shift := cursor_at_next (s.getReg .x6) 64 i
    rw [show BitVec.ofNat 64 64 = (64 : Word) from rfl] at shift
    rw [shift]
    exact ready.inputs (i+1) (by omega) k
  · intro i inside k
    rw [node_target s out h reached]
    have shift := cursor_at_next (s.getReg .x7) 32 i
    rw [show BitVec.ofNat 64 32 = (32 : Word) from rfl] at shift
    rw [shift]
    exact ready.outputs (i+1) (by omega) k

end CommitGolfCandidate.Chained.Native
