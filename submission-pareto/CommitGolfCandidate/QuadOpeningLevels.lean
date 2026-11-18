import CommitGolfCandidate.QuadOpeningLevel

/-! The eleven levels of one penta record (`levelStart 0 … levelStart 11`). -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open QOpening (trapdoorBase proofBase nonceBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

def neighboursRun (j : Nat) (state : MachineState) : MachineState :=
  ((List.range j).flatMap neighbourCode).foldl execInstrBr state

theorem neighbours_run (init : MachineState) (positions : Positions) (o k : Nat) (hk : k < 11)
    (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(levelStart k+8)))
    (rest : state.getReg .x25 = BitVec.ofNat 64 (ordinalIndex positions o / 5^k % 5))
    (group : state.getReg .x30 =
      BitVec.ofNat 64 (trapdoorBase+pentaGroupBase k+40+368*(ordinalIndex positions o / 5^k / 5)))
    (five : state.getReg .x19 = BitVec.ofNat 64 5)
    (dest : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*levelWord o k))
    (inv : Inv init state (wordSource positions) (levelWord o k)) :
    ∀ j ≤ 4, let after := neighboursRun j state
      Runs state after (13*j) (16*j) ∧ after.pc = BitVec.ofNat 64 (4096+4*(levelStart k+8+13*j)) ∧
      after.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(levelWord o k+4*j)) ∧
      Inv init after (wordSource positions) (levelWord o k+4*j) ∧
      ∀ r, r ≠ .x7 → r ≠ .x21 → r ≠ .x31 → after.getReg r = state.getReg r := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨Runs.zero state, by simpa [neighboursRun] using pc, by simpa [neighboursRun] using dest,
      by simpa [neighboursRun] using inv, fun _ _ _ _ => rfl⟩
  | succ j ih =>
    intro le
    obtain ⟨run, pc', dest', inv', regs⟩ := ih (by omega)
    let middle := neighboursRun j state
    have block := neighbour_block init middle positions o k j hk (by omega) inside ordinal pc'
      ((regs .x25 (by decide) (by decide) (by decide)).trans rest)
      ((regs .x30 (by decide) (by decide) (by decide)).trans group)
      ((regs .x19 (by decide) (by decide) (by decide)).trans five) dest' inv'
    obtain ⟨run₂, pc₂, dest₂, inv₂, regs₂⟩ := block
    have shape : neighboursRun (j+1) state = (neighbourCode j).foldl execInstrBr middle := by
      simp only [neighboursRun, middle, List.range_succ, List.flatMap_append, List.foldl_append,
        List.flatMap_singleton]
    intro after
    rw [show after = neighboursRun (j+1) state from rfl, shape]
    refine ⟨(run.trans run₂).cast (by omega) (by omega), pc₂, dest₂, inv₂, ?_⟩
    intro r a b c
    exact (regs₂ r a b c).trans (regs r a b c)

theorem level_step (init state : MachineState) (positions : Positions) (o k : Nat) (hk : k < 11)
    (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH)
    (at_ : LevelAt init state positions o k) :
    let after := (levelCode k).foldl execInstrBr state
    Runs state after 61 79 ∧ LevelAt init after positions o (k+1) ∧
      ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → r ≠ .x24 → r ≠ .x25 → r ≠ .x30 →
        r ≠ .x31 → after.getReg r = state.getReg r := by
  intro after
  let i := ordinalIndex positions o
  let s₀ := (levelHead k).foldl execInstrBr state
  have headPure : (levelHead k).all pureOp = true := by simp [levelHead, pureOp]
  have run₀ := runs_pure _ _ state (head_code k hk) at_.pc headPure
  have small : i/5^k < 2^30 := by
    have := Nat.div_le_self i (5^k); have : i < 2^24 := inside; omega
  have post₀ := level_head_post state k (i/5^k) hk small at_.node at_.five at_.width at_.heap
  have pc₀ : s₀.pc = BitVec.ofNat 64 (4096+4*(levelStart k+8)) := by
    rw [pure_pc _ _ headPure, at_.pc, pc_offset]
    rfl
  have keep₀ (r : Reg) (a : r ≠ .x10) (b : r ≠ .x11) (c : r ≠ .x24) (d : r ≠ .x25) (e : r ≠ .x30) :
      s₀.getReg r = state.getReg r := post₀.2.2.2 r a b c d e
  have run := neighbours_run init positions o k hk inside ordinal s₀ pc₀ post₀.2.1 post₀.2.2.1
    ((keep₀ .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans at_.five)
    ((keep₀ .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans at_.dest)
    (at_.inv.of_mem (pure_mem _ _ headPure)) 4 le_rfl
  obtain ⟨run₁, pc₁, dest₁, inv₁, regs₁⟩ := run
  let s₁ := neighboursRun 4 s₀
  have tailPure : ([.ADDI .x6 .x24 0] : List Instr).all pureOp = true := rfl
  have run₂ := runs_pure [.ADDI .x6 .x24 0] (levelStart k+60) s₁ (level_tail_code k hk)
    (pc₁.trans (by congr 2)) tailPure
  have shape : after = [.ADDI .x6 .x24 0].foldl execInstrBr s₁ := by
    simp only [after, s₁, s₀, neighboursRun, levelCode, List.foldl_append]
  have keep (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x10) (d : r ≠ .x11) (e : r ≠ .x21)
      (f : r ≠ .x24) (g : r ≠ .x25) (h : r ≠ .x30) (l : r ≠ .x31) : after.getReg r = state.getReg r := by
    rw [shape]
    simp [execInstrBr, Ne.symm a]
    rw [regs₁ r b e l, keep₀ r c d f g h]
  have x24 : s₁.getReg .x24 = BitVec.ofNat 64 (i/5^k/5) :=
    (regs₁ .x24 (by decide) (by decide) (by decide)).trans post₀.1
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, keep⟩
  · rw [shape]
    exact (run₀.trans (run₁.trans run₂)).cast (by simp [levelHead]) (by simp [cost, levelHead, instructionCycles])
  · rw [shape, pure_pc _ _ tailPure, pc₁, pc_offset]
    unfold levelStart
    congr 2
  · rw [shape]
    simp [execInstrBr, x24, signExtend12]
    congr 1
    rw [pow_succ, Nat.div_div_eq_div_mul]
  · rw [shape]
    simp [execInstrBr]
    rw [dest₁]
    unfold levelWord
    congr 2
  · exact (keep .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans at_.heap
  · exact (keep .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans at_.five
  · exact (keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans at_.width
  · rw [shape]
    exact (inv₁.of_mem (pure_mem _ _ tailPure)).cast_count (by unfold levelWord; omega)

def levelsRun (count : Nat) (state : MachineState) : MachineState :=
  ((List.range count).flatMap levelCode).foldl execInstrBr state

theorem levels_run (init : MachineState) (positions : Positions) (o : Nat)
    (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH) (state : MachineState)
    (at_ : LevelAt init state positions o 0) :
    ∀ count ≤ 11, let after := levelsRun count state
      Runs state after (61*count) (79*count) ∧ LevelAt init after positions o count ∧
      ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → r ≠ .x24 → r ≠ .x25 → r ≠ .x30 →
        r ≠ .x31 → after.getReg r = state.getReg r := by
  intro count
  induction count with
  | zero => intro _; exact ⟨Runs.zero state, at_, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ count ih =>
    intro le
    obtain ⟨run, at', regs⟩ := ih (by omega)
    obtain ⟨run₂, at₂, regs₂⟩ := level_step init (levelsRun count state) positions o count (by omega)
      inside ordinal at'
    have shape : levelsRun (count+1) state = (levelCode count).foldl execInstrBr (levelsRun count state) := by
      simp only [levelsRun, List.range_succ, List.flatMap_append, List.foldl_append, List.flatMap_singleton]
    intro after
    rw [show after = levelsRun (count+1) state from rfl, shape]
    refine ⟨(run.trans run₂).cast (by omega) (by omega), at₂, ?_⟩
    intro r a b c d e f g h l
    exact (regs₂ r a b c d e f g h l).trans (regs r a b c d e f g h l)

end TwoPermutationPrototype.QuadOpening
