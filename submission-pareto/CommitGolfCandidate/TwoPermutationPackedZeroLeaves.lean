import CommitGolfCandidate.TwoPermutationPackedSetup
import CommitGolfCandidate.TwoPermutationLeafMask

/-! After the leaf phase, commit keeps only the low 241 bits of every leaf digest.
Word 45128 jumps to a pass appended at word 233380:
`sub t4,s5,s3; li t5,-1; srli t5,t5,15` sets the cursor to the first leaf and the
mask to `2^49-1`; the loop at word 233383 masks the top doubleword of 32 leaves per
iteration (`ld t6,32u+24(t4); and t6,t6,t5; sd t6,32u+24(t4)`), then
`addi t4,t4,1024; bne t4,s5`. The exit runs `addi a0,s5,-64` and jumps back to
word 45129, where the remaining four parent-setup instructions run as before. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def zeroJump : Instr := .JAL .x0 753008
def zeroStart : Instr := .SUB .x29 .x21 .x19
def maskOnes : Instr := .ADDI .x30 .x0 4095
def maskShift : Instr := .SRLI .x30 .x30 15
def maskLoad (u : Nat) : Instr := .LD .x31 .x29 (BitVec.ofNat 12 (32*u+24))
def maskAnd : Instr := .AND .x31 .x31 .x30
def maskStore (u : Nat) : Instr := .SD .x29 .x31 (BitVec.ofNat 12 (32*u+24))
def zeroAdvance : Instr := .ADDI .x29 .x29 1024
def zeroBranch : Instr := .BNE .x29 .x21 7804
def zeroSource : Instr := .ADDI .x10 .x21 4032
def zeroBack : Instr := .JAL .x0 1343740

private theorem zero_decode_jump : Manifest.decodeBase (packed_wideCodeWord 45128) = some zeroJump := by decide +kernel
private theorem zero_decode_start : Manifest.decodeBase (packed_wideCodeWord 233380) = some zeroStart := by decide +kernel
private theorem zero_decode_ones : Manifest.decodeBase (packed_wideCodeWord 233381) = some maskOnes := by decide +kernel
private theorem zero_decode_shift : Manifest.decodeBase (packed_wideCodeWord 233382) = some maskShift := by decide +kernel
private theorem zero_decode_load : ∀ u : Fin 32,
    Manifest.decodeBase (packed_wideCodeWord (233383+3*u.val)) = some (maskLoad u.val) := by decide +kernel
private theorem zero_decode_and : ∀ u : Fin 32,
    Manifest.decodeBase (packed_wideCodeWord (233383+3*u.val+1)) = some maskAnd := by decide +kernel
private theorem zero_decode_store : ∀ u : Fin 32,
    Manifest.decodeBase (packed_wideCodeWord (233383+3*u.val+2)) = some (maskStore u.val) := by decide +kernel
private theorem zero_decode_advance : Manifest.decodeBase (packed_wideCodeWord 233479) = some zeroAdvance := by decide +kernel
private theorem zero_decode_branch : Manifest.decodeBase (packed_wideCodeWord 233480) = some zeroBranch := by decide +kernel
private theorem zero_decode_source : Manifest.decodeBase (packed_wideCodeWord 233481) = some zeroSource := by decide +kernel
private theorem zero_decode_back : Manifest.decodeBase (packed_wideCodeWord 233482) = some zeroBack := by decide +kernel

theorem zero_fetch (index : Nat) (instruction : Instr)
    (decoded : Manifest.decodeBase (packed_wideCodeWord index) = some instruction)
    (inCode : index < 233483) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*index)) :
    fetch packedWideCommitImage state = some (.base instruction) :=
  packed_wide_fetch_decoded state index inCode pc instruction decoded

/-- Word address of the top doubleword of leaf `i`. -/
def zeroAddress (i : Nat) : Word := wordAddress (leafDest i + 3)

open Classical in
/-- Memory with the top doubleword of the first `count` leaf digests masked to 49 bits. -/
noncomputable def maskedMemory (m : Word → Word) (count : Nat) : Word → Word :=
  fun a => if ∃ i < count, a = zeroAddress i then m a &&& leafMask else m a

theorem masked_hit (m : Word → Word) (count : Nat) (a : Word) (h : ∃ i < count, a = zeroAddress i) :
    maskedMemory m count a = m a &&& leafMask := by
  unfold maskedMemory; exact if_pos h

theorem masked_miss (m : Word → Word) (count : Nat) (a : Word) (h : ¬ ∃ i < count, a = zeroAddress i) :
    maskedMemory m count a = m a := by
  unfold maskedMemory; exact if_neg h

theorem zero_address_injective {i j : Nat} (hi : i < 2^24) (hj : j < 2^24)
    (same : zeroAddress i = zeroAddress j) : i = j := by
  have n := congrArg BitVec.toNat same
  simp only [zeroAddress, wordAddress, leafDest, BitVec.toNat_ofNat] at n
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at n
  omega

theorem masked_memory_zero (m : Word → Word) : maskedMemory m 0 = m := by
  funext a
  simp [maskedMemory]

theorem set_pc_mem (t : MachineState) (v : Word) : (t.setPC v).mem = t.mem := rfl

private theorem get_reg_set_mem (t : MachineState) (a v : Word) (r : Reg) :
    (t.setMem a v).getReg r = t.getReg r := by cases r <;> rfl

private theorem offset_word : ∀ u : Fin 32,
    signExtend12 (BitVec.ofNat 12 (32*u.val+24)) = BitVec.ofNat 64 (32*u.val+24) := by decide

/-- Inside an iteration whose cursor is leaf `j`, after `u` masked leaves. -/
structure InnerAt (s0 : MachineState) (j u : Nat) (st : MachineState) : Prop where
  cursor : st.getReg .x29 = wordAddress (leafDest j)
  mask : st.getReg .x30 = leafMask
  regs : ∀ r, r ≠ .x29 → r ≠ .x30 → r ≠ .x31 → st.getReg r = s0.getReg r
  mem : st.mem = maskedMemory s0.mem (j+u)

def maskStep (u : Nat) (st : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr st (maskLoad u)) maskAnd) (maskStore u)

private theorem mask_address (st : MachineState) (j u : Nat) (hu : u < 32)
    (cursor : st.getReg .x29 = wordAddress (leafDest j)) :
    st.getReg .x29 + signExtend12 (BitVec.ofNat 12 (32*u+24)) = zeroAddress (j+u) := by
  rw [cursor, show signExtend12 (BitVec.ofNat 12 (32*u+24)) = BitVec.ofNat 64 (32*u+24) from offset_word ⟨u, hu⟩]
  unfold zeroAddress wordAddress leafDest
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem mask_step_at (s0 st : MachineState) (j u : Nat) (hu : u < 32) (bound : j+u < 2^24)
    (at_ : InnerAt s0 j u st) : InnerAt s0 j (u+1) (maskStep u st) := by
  have addr := mask_address st j u hu at_.cursor
  let loaded := execInstrBr st (maskLoad u)
  let anded := execInstrBr loaded maskAnd
  have loaded29 : loaded.getReg .x29 = st.getReg .x29 := by
    simp only [loaded, maskLoad, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x31 ≠ Reg.x29 by decide)]
  have loaded30 : loaded.getReg .x30 = leafMask := by
    simp only [loaded, maskLoad, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x31 ≠ Reg.x30 by decide)]
    exact at_.mask
  have loaded31 : loaded.getReg .x31 = st.mem (zeroAddress (j+u)) := by
    simp only [loaded, maskLoad, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (show Reg.x31 ≠ Reg.x0 by decide), MachineState.getMem]
    rw [addr]
  have anded29 : anded.getReg .x29 = st.getReg .x29 := by
    simp only [anded, maskAnd, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x31 ≠ Reg.x29 by decide)]
    exact loaded29
  have anded31 : anded.getReg .x31 = st.mem (zeroAddress (j+u)) &&& leafMask := by
    simp only [anded, maskAnd, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (show Reg.x31 ≠ Reg.x0 by decide)]
    rw [loaded31, loaded30]
  have andedMem : anded.mem = st.mem := rfl
  have keep (r : Reg) (h31 : r ≠ .x31) : (maskStep u st).getReg r = st.getReg r := by
    simp only [maskStep, maskStore, maskAnd, maskLoad, execInstrBr, MachineState.getReg_setPC,
      get_reg_set_mem, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h31)]
  refine ⟨(keep _ (by decide)).trans at_.cursor, (keep _ (by decide)).trans at_.mask,
    fun r a b c => (keep r c).trans (at_.regs r a b c), ?_⟩
  have stored : (maskStep u st).mem =
      (anded.setMem (anded.getReg .x29 + signExtend12 (BitVec.ofNat 12 (32*u+24))) (anded.getReg .x31)).mem := rfl
  rw [stored, anded29, addr, anded31, at_.mem]
  funext a
  simp only [MachineState.setMem, andedMem, at_.mem]
  have old : maskedMemory s0.mem (j+u) (zeroAddress (j+u)) = s0.mem (zeroAddress (j+u)) := by
    apply masked_miss
    rintro ⟨i, lt, same⟩
    have := zero_address_injective (by omega) (by omega) same
    omega
  by_cases hit : a = zeroAddress (j+u)
  · subst hit
    simp only [beq_self_eq_true, ite_true]
    rw [old, masked_hit _ _ _ ⟨j+u, by omega, rfl⟩]
  · have neq : (a == zeroAddress (j+u)) = false := by simpa using hit
    have iff : (∃ i < j+(u+1), a = zeroAddress i) ↔ (∃ i < j+u, a = zeroAddress i) := by
      constructor
      · rintro ⟨i, lt, same⟩
        refine ⟨i, ?_, same⟩
        by_contra ge
        exact hit (by rw [same, show i = j+u by omega])
      · rintro ⟨i, lt, same⟩
        exact ⟨i, by omega, same⟩
    simp only [neq, Bool.false_eq_true, ite_false, maskedMemory, iff]

theorem mask_step_pc (st : MachineState) (u : Nat) : (maskStep u st).pc = st.pc + 12 := by
  simp only [maskStep, maskStore, maskAnd, maskLoad, execInstrBr, MachineState.setPC, MachineState.setMem,
    MachineState.setReg]
  rw [BitVec.add_assoc, BitVec.add_assoc]
  rfl

def innerPC (u : Nat) : Word := BitVec.ofNat 64 (4096+4*(233383+3*u))

private theorem pc_word (base off : Nat) :
    BitVec.ofNat 64 (4096+4*base) + BitVec.ofNat 64 (4*off) = BitVec.ofNat 64 (4096+4*(base+off)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

theorem mask_step_steps (s0 st : MachineState) (j u : Nat) (hu : u < 32) (bound : j+u < 2^24)
    (at_ : InnerAt s0 j u st) (pc : st.pc = innerPC u) (fuel : Nat) :
    execute packedWideCommitImage (3+fuel) st true =
      (do let result ← execute packedWideCommitImage fuel (maskStep u st) true
          return result.charge 3 0) := by
  have addr := mask_address st j u hu at_.cursor
  let s1 := execInstrBr st (maskLoad u)
  let s2 := execInstrBr s1 maskAnd
  let states : Nat → MachineState := fun i =>
    if i = 0 then st else if i = 1 then s1 else if i = 2 then s2 else maskStep u st
  have pc1 : s1.pc = BitVec.ofNat 64 (4096+4*(233383+3*u+1)) := by
    simp only [s1, maskLoad, execInstrBr, MachineState.setPC, MachineState.setReg, pc, innerPC]
    rw [show (4 : Word) = BitVec.ofNat 64 (4*1) from rfl, pc_word]
  have pc2 : s2.pc = BitVec.ofNat 64 (4096+4*(233383+3*u+2)) := by
    simp only [s2, maskAnd, execInstrBr, MachineState.setPC, MachineState.setReg]
    rw [pc1, show (4 : Word) = BitVec.ofNat 64 (4*1) from rfl, pc_word]
  have s1x29 : s1.getReg .x29 = st.getReg .x29 := by
    simp only [s1, maskLoad, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x31 ≠ Reg.x29 by decide)]
  have s2x29 : s2.getReg .x29 = st.getReg .x29 := by
    simp only [s2, maskAnd, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x31 ≠ Reg.x29 by decide)]
    exact s1x29
  have valid (t : MachineState) (same : t.getReg .x29 = st.getReg .x29) :
      accessValid (t.getReg .x29 + signExtend12 (BitVec.ofNat 12 (32*u+24))) 8 = true := by
    rw [same, addr]
    simp only [accessValid, rangeValid, zeroAddress, wordAddress, leafDest, BitVec.toNat_ofNat,
      Bool.and_eq_true, decide_eq_true_eq, MEMORY_BYTES]
    constructor <;> omega
  have uLt : u < 32 := hu
  have fu : 233383+3*u < 233483 := by omega
  exact CommitGolfCandidate.execute_unit_steps packedWideCommitImage 3 fuel states true (by
    intro i inside
    interval_cases i
    · refine ⟨.base (maskLoad u), zero_fetch _ _ (zero_decode_load ⟨u, hu⟩) (by omega) _ pc, ?_, rfl⟩
      show ordinaryStep st (.base (maskLoad u)) = some s1
      have v := valid st rfl
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, maskLoad, v, ite_true]
      rfl
    · refine ⟨.base maskAnd, zero_fetch _ _ (zero_decode_and ⟨u, hu⟩) (by omega) _ pc1, ?_, rfl⟩
      show ordinaryStep s1 (.base maskAnd) = some s2
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, maskAnd, ite_true]
      rfl
    · refine ⟨.base (maskStore u), zero_fetch _ _ (zero_decode_store ⟨u, hu⟩) (by omega) _ pc2, ?_, rfl⟩
      show ordinaryStep s2 (.base (maskStore u)) = some (maskStep u st)
      have v := valid s2 s2x29
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, maskStore, v, ite_true]
      rfl)

/-- Run sub-blocks `u, u+1, …, u+k-1` of one iteration. -/
def maskRun : Nat → Nat → MachineState → MachineState
  | _, 0, s => s
  | u, k+1, s => maskRun (u+1) k (maskStep u s)

theorem mask_run_post (s0 : MachineState) (j : Nat) :
    ∀ (k u : Nat) (st : MachineState), InnerAt s0 j u st → st.pc = innerPC u → u+k ≤ 32 → j+u+k ≤ 2^24 →
      InnerAt s0 j (u+k) (maskRun u k st) ∧ (maskRun u k st).pc = innerPC (u+k) := by
  intro k
  induction k with
  | zero => intro u st at_ pc _ _; exact ⟨at_, pc⟩
  | succ k ih =>
    intro u st at_ pc room bound
    have next := mask_step_at s0 st j u (by omega) (by omega) at_
    have npc : (maskStep u st).pc = innerPC (u+1) := by
      rw [mask_step_pc, pc]; unfold innerPC; rw [show (12 : Word) = BitVec.ofNat 64 (4*3) from rfl, pc_word]
      congr 2
    have r := ih (u+1) _ next npc (by omega) (by omega)
    simp only [maskRun]
    rw [show u+(k+1) = u+1+k by omega]
    exact r

theorem mask_run_execute (s0 : MachineState) (j : Nat) :
    ∀ (k u : Nat) (st : MachineState), InnerAt s0 j u st → st.pc = innerPC u → u+k ≤ 32 → j+u+k ≤ 2^24 →
      ∀ fuel, execute packedWideCommitImage (3*k+fuel) st true =
        (do let result ← execute packedWideCommitImage fuel (maskRun u k st) true
            return result.charge (3*k) 0) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ fuel; simp [maskRun, Execution.charge]
  | succ k ih =>
    intro u st at_ pc room bound fuel
    rw [show 3*(k+1)+fuel = 3+(3*k+fuel) by omega, mask_step_steps s0 st j u (by omega) (by omega) at_ pc]
    have next := mask_step_at s0 st j u (by omega) (by omega) at_
    have npc : (maskStep u st).pc = innerPC (u+1) := by
      rw [mask_step_pc, pc]; unfold innerPC; rw [show (12 : Word) = BitVec.ofNat 64 (4*3) from rfl, pc_word]
      congr 2
    rw [ih (u+1) _ next npc (by omega) (by omega) fuel]
    simp only [maskRun, bind_assoc, pure_bind, Execution.charge]
    simp only [show ∀ c, 3 + (3*k+c) = 3*(k+1)+c from fun c => by omega, Nat.zero_add]

/-- One loop iteration: 32 masked leaves, advance, branch. -/
def zeroBody (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (maskRun 0 32 s) zeroAdvance) zeroBranch

def zeroLoop : Nat → MachineState → MachineState
  | 0, s => s
  | k+1, s => zeroLoop k (zeroBody s)

def zeroLoopPC : Word := innerPC 0
def zeroExitPC : Word := BitVec.ofNat 64 (4096+4*233481)

theorem zero_branch_reg (t : MachineState) (r : Reg) : (execInstrBr t zeroBranch).getReg r = t.getReg r := by
  simp only [zeroBranch, execInstrBr]; split <;> exact MachineState.getReg_setPC

theorem zero_advance_reg (t : MachineState) (r : Reg) (ne : r ≠ .x29) :
    (execInstrBr t zeroAdvance).getReg r = t.getReg r := by
  simp only [zeroAdvance, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]

theorem zero_advance_cursor (t : MachineState) :
    (execInstrBr t zeroAdvance).getReg .x29 = t.getReg .x29 + signExtend12 1024 := by
  simp only [zeroAdvance, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (r := .x29) (by decide)]

theorem zero_body_at (s0 st : MachineState) (j : Nat) (bound : j+32 ≤ 2^24) (at_ : InnerAt s0 j 0 st)
    (pc : st.pc = zeroLoopPC) :
    InnerAt s0 (j+32) 0 (zeroBody st) ∧ (maskRun 0 32 st).pc = innerPC 32 := by
  obtain ⟨inner, ipc⟩ := mask_run_post s0 j 32 0 st at_ pc (by omega) (by omega)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ipc⟩
  · unfold zeroBody
    rw [zero_branch_reg, zero_advance_cursor, inner.cursor]
    unfold wordAddress leafDest
    rw [show signExtend12 (1024 : BitVec 12) = BitVec.ofNat 64 1024 by decide, ← BitVec.ofNat_add]
    congr 1
  · unfold zeroBody
    rw [zero_branch_reg, zero_advance_reg _ _ (by decide)]
    exact inner.mask
  · intro r a b c
    unfold zeroBody
    rw [zero_branch_reg, zero_advance_reg _ _ a]
    exact inner.regs r a b c
  · have advanceMem : (execInstrBr (maskRun 0 32 st) zeroAdvance).mem = (maskRun 0 32 st).mem := by
      simp only [zeroAdvance, execInstrBr, MachineState.setReg, MachineState.setPC]
    have branchMem (t : MachineState) : (execInstrBr t zeroBranch).mem = t.mem := by
      simp only [zeroBranch, execInstrBr]; split <;> exact set_pc_mem _ _
    unfold zeroBody
    rw [branchMem, advanceMem, inner.mem]

theorem zero_body_pc (s0 st : MachineState) (j : Nat) (bound : j+32 ≤ 2^24) (at_ : InnerAt s0 j 0 st)
    (stop : s0.getReg .x21 = wordAddress (leafDest (2^24))) (pc : st.pc = zeroLoopPC) :
    (zeroBody st).pc = if j+32 = 2^24 then zeroExitPC else zeroLoopPC := by
  obtain ⟨next, ipc⟩ := zero_body_at s0 st j bound at_ pc
  let t := execInstrBr (maskRun 0 32 st) zeroAdvance
  have tpc : t.pc = BitVec.ofNat 64 (4096+4*233480) := by
    simp only [t, zeroAdvance, execInstrBr, MachineState.setPC, MachineState.setReg]
    rw [ipc]; rfl
  have cur : t.getReg .x29 = wordAddress (leafDest (j+32)) := by
    have := next.cursor
    unfold zeroBody at this
    rwa [zero_branch_reg] at this
  have end_ : t.getReg .x21 = wordAddress (leafDest (2^24)) := by
    have := next.regs .x21 (by decide) (by decide) (by decide)
    unfold zeroBody at this
    rw [zero_branch_reg] at this
    exact this.trans stop
  change (execInstrBr t zeroBranch).pc = _
  simp only [zeroBranch, execInstrBr, cur, end_]
  by_cases last : j+32 = 2^24
  · have same : (wordAddress (leafDest (j+32)) != wordAddress (leafDest (2^24))) = false := by
      rw [last]; simp
    rw [if_pos last]
    simp only [same, Bool.false_eq_true, if_false, MachineState.setPC, tpc]
    rfl
  · have differ : wordAddress (leafDest (j+32)) ≠ wordAddress (leafDest (2^24)) := by
      intro same
      have n := congrArg BitVec.toNat same
      simp only [wordAddress, leafDest, BitVec.toNat_ofNat] at n
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at n
      omega
    have taken : (wordAddress (leafDest (j+32)) != wordAddress (leafDest (2^24))) = true := by
      simpa using differ
    rw [if_neg last]
    simp only [taken, if_true, MachineState.setPC, tpc]
    rfl

attribute [local irreducible] execute packedWideCommitImage in
theorem zero_body_steps (s0 st : MachineState) (j : Nat) (bound : j+32 ≤ 2^24) (at_ : InnerAt s0 j 0 st)
    (pc : st.pc = zeroLoopPC) (fuel : Nat) :
    execute packedWideCommitImage (98+fuel) st true =
      (do let result ← execute packedWideCommitImage fuel (zeroBody st) true
          return result.charge 98 0) := by
  obtain ⟨_, ipc⟩ := zero_body_at s0 st j bound at_ pc
  have run := mask_run_execute s0 j 32 0 st at_ pc (by omega) (by omega) (2+fuel)
  have apc : (execInstrBr (maskRun 0 32 st) zeroAdvance).pc = BitVec.ofNat 64 (4096+4*233480) := by
    simp only [zeroAdvance, execInstrBr, MachineState.setPC, MachineState.setReg]
    rw [ipc]; rfl
  have fA := zero_fetch 233479 _ zero_decode_advance (by decide) (maskRun 0 32 st) ipc
  have fB := zero_fetch 233480 _ zero_decode_branch (by decide) _ apc
  have stepA : ordinaryStep (maskRun 0 32 st) (.base zeroAdvance) =
      some (execInstrBr (maskRun 0 32 st) zeroAdvance) := by unfold zeroAdvance; rfl
  have stepB : ordinaryStep (execInstrBr (maskRun 0 32 st) zeroAdvance) (.base zeroBranch) = some (zeroBody st) := by
    unfold zeroBody zeroBranch; rfl
  rw [show 98+fuel = 3*32+(2+fuel) by omega, run]
  rw [show 2+fuel = (fuel+1)+1 by omega, CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fA stepA,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fB stepB]
  simp only [bind_assoc, pure_bind, Execution.charge, instructionCycles, zeroAdvance, zeroBranch, Nat.zero_add,
    show ∀ c, 3*32+(1+(1+c)) = 98+c from fun c => by omega]

theorem zero_loop_execute (s0 : MachineState) (stop : s0.getReg .x21 = wordAddress (leafDest (2^24))) :
    ∀ (k j : Nat) (st : MachineState), InnerAt s0 j 0 st → (0 < k → st.pc = zeroLoopPC) → j + 32*k = 2^24 →
      ∀ fuel, execute packedWideCommitImage (98*k+fuel) st true =
        (do let result ← execute packedWideCommitImage fuel (zeroLoop k st) true
            return result.charge (98*k) 0) := by
  intro k
  induction k with
  | zero =>
    intro j st _ _ _ fuel
    simp [zeroLoop, Execution.charge]
  | succ k ih =>
    intro j st at_ pc sum fuel
    have bound : j+32 ≤ 2^24 := by omega
    have here := pc (by omega)
    rw [show 98*(k+1)+fuel = 98+(98*k+fuel) by omega, zero_body_steps s0 st j bound at_ here]
    have next := (zero_body_at s0 st j bound at_ here).1
    have nextPC : 0 < k → (zeroBody st).pc = zeroLoopPC := by
      intro positive
      rw [zero_body_pc s0 st j bound at_ stop here, if_neg (by omega)]
    rw [ih (j+32) (zeroBody st) next nextPC (by omega) fuel]
    simp only [zeroLoop, bind_assoc, pure_bind, Execution.charge]
    simp only [show ∀ c, 98 + (98*k+c) = 98*(k+1)+c from fun c => by omega, Nat.zero_add]

theorem zero_loop_post (s0 : MachineState) (stop : s0.getReg .x21 = wordAddress (leafDest (2^24))) :
    ∀ (k j : Nat) (st : MachineState), InnerAt s0 j 0 st → (0 < k → st.pc = zeroLoopPC) → j + 32*k = 2^24 → 0 < k →
      InnerAt s0 (2^24) 0 (zeroLoop k st) ∧ (zeroLoop k st).pc = zeroExitPC := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ impossible; omega
  | succ k ih =>
    intro j st at_ pc sum _
    have bound : j+32 ≤ 2^24 := by omega
    have here := pc (by omega)
    have next := (zero_body_at s0 st j bound at_ here).1
    have nextPC := zero_body_pc s0 st j bound at_ stop here
    by_cases last : k = 0
    · subst last
      have full : j + 32 = 2^24 := by omega
      rw [full] at next
      rw [if_pos full] at nextPC
      exact ⟨next, nextPC⟩
    · exact ih (j+32) (zeroBody st) next (fun _ => by rw [nextPC, if_neg (by omega)]) (by omega) (by omega)

theorem jal_mem (t : MachineState) (off : BitVec 21) : (execInstrBr t (.JAL .x0 off)).mem = t.mem := rfl
theorem jal_reg (t : MachineState) (off : BitVec 21) (r : Reg) :
    (execInstrBr t (.JAL .x0 off)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC]; rfl
theorem jal_pc (t : MachineState) (off : BitVec 21) :
    (execInstrBr t (.JAL .x0 off)).pc = t.pc + signExtend21 off := rfl
theorem sub_mem (t : MachineState) (rd a b : Reg) : (execInstrBr t (.SUB rd a b)).mem = t.mem := by
  cases rd <;> rfl
theorem addi_mem (t : MachineState) (rd a : Reg) (i : BitVec 12) : (execInstrBr t (.ADDI rd a i)).mem = t.mem := by
  cases rd <;> rfl
theorem srli_mem (t : MachineState) (rd a : Reg) (i : BitVec 6) : (execInstrBr t (.SRLI rd a i)).mem = t.mem := by
  cases rd <;> rfl
theorem sub_pc (t : MachineState) (rd a b : Reg) : (execInstrBr t (.SUB rd a b)).pc = t.pc + 4 := by
  cases rd <;> rfl
theorem addi_pc (t : MachineState) (rd a : Reg) (i : BitVec 12) : (execInstrBr t (.ADDI rd a i)).pc = t.pc + 4 := by
  cases rd <;> rfl
theorem srli_pc (t : MachineState) (rd a : Reg) (i : BitVec 6) : (execInstrBr t (.SRLI rd a i)).pc = t.pc + 4 := by
  cases rd <;> rfl
theorem sub_reg (t : MachineState) (rd a b r : Reg) (ne : rd ≠ r) :
    (execInstrBr t (.SUB rd a b)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
theorem addi_reg (t : MachineState) (rd a r : Reg) (i : BitVec 12) (ne : rd ≠ r) :
    (execInstrBr t (.ADDI rd a i)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
theorem srli_reg (t : MachineState) (rd a r : Reg) (i : BitVec 6) (ne : rd ≠ r) :
    (execInstrBr t (.SRLI rd a i)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
theorem sub_dest (t : MachineState) (rd a b : Reg) (ne : rd ≠ .x0) :
    (execInstrBr t (.SUB rd a b)).getReg rd = t.getReg a - t.getReg b := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq ne]
theorem addi_dest (t : MachineState) (rd a : Reg) (i : BitVec 12) (ne : rd ≠ .x0) :
    (execInstrBr t (.ADDI rd a i)).getReg rd = t.getReg a + signExtend12 i := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq ne]
theorem srli_dest (t : MachineState) (rd a : Reg) (i : BitVec 6) (ne : rd ≠ .x0) :
    (execInstrBr t (.SRLI rd a i)).getReg rd = t.getReg a >>> i.toNat := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq ne]

def zeroLoopEntry (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr s zeroJump) zeroStart) maskOnes) maskShift
def zeroTail (t : MachineState) : MachineState := (parentSetupOps.drop 1).foldl execInstrBr t
def zeroLoopExit (s : MachineState) : MachineState := zeroLoop (2^19) (zeroLoopEntry s)
def zeroA (s : MachineState) : MachineState := execInstrBr (zeroLoopExit s) zeroSource
def zeroB (s : MachineState) : MachineState := execInstrBr (zeroA s) zeroBack
def zeroTailAt (s : MachineState) (i : Nat) : MachineState := ((parentSetupOps.drop 1).take i).foldl execInstrBr (zeroB s)
/-- The state after the truncation pass and the rest of the parent setup. -/
def zeroEntry (s : MachineState) : MachineState := zeroTail (zeroB s)

/-- Jump, three setup instructions, `2^19` iterations of 98, exit pair, four setup instructions. -/
def zeroEntryCost : Nat := 51380234

attribute [irreducible] zeroLoop zeroLoopExit

theorem zero_tail_mem (t : MachineState) : (zeroTail t).mem = t.mem := by
  simp only [zeroTail, parentSetupOps, List.drop, List.foldl, sub_mem, addi_mem]

section
variable (s : MachineState) (atLeaves : s.pc = 184608)
  (stride : s.getReg .x19 = 536870912) (stop : s.getReg .x21 = wordAddress (leafDest (2^24)))
include atLeaves stride stop

theorem zero_loop_entry_at :
    InnerAt (zeroLoopEntry s) 0 0 (zeroLoopEntry s) ∧ (zeroLoopEntry s).pc = zeroLoopPC := by
  refine ⟨⟨?_, ?_, fun _ _ _ _ => rfl, (masked_memory_zero _).symm⟩, ?_⟩
  · unfold zeroLoopEntry maskShift maskOnes zeroStart zeroJump
    rw [srli_reg _ _ _ _ _ (by decide), addi_reg _ _ _ _ _ (by decide), sub_dest _ _ _ _ (by decide),
      jal_reg, jal_reg, stop, stride]
    unfold wordAddress leafDest
    rw [show (536870912 : Word) = BitVec.ofNat 64 536870912 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    congr 1
  · unfold zeroLoopEntry maskShift maskOnes
    rw [srli_dest _ _ _ _ (by decide), addi_dest _ _ _ _ (by decide)]
    rw [show (execInstrBr (execInstrBr s zeroJump) zeroStart).getReg .x0 = 0#64 from rfl]
    decide
  · unfold zeroLoopEntry maskShift maskOnes zeroStart zeroJump
    rw [srli_pc, addi_pc, sub_pc, jal_pc, atLeaves]; rfl

theorem zero_loop_exit_post :
    InnerAt (zeroLoopEntry s) (2^24) 0 (zeroLoopExit s) ∧ (zeroLoopExit s).pc = zeroExitPC := by
  have entry := zero_loop_entry_at s atLeaves stride stop
  have stop' : (zeroLoopEntry s).getReg .x21 = wordAddress (leafDest (2^24)) := by
    unfold zeroLoopEntry maskShift maskOnes zeroStart zeroJump
    rw [srli_reg _ _ _ _ _ (by decide), addi_reg _ _ _ _ _ (by decide), sub_reg _ _ _ _ _ (by decide), jal_reg, stop]
  unfold zeroLoopExit
  exact zero_loop_post _ stop' (2^19) 0 _ entry.1 (fun _ => entry.2) (by omega) (by decide)

theorem zero_entry_mem : (zeroEntry s).mem = maskedMemory s.mem (2^24) := by
  have post := zero_loop_exit_post s atLeaves stride stop
  unfold zeroEntry zeroB zeroA zeroBack zeroSource
  rw [zero_tail_mem, jal_mem, addi_mem, post.1.mem, Nat.add_zero]
  unfold zeroLoopEntry maskShift maskOnes zeroStart zeroJump
  rw [srli_mem, addi_mem, sub_mem, jal_mem]

theorem zero_exit_reg (r : Reg) (h29 : r ≠ .x29) (h30 : r ≠ .x30) (h31 : r ≠ .x31) :
    (zeroLoopExit s).getReg r = s.getReg r := by
  have post := zero_loop_exit_post s atLeaves stride stop
  rw [post.1.regs r h29 h30 h31]
  unfold zeroLoopEntry maskShift maskOnes zeroStart zeroJump
  rw [srli_reg _ _ _ _ _ (Ne.symm h30), addi_reg _ _ _ _ _ (Ne.symm h30), sub_reg _ _ _ _ _ (Ne.symm h29), jal_reg]

end

private theorem set_reg_get (t : MachineState) (rd rs : Reg) (value : Word) :
    (t.setReg rd value).getReg rs = if rd = rs ∧ rd ≠ .x0 then value else t.getReg rs := by
  by_cases same : rd = rs
  · subst rs
    by_cases zero : rd = .x0
    · subst rd; rfl
    · simp [zero, MachineState.getReg_setReg_eq]
  · simp [same, MachineState.getReg_setReg_ne]

/-- Registers other than the pass's scratch registers `x29..x31` agree. -/
def AgreeOffScratch (t u : MachineState) : Prop :=
  ∀ r, r ≠ .x29 → r ≠ .x30 → r ≠ .x31 → t.getReg r = u.getReg r

theorem agree_addi {t u : MachineState} (h : AgreeOffScratch t u) (rd a : Reg) (i : BitVec 12)
    (ha29 : a ≠ .x29) (ha30 : a ≠ .x30) (ha31 : a ≠ .x31) :
    AgreeOffScratch (execInstrBr t (.ADDI rd a i)) (execInstrBr u (.ADDI rd a i)) := by
  intro r h29 h30 h31
  simp only [execInstrBr, MachineState.getReg_setPC, set_reg_get, h a ha29 ha30 ha31, h r h29 h30 h31]

theorem agree_sub {t u : MachineState} (h : AgreeOffScratch t u) (rd a b : Reg)
    (ha29 : a ≠ .x29) (ha30 : a ≠ .x30) (ha31 : a ≠ .x31)
    (hb29 : b ≠ .x29) (hb30 : b ≠ .x30) (hb31 : b ≠ .x31) :
    AgreeOffScratch (execInstrBr t (.SUB rd a b)) (execInstrBr u (.SUB rd a b)) := by
  intro r h29 h30 h31
  simp only [execInstrBr, MachineState.getReg_setPC, set_reg_get, h a ha29 ha30 ha31, h b hb29 hb30 hb31,
    h r h29 h30 h31]

theorem zero_entry_agree (s : MachineState) (atLeaves : s.pc = 184608)
    (stride : s.getReg .x19 = 536870912) (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) :
    AgreeOffScratch (zeroEntry s) (parentSetup s 5) := by
  have exit_ : AgreeOffScratch (zeroLoopExit s) s := zero_exit_reg s atLeaves stride stop
  have a := agree_addi exit_ .x10 .x21 4032 (by decide) (by decide) (by decide)
  have b : AgreeOffScratch (execInstrBr (execInstrBr (zeroLoopExit s) zeroSource) zeroBack)
      (execInstrBr s (.ADDI .x10 .x21 4032)) := by
    intro r h29 h30 h31
    unfold zeroBack zeroSource
    rw [jal_reg]
    exact a r h29 h30 h31
  unfold zeroEntry zeroB zeroA zeroTail parentSetup parentSetupOps
  simp only [List.drop, List.take, List.foldl]
  exact agree_addi (agree_addi (agree_addi (agree_sub b .x12 .x21 .x19 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))
    .x12 .x12 4064 (by decide) (by decide) (by decide)) .x11 .x0 64 (by decide) (by decide) (by decide))
    .x13 .x0 0 (by decide) (by decide) (by decide)

theorem zero_entry_pc (s : MachineState) (atLeaves : s.pc = 184608)
    (stride : s.getReg .x19 = 536870912) (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) :
    (zeroEntry s).pc = 184628 := by
  have post := zero_loop_exit_post s atLeaves stride stop
  unfold zeroEntry zeroB zeroA zeroTail parentSetupOps zeroBack zeroSource
  simp only [List.drop, List.foldl, addi_pc, sub_pc, jal_pc, post.2]
  rfl

attribute [local irreducible] execute packedWideCommitImage in
theorem zero_exit_steps (s : MachineState) (exitPC : (zeroLoopExit s).pc = zeroExitPC) (fuel : Nat) :
    execute packedWideCommitImage (2+fuel) (zeroLoopExit s) true =
      (do let result ← execute packedWideCommitImage fuel (zeroB s) true
          return result.charge 2 0) := by
  have apc : (zeroA s).pc = BitVec.ofNat 64 (4096+4*233482) := by
    unfold zeroA zeroSource; rw [addi_pc, exitPC]; rfl
  have stepA : ordinaryStep (zeroLoopExit s) (.base zeroSource) = some (zeroA s) := by
    unfold zeroA zeroSource; rfl
  have stepB : ordinaryStep (zeroA s) (.base zeroBack) = some (zeroB s) := by
    unfold zeroB zeroBack; rfl
  have fA := zero_fetch 233481 _ zero_decode_source (by decide) _ exitPC
  have fB := zero_fetch 233482 _ zero_decode_back (by decide) _ apc
  rw [Nat.add_comm 2 fuel, show fuel + 2 = (fuel+1)+1 by omega,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fA stepA,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fB stepB]
  simp only [bind_assoc, pure_bind, Execution.charge, instructionCycles, zeroSource, zeroBack, Nat.zero_add,
    show ∀ c, 1+(1+c) = 2+c from fun c => by omega]

attribute [local irreducible] execute packedWideCommitImage in
theorem zero_tail_steps (s : MachineState) (bpc : (zeroB s).pc = BitVec.ofNat 64 (4096+4*45129)) (fuel : Nat) :
    execute packedWideCommitImage (4+fuel) (zeroB s) true =
      (do let result ← execute packedWideCommitImage fuel (zeroEntry s) true
          return result.charge 4 0) := by
  have tailPC (i : Nat) (h : i < 4) : (zeroTailAt s i).pc = BitVec.ofNat 64 (4096+4*(45129+i)) := by
    interval_cases i <;> simp only [zeroTailAt, parentSetupOps, List.drop, List.take, List.foldl, addi_pc, sub_pc, bpc] <;> rfl
  have tailStep (i : Nat) (h : i < 4) : ordinaryStep (zeroTailAt s i) (.base ((parentSetupOps[i+1]?).getD .EBREAK)) =
      some (zeroTailAt s (i+1)) := by
    interval_cases i <;>
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, parentSetupOps, zeroTailAt, List.drop, List.take,
        List.foldl, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, ite_true]
  have run := CommitGolfCandidate.execute_unit_steps packedWideCommitImage 4 fuel (zeroTailAt s) true (by
    intro i inside
    refine ⟨_, packed_wide_fetch_parent_setup ⟨i, inside⟩ _ (tailPC i inside), tailStep i inside, ?_⟩
    interval_cases i <;> rfl)
  have done : zeroTailAt s 4 = zeroEntry s := by
    simp only [zeroTailAt, zeroEntry, zeroTail, parentSetupOps, List.drop, List.take]
  rw [← done]
  exact run

attribute [local irreducible] execute packedWideCommitImage in
theorem zero_entry_execute (s : MachineState) (atLeaves : s.pc = 184608)
    (stride : s.getReg .x19 = 536870912) (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) (fuel : Nat) :
    execute packedWideCommitImage (zeroEntryCost+fuel) s true =
      (do let result ← execute packedWideCommitImage fuel (zeroEntry s) true
          return result.charge zeroEntryCost 0) := by
  have entry := zero_loop_entry_at s atLeaves stride stop
  have post := zero_loop_exit_post s atLeaves stride stop
  have stop' : (zeroLoopEntry s).getReg .x21 = wordAddress (leafDest (2^24)) := by
    unfold zeroLoopEntry maskShift maskOnes zeroStart zeroJump
    rw [srli_reg _ _ _ _ _ (by decide), addi_reg _ _ _ _ _ (by decide), sub_reg _ _ _ _ _ (by decide), jal_reg, stop]
  let s1 := execInstrBr s zeroJump
  let s2 := execInstrBr s1 zeroStart
  let s3 := execInstrBr s2 maskOnes
  have pc1 : s1.pc = BitVec.ofNat 64 (4096+4*233380) := by
    unfold s1 zeroJump; rw [jal_pc, atLeaves]; rfl
  have pc2 : s2.pc = BitVec.ofNat 64 (4096+4*233381) := by
    unfold s2 zeroStart; rw [sub_pc, pc1]; rfl
  have pc3 : s3.pc = BitVec.ofNat 64 (4096+4*233382) := by
    unfold s3 maskOnes; rw [addi_pc, pc2]; rfl
  have fJ := zero_fetch 45128 _ zero_decode_jump (by decide) s (by rw [atLeaves]; rfl)
  have fS := zero_fetch 233380 _ zero_decode_start (by decide) _ pc1
  have fO := zero_fetch 233381 _ zero_decode_ones (by decide) _ pc2
  have fH := zero_fetch 233382 _ zero_decode_shift (by decide) _ pc3
  have stepJ : ordinaryStep s (.base zeroJump) = some s1 := by unfold s1 zeroJump; rfl
  have stepS : ordinaryStep s1 (.base zeroStart) = some s2 := by unfold s2 zeroStart; rfl
  have stepO : ordinaryStep s2 (.base maskOnes) = some s3 := by unfold s3 maskOnes; rfl
  have stepH : ordinaryStep s3 (.base maskShift) = some (zeroLoopEntry s) := by
    unfold zeroLoopEntry maskShift; rfl
  have loopRun := zero_loop_execute _ stop' (2^19) 0 (zeroLoopEntry s) entry.1 (fun _ => entry.2) (by omega) (2+(4+fuel))
  have exitEq : zeroLoop (2^19) (zeroLoopEntry s) = zeroLoopExit s := by unfold zeroLoopExit; rfl
  have apc : (zeroA s).pc = BitVec.ofNat 64 (4096+4*233482) := by
    unfold zeroA zeroSource; rw [addi_pc, post.2]; rfl
  have bpc : (zeroB s).pc = BitVec.ofNat 64 (4096+4*45129) := by
    unfold zeroB zeroBack; rw [jal_pc, apc]; rfl
  rw [show zeroEntryCost+fuel = ((((98*2^19+(2+(4+fuel)))+1)+1)+1)+1 by unfold zeroEntryCost; omega,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fJ stepJ,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fS stepS,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fO stepO,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fH stepH, loopRun, exitEq]
  simp only [bind_assoc, pure_bind]
  rw [zero_exit_steps s post.2]
  simp only [bind_assoc, pure_bind]
  rw [zero_tail_steps s bpc]
  simp only [bind_assoc, pure_bind, Execution.charge, instructionCycles, zeroJump, zeroStart, maskOnes, maskShift,
    zeroEntryCost, Nat.zero_add]
  have arith : ∀ c : Nat, 1 + (1 + (1 + (1 + (98 * 2 ^ 19 + (2 + (4 + c)))))) = 51380234 + c := fun c => by omega
  simp only [arith]

theorem zero_entry_ready (state : MachineState) (atSetup : state.pc=184608)
    (selector : state.getReg .x5=0) (heap : state.getReg .x9=4294971424)
    (stride : state.getReg .x19=536870912)
    (stop : state.getReg .x21=wordAddress (leafDest (2^24))) :
    ParentRegs (zeroEntry state) (2^24-1) ∧ (zeroEntry state).pc=184628 ∧
      (zeroEntry state).getReg .x8=state.getReg .x8 := by
  have old := packed_wide_parent_setup_ready state atSetup selector heap stride stop
  have agree := zero_entry_agree state atSetup stride stop
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩, zero_entry_pc state atSetup stride stop, ?_⟩
  · rw [agree _ (by decide) (by decide) (by decide)]; exact old.1.source
  · rw [agree _ (by decide) (by decide) (by decide)]; exact old.1.target
  · rw [agree _ (by decide) (by decide) (by decide)]; exact old.1.selector
  · rw [agree _ (by decide) (by decide) (by decide)]; exact old.1.size
  · rw [agree _ (by decide) (by decide) (by decide)]; exact old.1.primitive
  · rw [agree _ (by decide) (by decide) (by decide)]; exact old.1.heap
  · rw [agree _ (by decide) (by decide) (by decide)]; exact old.2.2

end TwoPermutationPrototype.RV64
