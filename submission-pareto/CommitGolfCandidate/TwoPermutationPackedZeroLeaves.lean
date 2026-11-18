import CommitGolfCandidate.TwoPermutationPackedSetup
import RiscvZkvm.Rv64.Logic.ByteOps

/-! After the leaf phase, commit clears bytes 30 and 31 of every leaf digest, so leaves keep
240 bits. The jump at word 45128 enters an appended loop
`sub t4,s5,s3; sh zero,30(t4); addi t4,t4,32; bne t4,s5; addi a0,s5,-64; jal 45129`,
after which the remaining four parent-setup instructions run as before. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def zeroJump : Instr := .JAL .x0 752788
def zeroStart : Instr := .SUB .x29 .x21 .x19
def zeroStore : Instr := .SH .x29 .x0 30
def zeroAdvance : Instr := .ADDI .x29 .x29 32
def zeroBranch : Instr := .BNE .x29 .x21 8184
def zeroSource : Instr := .ADDI .x10 .x21 4032
def zeroBack : Instr := .JAL .x0 1344348

private theorem zero_decode_jump : Manifest.decodeBase (packed_wideCodeWord 45128) = some zeroJump := by decide +kernel
private theorem zero_decode_start : Manifest.decodeBase (packed_wideCodeWord 233325) = some zeroStart := by decide +kernel
private theorem zero_decode_store : Manifest.decodeBase (packed_wideCodeWord 233326) = some zeroStore := by decide +kernel
private theorem zero_decode_advance : Manifest.decodeBase (packed_wideCodeWord 233327) = some zeroAdvance := by decide +kernel
private theorem zero_decode_branch : Manifest.decodeBase (packed_wideCodeWord 233328) = some zeroBranch := by decide +kernel
private theorem zero_decode_source : Manifest.decodeBase (packed_wideCodeWord 233329) = some zeroSource := by decide +kernel
private theorem zero_decode_back : Manifest.decodeBase (packed_wideCodeWord 233330) = some zeroBack := by decide +kernel

theorem zero_fetch (index : Nat) (instruction : Instr)
    (decoded : Manifest.decodeBase (packed_wideCodeWord index) = some instruction)
    (inCode : index < 233331) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*index)) :
    fetch packedWideCommitImage state = some (.base instruction) :=
  packed_wide_fetch_decoded state index inCode pc instruction decoded

/-- Word address of the doubleword holding bytes 30 and 31 of leaf `i`. -/
def zeroAddress (i : Nat) : Word := wordAddress (leafDest i + 3)

open Classical in
/-- Memory with bytes 30 and 31 of the first `count` leaf digests cleared. -/
noncomputable def zeroedMemory (m : Word → Word) (count : Nat) : Word → Word :=
  fun a => if ∃ i < count, a = zeroAddress i then replaceHalfword (m a) 3 0 else m a

theorem zeroed_hit (m : Word → Word) (count : Nat) (a : Word) (h : ∃ i < count, a = zeroAddress i) :
    zeroedMemory m count a = replaceHalfword (m a) 3 0 := by
  unfold zeroedMemory; exact if_pos h

theorem zeroed_miss (m : Word → Word) (count : Nat) (a : Word) (h : ¬ ∃ i < count, a = zeroAddress i) :
    zeroedMemory m count a = m a := by
  unfold zeroedMemory; exact if_neg h

theorem zero_address_injective {i j : Nat} (hi : i < 2^24) (hj : j < 2^24)
    (same : zeroAddress i = zeroAddress j) : i = j := by
  have n := congrArg BitVec.toNat same
  simp only [zeroAddress, wordAddress, leafDest, BitVec.toNat_ofNat] at n
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at n
  omega

theorem zeroed_memory_zero (m : Word → Word) : zeroedMemory m 0 = m := by
  funext a
  simp [zeroedMemory]

private theorem byte_offset_aligned (word i : Nat) (small : i < 8) :
    byteOffset (BitVec.ofNat 64 (8*word+i)) = i := by
  unfold byteOffset
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change ((8*word+i)%2^64) &&& (2^3-1) = i
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem align_word (word i : Nat) (small : i < 8) :
    alignToDword (BitVec.ofNat 64 (8*word+i)) = BitVec.ofNat 64 (8*word) := by
  have split := alignToDword_add_byteOffset (BitVec.ofNat 64 (8*word+i))
  rw [byte_offset_aligned word i small] at split
  have joined : BitVec.ofNat 64 (8*word) + BitVec.ofNat 64 i = BitVec.ofNat 64 (8*word+i) := by
    rw [← BitVec.ofNat_add]
  have eq := congrArg (fun v : Word => v-BitVec.ofNat 64 i) (split.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using eq

/-- One loop iteration: store, advance, branch. -/
def zeroBody (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr s zeroStore) zeroAdvance) zeroBranch

def zeroLoop : Nat → MachineState → MachineState
  | 0, s => s
  | k+1, s => zeroLoop k (zeroBody s)

def zeroLoopPC : Word := BitVec.ofNat 64 (4096+4*233326)
def zeroExitPC : Word := BitVec.ofNat 64 (4096+4*233329)

theorem set_pc_mem (t : MachineState) (v : Word) : (t.setPC v).mem = t.mem := rfl

structure ZeroAt (s0 : MachineState) (j : Nat) (st : MachineState) : Prop where
  cursor : st.getReg .x29 = wordAddress (leafDest j)
  regs : ∀ r, r ≠ .x29 → st.getReg r = s0.getReg r
  mem : st.mem = zeroedMemory s0.mem j

theorem zero_body_mem (s0 st : MachineState) (j : Nat) (bound : j < 2^24) (at_ : ZeroAt s0 j st) :
    (zeroBody st).mem = zeroedMemory s0.mem (j+1) := by
  have addr : st.getReg .x29 + signExtend12 30 = BitVec.ofNat 64 (8*(leafDest j+3)+6) := by
    rw [at_.cursor]
    unfold wordAddress
    rw [show signExtend12 (30 : BitVec 12) = BitVec.ofNat 64 30 by decide, ← BitVec.ofNat_add]
    congr 1
  have store : (execInstrBr st zeroStore).mem =
      (st.setMem (zeroAddress j) (replaceHalfword (st.mem (zeroAddress j)) 3 0)).mem := by
    simp only [zeroStore, execInstrBr, MachineState.setHalfword, addr, align_word _ 6 (by decide),
      byte_offset_aligned _ 6 (by decide)]
    rfl
  have branchMem (t : MachineState) : (execInstrBr t zeroBranch).mem = t.mem := by
    simp only [zeroBranch, execInstrBr]; split <;> exact set_pc_mem _ _
  have viaStore : (zeroBody st).mem = (execInstrBr st zeroStore).mem := by
    have advanceMem : (execInstrBr (execInstrBr st zeroStore) zeroAdvance).mem = (execInstrBr st zeroStore).mem := by
      simp only [zeroAdvance, execInstrBr, MachineState.setReg, MachineState.setPC]
    unfold zeroBody; rw [branchMem, advanceMem]
  rw [viaStore, store]
  funext a
  simp only [MachineState.setMem, at_.mem, zeroedMemory]
  by_cases hit : a = zeroAddress j
  · subst hit
    have fresh : ¬ ∃ i < j, zeroAddress j = zeroAddress i := by
      rintro ⟨i, lt, same⟩
      have := zero_address_injective (by omega) (by omega) same
      omega
    simp only [beq_self_eq_true, ite_true, fresh, ite_false]
    rw [if_pos ⟨j, by omega, rfl⟩]
  · have neq : (a == zeroAddress j) = false := by simpa using hit
    have iff : (∃ i < j+1, a = zeroAddress i) ↔ (∃ i < j, a = zeroAddress i) := by
      constructor
      · rintro ⟨i, lt, same⟩
        refine ⟨i, ?_, same⟩
        by_contra ge
        exact hit (by rw [same, show i = j by omega])
      · rintro ⟨i, lt, same⟩
        exact ⟨i, by omega, same⟩
    simp only [neq, Bool.false_eq_true, ite_false, iff]

private theorem get_reg_set_mem (t : MachineState) (a v : Word) (r : Reg) :
    (t.setMem a v).getReg r = t.getReg r := by cases r <;> rfl

theorem zero_store_reg (t : MachineState) (r : Reg) : (execInstrBr t zeroStore).getReg r = t.getReg r := by
  simp only [zeroStore, execInstrBr, MachineState.getReg_setPC, MachineState.setHalfword, get_reg_set_mem]

theorem zero_branch_reg (t : MachineState) (r : Reg) : (execInstrBr t zeroBranch).getReg r = t.getReg r := by
  simp only [zeroBranch, execInstrBr]; split <;> exact MachineState.getReg_setPC

theorem zero_advance_reg (t : MachineState) (r : Reg) (ne : r ≠ .x29) :
    (execInstrBr t zeroAdvance).getReg r = t.getReg r := by
  simp only [zeroAdvance, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]

theorem zero_advance_cursor (t : MachineState) :
    (execInstrBr t zeroAdvance).getReg .x29 = t.getReg .x29 + signExtend12 32 := by
  simp only [zeroAdvance, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (r := .x29) (by decide)]

theorem zero_store_pc (t : MachineState) : (execInstrBr t zeroStore).pc = t.pc + 4 := by
  simp only [zeroStore, execInstrBr, MachineState.setPC, MachineState.setHalfword, MachineState.setMem]

theorem zero_advance_pc (t : MachineState) : (execInstrBr t zeroAdvance).pc = t.pc + 4 := by
  simp only [zeroAdvance, execInstrBr, MachineState.setPC, MachineState.setReg]

theorem zero_body_regs (st : MachineState) (r : Reg) (ne : r ≠ .x29) :
    (zeroBody st).getReg r = st.getReg r := by
  unfold zeroBody
  rw [zero_branch_reg, zero_advance_reg _ _ ne, zero_store_reg]

theorem zero_body_cursor (st : MachineState) (j : Nat) (cursor : st.getReg .x29 = wordAddress (leafDest j)) :
    (zeroBody st).getReg .x29 = wordAddress (leafDest (j+1)) := by
  unfold zeroBody
  rw [zero_branch_reg, zero_advance_cursor, zero_store_reg, cursor]
  unfold wordAddress leafDest
  rw [show signExtend12 (32 : BitVec 12) = BitVec.ofNat 64 32 by decide, ← BitVec.ofNat_add]
  congr 1

theorem zero_body_at (s0 st : MachineState) (j : Nat) (bound : j < 2^24) (at_ : ZeroAt s0 j st) :
    ZeroAt s0 (j+1) (zeroBody st) :=
  ⟨zero_body_cursor st j at_.cursor, fun r ne => (zero_body_regs st r ne).trans (at_.regs r ne),
    zero_body_mem s0 st j bound at_⟩

theorem zero_body_pc (s0 st : MachineState) (j : Nat) (bound : j < 2^24) (at_ : ZeroAt s0 j st)
    (stop : s0.getReg .x21 = wordAddress (leafDest (2^24))) (pc : st.pc = zeroLoopPC) :
    (zeroBody st).pc = if j+1 = 2^24 then zeroExitPC else zeroLoopPC := by
  let t := execInstrBr (execInstrBr st zeroStore) zeroAdvance
  have tpc : t.pc = zeroLoopPC + 8 := by
    simp only [t]
    rw [zero_advance_pc, zero_store_pc, pc, BitVec.add_assoc]; rfl
  have cur : t.getReg .x29 = wordAddress (leafDest (j+1)) := by
    have := zero_body_cursor st j at_.cursor
    unfold zeroBody at this
    rwa [zero_branch_reg] at this
  have end_ : t.getReg .x21 = wordAddress (leafDest (2^24)) := by
    have := zero_body_regs st .x21 (by decide)
    unfold zeroBody at this
    rw [zero_branch_reg] at this
    exact this.trans ((at_.regs _ (by decide)).trans stop)
  change (execInstrBr t zeroBranch).pc = _
  simp only [zeroBranch, execInstrBr, cur, end_]
  by_cases last : j+1 = 2^24
  · have same : (wordAddress (leafDest (j+1)) != wordAddress (leafDest (2^24))) = false := by
      rw [last]; simp
    rw [if_pos last]
    simp only [same, Bool.false_eq_true, if_false, MachineState.setPC, tpc]
    rfl
  · have differ : wordAddress (leafDest (j+1)) ≠ wordAddress (leafDest (2^24)) := by
      intro same
      have n := congrArg BitVec.toNat same
      simp only [wordAddress, leafDest, BitVec.toNat_ofNat] at n
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at n
      omega
    have taken : (wordAddress (leafDest (j+1)) != wordAddress (leafDest (2^24))) = true := by
      simpa using differ
    rw [if_neg last]
    simp only [taken, if_true, MachineState.setPC, tpc]
    rfl

private theorem pc_word (base : Nat) (off : Nat) :
    BitVec.ofNat 64 (4096+4*base) + BitVec.ofNat 64 (4*off) = BitVec.ofNat 64 (4096+4*(base+off)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

theorem zero_body_steps (s0 st : MachineState) (j : Nat) (bound : j < 2^24) (at_ : ZeroAt s0 j st)
    (pc : st.pc = zeroLoopPC) (fuel : Nat) :
    execute packedWideCommitImage (3+fuel) st true =
      (do let result ← execute packedWideCommitImage fuel (zeroBody st) true
          return result.charge 3 0) := by
  let states : Nat → MachineState := fun i =>
    if i = 0 then st else if i = 1 then execInstrBr st zeroStore
    else if i = 2 then execInstrBr (execInstrBr st zeroStore) zeroAdvance else zeroBody st
  have pc1 : (execInstrBr st zeroStore).pc = BitVec.ofNat 64 (4096+4*233327) := by
    rw [zero_store_pc, pc]; rfl
  have pc2 : (execInstrBr (execInstrBr st zeroStore) zeroAdvance).pc = BitVec.ofNat 64 (4096+4*233328) := by
    rw [zero_advance_pc, pc1]; rfl
  have addrValid : memoryArgumentsValid st zeroStore = true := by
    have addr : st.getReg .x29 + signExtend12 30 = BitVec.ofNat 64 (8*(leafDest j+3)+6) := by
      rw [at_.cursor]
      unfold wordAddress
      rw [show signExtend12 (30 : BitVec 12) = BitVec.ofNat 64 30 by decide, ← BitVec.ofNat_add]
      congr 1
    simp only [memoryArgumentsValid, memAccess, zeroStore, addr, accessValid, rangeValid, BitVec.toNat_ofNat,
      Bool.and_eq_true, decide_eq_true_eq]
    unfold leafDest
    constructor <;> simp [MEMORY_BYTES] <;> omega
  have run := CommitGolfCandidate.execute_unit_steps packedWideCommitImage 3 fuel states true (by
    intro i inside
    interval_cases i
    · refine ⟨.base zeroStore, zero_fetch 233326 _ zero_decode_store (by decide) _ pc, ?_, rfl⟩
      unfold zeroStore at addrValid ⊢
      simp only [ordinaryStep, addrValid, ite_true, states]; rfl
    · refine ⟨.base zeroAdvance, zero_fetch 233327 _ zero_decode_advance (by decide) _ pc1, ?_, rfl⟩
      unfold zeroAdvance
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, states]; rfl
    · refine ⟨.base zeroBranch, zero_fetch 233328 _ zero_decode_branch (by decide) _ pc2, ?_, rfl⟩
      unfold zeroBranch
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, states]; rfl)
  exact run

theorem zero_loop_execute (s0 : MachineState) (stop : s0.getReg .x21 = wordAddress (leafDest (2^24))) :
    ∀ (k j : Nat) (st : MachineState), ZeroAt s0 j st → (0 < k → st.pc = zeroLoopPC) → j + k = 2^24 →
      ∀ fuel, execute packedWideCommitImage (3*k+fuel) st true =
        (do let result ← execute packedWideCommitImage fuel (zeroLoop k st) true
            return result.charge (3*k) 0) := by
  intro k
  induction k with
  | zero =>
    intro j st _ _ _ fuel
    simp [zeroLoop, Execution.charge]
  | succ k ih =>
    intro j st at_ pc sum fuel
    have bound : j < 2^24 := by omega
    have here := pc (by omega)
    rw [show 3*(k+1)+fuel = 3+(3*k+fuel) by omega, zero_body_steps s0 st j bound at_ here]
    have next := zero_body_at s0 st j bound at_
    have nextPC : 0 < k → (zeroBody st).pc = zeroLoopPC := by
      intro positive
      rw [zero_body_pc s0 st j bound at_ stop here, if_neg (by omega)]
    rw [ih (j+1) (zeroBody st) next nextPC (by omega) fuel]
    simp only [zeroLoop, bind_assoc, pure_bind, Execution.charge]
    simp only [show ∀ c, 3 + (3*k+c) = 3*(k+1)+c from fun c => by omega, Nat.zero_add]

theorem zero_loop_post (s0 : MachineState) (stop : s0.getReg .x21 = wordAddress (leafDest (2^24))) :
    ∀ (k j : Nat) (st : MachineState), ZeroAt s0 j st → (0 < k → st.pc = zeroLoopPC) → j + k = 2^24 → 0 < k →
      ZeroAt s0 (2^24) (zeroLoop k st) ∧ (zeroLoop k st).pc = zeroExitPC := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ impossible; omega
  | succ k ih =>
    intro j st at_ pc sum _
    have bound : j < 2^24 := by omega
    have here := pc (by omega)
    have next := zero_body_at s0 st j bound at_
    have nextPC := zero_body_pc s0 st j bound at_ stop here
    by_cases last : k = 0
    · subst last
      have full : j + 1 = 2^24 := by omega
      rw [full] at next
      rw [if_pos full] at nextPC
      exact ⟨next, nextPC⟩
    · exact ih (j+1) (zeroBody st) next (fun _ => by rw [nextPC, if_neg (by omega)]) (by omega) (by omega)

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
theorem sub_pc (t : MachineState) (rd a b : Reg) : (execInstrBr t (.SUB rd a b)).pc = t.pc + 4 := by
  cases rd <;> rfl
theorem addi_pc (t : MachineState) (rd a : Reg) (i : BitVec 12) : (execInstrBr t (.ADDI rd a i)).pc = t.pc + 4 := by
  cases rd <;> rfl
theorem sub_reg (t : MachineState) (rd a b r : Reg) (ne : rd ≠ r) :
    (execInstrBr t (.SUB rd a b)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
theorem addi_reg (t : MachineState) (rd a r : Reg) (i : BitVec 12) (ne : rd ≠ r) :
    (execInstrBr t (.ADDI rd a i)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
theorem sub_dest (t : MachineState) (rd a b : Reg) (ne : rd ≠ .x0) :
    (execInstrBr t (.SUB rd a b)).getReg rd = t.getReg a - t.getReg b := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq ne]
theorem addi_dest (t : MachineState) (rd a : Reg) (i : BitVec 12) (ne : rd ≠ .x0) :
    (execInstrBr t (.ADDI rd a i)).getReg rd = t.getReg a + signExtend12 i := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq ne]

def zeroLoopEntry (s : MachineState) : MachineState := execInstrBr (execInstrBr s zeroJump) zeroStart
def zeroTail (t : MachineState) : MachineState := (parentSetupOps.drop 1).foldl execInstrBr t
def zeroLoopExit (s : MachineState) : MachineState := zeroLoop (2^24) (zeroLoopEntry s)
def zeroA (s : MachineState) : MachineState := execInstrBr (zeroLoopExit s) zeroSource
def zeroB (s : MachineState) : MachineState := execInstrBr (zeroA s) zeroBack
def zeroTailAt (s : MachineState) (i : Nat) : MachineState := ((parentSetupOps.drop 1).take i).foldl execInstrBr (zeroB s)
def zeroEntry (s : MachineState) : MachineState := zeroTail (zeroB s)

def zeroEntryCost : Nat := 50331656

attribute [irreducible] zeroLoop zeroLoopExit

theorem zero_tail_mem (t : MachineState) : (zeroTail t).mem = t.mem := by
  simp only [zeroTail, parentSetupOps, List.drop, List.foldl, sub_mem, addi_mem]

section
variable (s : MachineState) (atLeaves : s.pc = 184608)
  (stride : s.getReg .x19 = 536870912) (stop : s.getReg .x21 = wordAddress (leafDest (2^24)))
include atLeaves stride stop

theorem zero_loop_entry_at : ZeroAt (zeroLoopEntry s) 0 (zeroLoopEntry s) ∧ (zeroLoopEntry s).pc = zeroLoopPC := by
  refine ⟨⟨?_, fun _ _ => rfl, (zeroed_memory_zero _).symm⟩, ?_⟩
  · unfold zeroLoopEntry zeroStart zeroJump
    rw [sub_dest _ _ _ _ (by decide), jal_reg, jal_reg, stop, stride]
    unfold wordAddress leafDest
    rw [show (536870912 : Word) = BitVec.ofNat 64 536870912 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    congr 1
  · unfold zeroLoopEntry zeroStart zeroJump
    rw [sub_pc, jal_pc, atLeaves]; rfl

theorem zero_loop_exit_post :
    ZeroAt (zeroLoopEntry s) (2^24) (zeroLoopExit s) ∧ (zeroLoopExit s).pc = zeroExitPC := by
  have entry := zero_loop_entry_at s atLeaves stride stop
  have stop' : (zeroLoopEntry s).getReg .x21 = wordAddress (leafDest (2^24)) := by
    unfold zeroLoopEntry zeroStart zeroJump; rw [sub_reg _ _ _ _ _ (by decide), jal_reg, stop]
  unfold zeroLoopExit
  exact zero_loop_post _ stop' (2^24) 0 _ entry.1 (fun _ => entry.2) (by omega) (by decide)

theorem zero_entry_mem : (zeroEntry s).mem = zeroedMemory s.mem (2^24) := by
  have post := zero_loop_exit_post s atLeaves stride stop
  unfold zeroEntry zeroB zeroA zeroBack zeroSource
  rw [zero_tail_mem, jal_mem, addi_mem, post.1.mem]
  unfold zeroLoopEntry zeroStart zeroJump
  rw [sub_mem, jal_mem]

theorem zero_exit_reg (r : Reg) (ne : r ≠ .x29) : (zeroLoopExit s).getReg r = s.getReg r := by
  have post := zero_loop_exit_post s atLeaves stride stop
  rw [post.1.regs r ne]
  unfold zeroLoopEntry zeroStart zeroJump
  rw [sub_reg _ _ _ _ _ (Ne.symm ne), jal_reg]

end

private theorem set_reg_get (t : MachineState) (rd rs : Reg) (value : Word) :
    (t.setReg rd value).getReg rs = if rd = rs ∧ rd ≠ .x0 then value else t.getReg rs := by
  by_cases same : rd = rs
  · subst rs
    by_cases zero : rd = .x0
    · subst rd; rfl
    · simp [zero, MachineState.getReg_setReg_eq]
  · simp [same, MachineState.getReg_setReg_ne]

def AgreeOff29 (t u : MachineState) : Prop := ∀ r, r ≠ .x29 → t.getReg r = u.getReg r

theorem agree_addi {t u : MachineState} (h : AgreeOff29 t u) (rd a : Reg) (i : BitVec 12) (ha : a ≠ .x29) :
    AgreeOff29 (execInstrBr t (.ADDI rd a i)) (execInstrBr u (.ADDI rd a i)) := by
  intro r hr
  simp only [execInstrBr, MachineState.getReg_setPC, set_reg_get, h a ha, h r hr]

theorem agree_sub {t u : MachineState} (h : AgreeOff29 t u) (rd a b : Reg) (ha : a ≠ .x29) (hb : b ≠ .x29) :
    AgreeOff29 (execInstrBr t (.SUB rd a b)) (execInstrBr u (.SUB rd a b)) := by
  intro r hr
  simp only [execInstrBr, MachineState.getReg_setPC, set_reg_get, h a ha, h b hb, h r hr]

theorem zero_entry_agree (s : MachineState) (atLeaves : s.pc = 184608)
    (stride : s.getReg .x19 = 536870912) (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) :
    AgreeOff29 (zeroEntry s) (parentSetup s 5) := by
  have exit_ : AgreeOff29 (zeroLoopExit s) s := zero_exit_reg s atLeaves stride stop
  have a := agree_addi exit_ .x10 .x21 4032 (by decide)
  have b : AgreeOff29 (execInstrBr (execInstrBr (zeroLoopExit s) zeroSource) zeroBack)
      (execInstrBr s (.ADDI .x10 .x21 4032)) := by
    intro r hr
    unfold zeroBack zeroSource
    rw [jal_reg]
    exact a r hr
  unfold zeroEntry zeroB zeroA zeroTail parentSetup parentSetupOps
  simp only [List.drop, List.take, List.foldl]
  exact agree_addi (agree_addi (agree_addi (agree_sub b .x12 .x21 .x19 (by decide) (by decide))
    .x12 .x12 4064 (by decide)) .x11 .x0 64 (by decide)) .x13 .x0 0 (by decide)

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
  have apc : (zeroA s).pc = BitVec.ofNat 64 (4096+4*233330) := by
    unfold zeroA zeroSource; rw [addi_pc, exitPC]; rfl
  have stepA : ordinaryStep (zeroLoopExit s) (.base zeroSource) = some (zeroA s) := by
    unfold zeroA zeroSource; rfl
  have stepB : ordinaryStep (zeroA s) (.base zeroBack) = some (zeroB s) := by
    unfold zeroB zeroBack; rfl
  have fA := zero_fetch 233329 _ zero_decode_source (by decide) _ exitPC
  have fB := zero_fetch 233330 _ zero_decode_back (by decide) _ apc
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
    unfold zeroLoopEntry zeroStart zeroJump; rw [sub_reg _ _ _ _ _ (by decide), jal_reg, stop]
  have jpc : (execInstrBr s zeroJump).pc = BitVec.ofNat 64 (4096+4*233325) := by
    unfold zeroJump; rw [jal_pc, atLeaves]; rfl
  have fJ := zero_fetch 45128 _ zero_decode_jump (by decide) s (by rw [atLeaves]; rfl)
  have fS := zero_fetch 233325 _ zero_decode_start (by decide) _ jpc
  have stepJ : ordinaryStep s (.base zeroJump) = some (execInstrBr s zeroJump) := by unfold zeroJump; rfl
  have stepS : ordinaryStep (execInstrBr s zeroJump) (.base zeroStart) = some (zeroLoopEntry s) := by
    unfold zeroLoopEntry zeroStart; rfl
  have loopRun := zero_loop_execute _ stop' (2^24) 0 (zeroLoopEntry s) entry.1 (fun _ => entry.2) (by omega) (2+(4+fuel))
  have exitEq : zeroLoop (2^24) (zeroLoopEntry s) = zeroLoopExit s := by unfold zeroLoopExit; rfl
  have apc : (zeroA s).pc = BitVec.ofNat 64 (4096+4*233330) := by
    unfold zeroA zeroSource; rw [addi_pc, post.2]; rfl
  have bpc : (zeroB s).pc = BitVec.ofNat 64 (4096+4*45129) := by
    unfold zeroB zeroBack; rw [jal_pc, apc]; rfl
  rw [show zeroEntryCost+fuel = ((3*2^24+(2+(4+fuel)))+1)+1 by unfold zeroEntryCost; omega,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fJ stepJ,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fS stepS, loopRun, exitEq]
  simp only [bind_assoc, pure_bind]
  rw [zero_exit_steps s post.2]
  simp only [bind_assoc, pure_bind]
  rw [zero_tail_steps s bpc]
  simp only [bind_assoc, pure_bind, Execution.charge, instructionCycles, zeroJump, zeroStart, zeroEntryCost,
    Nat.zero_add]
  have arith : ∀ c : Nat, 1 + (1 + (3 * 2 ^ 24 + (2 + (4 + c)))) = 50331656 + c := fun c => by omega
  simp only [arith]

end TwoPermutationPrototype.RV64

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem zero_entry_ready (state : MachineState) (atSetup : state.pc=184608)
    (selector : state.getReg .x5=0) (heap : state.getReg .x9=4294971424)
    (stride : state.getReg .x19=536870912)
    (stop : state.getReg .x21=wordAddress (leafDest (2^24))) :
    ParentRegs (zeroEntry state) (2^24-1) ∧ (zeroEntry state).pc=184628 ∧
      (zeroEntry state).getReg .x8=state.getReg .x8 := by
  have old := packed_wide_parent_setup_ready state atSetup selector heap stride stop
  have agree := zero_entry_agree state atSetup stride stop
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩, zero_entry_pc state atSetup stride stop, ?_⟩
  · rw [agree _ (by decide)]; exact old.1.source
  · rw [agree _ (by decide)]; exact old.1.target
  · rw [agree _ (by decide)]; exact old.1.selector
  · rw [agree _ (by decide)]; exact old.1.size
  · rw [agree _ (by decide)]; exact old.1.primitive
  · rw [agree _ (by decide)]; exact old.1.heap
  · rw [agree _ (by decide)]; exact old.2.2

end TwoPermutationPrototype.RV64
