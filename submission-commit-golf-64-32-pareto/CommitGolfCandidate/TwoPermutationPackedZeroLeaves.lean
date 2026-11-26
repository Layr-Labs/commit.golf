import CommitGolfCandidate.TwoPermutationPackedSetup
import RiscvZkvm.Rv64.Logic.ByteOps

/-! After the leaf phase, commit clears bytes 30 and 31 of every leaf digest, so leaves keep
240 bits. The jump at word 45128 enters an appended loop
an unrolled loop of 128 `sh zero,30+32j(t4)` stores per iteration, then `addi a0,s5,-64; jal 45129`,
after which the remaining four parent-setup instructions run as before. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 65536
set_option maxHeartbeats 1500000


def zeroJump : Instr := .JAL .x0 752788
def zeroSetupOps : List Instr :=
  [.SUB .x29 .x21 .x19, .ADDI .x29 .x29 2047, .ADDI .x29 .x29 1,
   .ADDI .x30 .x21 2047, .ADDI .x30 .x30 1, .LUI .x31 1]
def zeroStoreAt (i : Nat) : Instr := .SH .x29 .x0 (BitVec.ofNat 12 (2078+32*i))
def zeroAdvance : Instr := .ADD .x29 .x29 .x31
def zeroBranch : Instr := .BNE .x29 .x30 7676
def zeroSource : Instr := .ADDI .x10 .x21 4032
def zeroBack : Instr := .JAL .x0 1343820

private theorem zero_decode_jump : Manifest.decodeBase (packed_wideCodeWord 45128) = some zeroJump := by decide +kernel
private theorem zero_decode_setup : ∀ i : Fin 6,
    Manifest.decodeBase (packed_wideCodeWord (233325+i.val)) = some ((zeroSetupOps[i.val]?).getD .EBREAK) := by
  decide +kernel
private theorem zero_decode_stores : ∀ i : Fin 128,
    Manifest.decodeBase (packed_wideCodeWord (233331+i.val)) = some (zeroStoreAt i.val) := by decide +kernel
private theorem zero_decode_advance : Manifest.decodeBase (packed_wideCodeWord 233459) = some zeroAdvance := by decide +kernel
private theorem zero_decode_branch : Manifest.decodeBase (packed_wideCodeWord 233460) = some zeroBranch := by decide +kernel
private theorem zero_decode_source : Manifest.decodeBase (packed_wideCodeWord 233461) = some zeroSource := by decide +kernel
private theorem zero_decode_back : Manifest.decodeBase (packed_wideCodeWord 233462) = some zeroBack := by decide +kernel

private theorem store_offsets : ∀ i : Fin 128,
    signExtend12 (BitVec.ofNat 12 (2078+32*i.val)) = -(2048 : Word) + BitVec.ofNat 64 (30+32*i.val) := by
  decide +kernel

theorem zero_fetch (index : Nat) (instruction : Instr)
    (decoded : Manifest.decodeBase (packed_wideCodeWord index) = some instruction)
    (inCode : index < 233463) (state : MachineState)
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


theorem set_pc_mem (t : MachineState) (v : Word) : (t.setPC v).mem = t.mem := rfl

private theorem get_reg_set_mem (t : MachineState) (a v : Word) (r : Reg) :
    (t.setMem a v).getReg r = t.getReg r := by cases r <;> rfl

/-- Cursor of loop iteration `k`: 2048 bytes past the first leaf of block `k`. -/
def cursorWord (k : Nat) : Word := BitVec.ofNat 64 (8*leafDest (128*k) + 2048)

def zeroStores (st : MachineState) : Nat → MachineState
  | 0 => st
  | i+1 => execInstrBr (zeroStores st i) (zeroStoreAt i)

/-- One loop iteration: 128 stores, advance, branch. -/
def zeroBody (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (zeroStores s 128) zeroAdvance) zeroBranch

def zeroLoop : Nat → MachineState → MachineState
  | 0, s => s
  | k+1, s => zeroLoop k (zeroBody s)

def zeroLoopPC : Word := BitVec.ofNat 64 (4096+4*233331)
def zeroExitPC : Word := BitVec.ofNat 64 (4096+4*233461)

structure ZeroAt (s0 : MachineState) (k : Nat) (st : MachineState) : Prop where
  cursor : st.getReg .x29 = cursorWord k
  regs : ∀ r, r ≠ .x29 → st.getReg r = s0.getReg r
  mem : st.mem = zeroedMemory s0.mem (128*k)

theorem zero_store_reg (t : MachineState) (i : Nat) (r : Reg) :
    (execInstrBr t (zeroStoreAt i)).getReg r = t.getReg r := by
  simp only [zeroStoreAt, execInstrBr, MachineState.getReg_setPC, MachineState.setHalfword, get_reg_set_mem]

theorem zero_store_pc (t : MachineState) (i : Nat) : (execInstrBr t (zeroStoreAt i)).pc = t.pc + 4 := by
  simp only [zeroStoreAt, execInstrBr, MachineState.setPC, MachineState.setHalfword, MachineState.setMem]

theorem zero_store_address (t : MachineState) (k i : Nat) (hi : i < 128) (cursor : t.getReg .x29 = cursorWord k) :
    t.getReg .x29 + signExtend12 (BitVec.ofNat 12 (2078+32*i)) = BitVec.ofNat 64 (8*(leafDest (128*k+i)+3)+6) := by
  rw [cursor, store_offsets ⟨i, hi⟩]
  unfold cursorWord
  rw [show (2048 : Word) = BitVec.ofNat 64 2048 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_neg, leafDest]
  omega

theorem zero_store_mem (t : MachineState) (m : Word → Word) (n : Nat) (bound : n < 2^24) (i : Nat)
    (mem : t.mem = zeroedMemory m n)
    (addr : t.getReg .x29 + signExtend12 (BitVec.ofNat 12 (2078+32*i)) = BitVec.ofNat 64 (8*(leafDest n+3)+6)) :
    (execInstrBr t (zeroStoreAt i)).mem = zeroedMemory m (n+1) := by
  have store : (execInstrBr t (zeroStoreAt i)).mem =
      (t.setMem (zeroAddress n) (replaceHalfword (t.mem (zeroAddress n)) 3 0)).mem := by
    simp only [zeroStoreAt, execInstrBr, MachineState.setHalfword, addr, align_word _ 6 (by decide),
      byte_offset_aligned _ 6 (by decide)]
    rfl
  rw [store]
  funext a
  simp only [MachineState.setMem, mem, zeroedMemory]
  by_cases hit : a = zeroAddress n
  · subst hit
    have fresh : ¬ ∃ j < n, zeroAddress n = zeroAddress j := by
      rintro ⟨j, lt, same⟩
      have := zero_address_injective (by omega) (by omega) same
      omega
    simp only [beq_self_eq_true, ite_true, fresh, ite_false]
    rw [if_pos ⟨n, by omega, rfl⟩]
  · have neq : (a == zeroAddress n) = false := by simpa using hit
    have iff : (∃ j < n+1, a = zeroAddress j) ↔ (∃ j < n, a = zeroAddress j) := by
      constructor
      · rintro ⟨j, lt, same⟩
        refine ⟨j, ?_, same⟩
        by_contra ge
        exact hit (by rw [same, show j = n by omega])
      · rintro ⟨j, lt, same⟩
        exact ⟨j, by omega, same⟩
    simp only [neq, Bool.false_eq_true, ite_false, iff]

theorem zero_stores_facts (s0 st : MachineState) (k : Nat) (bound : 128*k + 128 ≤ 2^24) (at_ : ZeroAt s0 k st) :
    ∀ i ≤ 128, (zeroStores st i).mem = zeroedMemory s0.mem (128*k+i) ∧
      (∀ r, (zeroStores st i).getReg r = st.getReg r) ∧ (zeroStores st i).pc = st.pc + BitVec.ofNat 64 (4*i) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨at_.mem, fun _ => rfl, by simp [zeroStores]⟩
  | succ i ih =>
    intro hi
    obtain ⟨mem, regs, pc⟩ := ih (by omega)
    refine ⟨?_, fun r => (zero_store_reg _ _ r).trans (regs r), ?_⟩
    · exact zero_store_mem _ _ (128*k+i) (by omega) i mem
        (zero_store_address _ k i (by omega) ((regs .x29).trans at_.cursor))
    · change (execInstrBr (zeroStores st i) (zeroStoreAt i)).pc = _
      rw [zero_store_pc, pc, BitVec.add_assoc]
      congr 1
      rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega

theorem zero_branch_mem (t : MachineState) : (execInstrBr t zeroBranch).mem = t.mem := by
  simp only [zeroBranch, execInstrBr]; split <;> exact set_pc_mem _ _

theorem zero_branch_reg (t : MachineState) (r : Reg) : (execInstrBr t zeroBranch).getReg r = t.getReg r := by
  simp only [zeroBranch, execInstrBr]; split <;> exact MachineState.getReg_setPC

theorem zero_advance_mem (t : MachineState) : (execInstrBr t zeroAdvance).mem = t.mem := by
  simp only [zeroAdvance, execInstrBr, MachineState.setReg, MachineState.setPC]

theorem zero_advance_reg (t : MachineState) (r : Reg) (ne : r ≠ .x29) :
    (execInstrBr t zeroAdvance).getReg r = t.getReg r := by
  simp only [zeroAdvance, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]

theorem zero_advance_cursor (t : MachineState) :
    (execInstrBr t zeroAdvance).getReg .x29 = t.getReg .x29 + t.getReg .x31 := by
  simp only [zeroAdvance, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (r := .x29) (by decide)]

theorem zero_advance_pc (t : MachineState) : (execInstrBr t zeroAdvance).pc = t.pc + 4 := by
  simp only [zeroAdvance, execInstrBr, MachineState.setPC, MachineState.setReg]

theorem cursor_step (k : Nat) (hk : k < 2^17) : cursorWord k + 4096 = cursorWord (k+1) := by
  unfold cursorWord leafDest
  rw [show (4096 : Word) = BitVec.ofNat 64 4096 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem cursor_injective {k l : Nat} (hk : k ≤ 2^17) (hl : l ≤ 2^17) (same : cursorWord k = cursorWord l) : k = l := by
  have n := congrArg BitVec.toNat same
  simp only [cursorWord, leafDest, BitVec.toNat_ofNat] at n
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at n
  omega

theorem zero_body_at (s0 st : MachineState) (k : Nat) (bound : k < 2^17) (at_ : ZeroAt s0 k st)
    (step : s0.getReg .x31 = 4096) : ZeroAt s0 (k+1) (zeroBody st) := by
  obtain ⟨mem, regs, _⟩ := zero_stores_facts s0 st k (by omega) at_ 128 le_rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold zeroBody
    rw [zero_branch_reg, zero_advance_cursor, regs, regs, at_.cursor, at_.regs _ (by decide), step, cursor_step k bound]
  · intro r ne
    unfold zeroBody
    rw [zero_branch_reg, zero_advance_reg _ _ ne, regs, at_.regs r ne]
  · unfold zeroBody
    rw [zero_branch_mem, zero_advance_mem, mem, show 128*k+128 = 128*(k+1) by ring]

theorem zero_body_pc (s0 st : MachineState) (k : Nat) (bound : k < 2^17) (at_ : ZeroAt s0 k st)
    (step : s0.getReg .x31 = 4096) (stop : s0.getReg .x30 = cursorWord (2^17)) (pc : st.pc = zeroLoopPC) :
    (zeroBody st).pc = if k+1 = 2^17 then zeroExitPC else zeroLoopPC := by
  obtain ⟨_, regs, spc⟩ := zero_stores_facts s0 st k (by omega) at_ 128 le_rfl
  let t := execInstrBr (zeroStores st 128) zeroAdvance
  have tpc : t.pc = zeroLoopPC + 516 := by
    simp only [t]
    rw [zero_advance_pc, spc, pc, BitVec.add_assoc]; rfl
  have cur : t.getReg .x29 = cursorWord (k+1) := by
    simp only [t]
    rw [zero_advance_cursor, regs, regs, at_.cursor, at_.regs _ (by decide), step, cursor_step k bound]
  have end_ : t.getReg .x30 = cursorWord (2^17) := by
    simp only [t]
    rw [zero_advance_reg _ _ (by decide), regs, at_.regs _ (by decide), stop]
  change (execInstrBr t zeroBranch).pc = _
  simp only [zeroBranch, execInstrBr, cur, end_]
  by_cases last : k+1 = 2^17
  · have same : (cursorWord (k+1) != cursorWord (2^17)) = false := by rw [last]; simp
    rw [if_pos last]
    simp only [same, Bool.false_eq_true, if_false, MachineState.setPC, tpc]
    rfl
  · have differ : cursorWord (k+1) ≠ cursorWord (2^17) := fun h => last (cursor_injective (by omega) le_rfl h)
    have taken : (cursorWord (k+1) != cursorWord (2^17)) = true := by simpa using differ
    rw [if_neg last]
    simp only [taken, if_true, MachineState.setPC, tpc]
    rfl

attribute [local irreducible] execute packedWideCommitImage in
theorem zero_body_steps (s0 st : MachineState) (k : Nat) (bound : k < 2^17) (at_ : ZeroAt s0 k st)
    (pc : st.pc = zeroLoopPC) (fuel : Nat) :
    execute packedWideCommitImage (130+fuel) st true =
      (do let result ← execute packedWideCommitImage fuel (zeroBody st) true
          return result.charge 130 0) := by
  have facts := zero_stores_facts s0 st k (by omega) at_
  let states : Nat → MachineState := fun i =>
    if i ≤ 128 then zeroStores st i
    else if i = 129 then execInstrBr (zeroStores st 128) zeroAdvance else zeroBody st
  have storePC (i : Nat) (hi : i ≤ 128) : (zeroStores st i).pc = BitVec.ofNat 64 (4096+4*(233331+i)) := by
    rw [(facts i hi).2.2, pc, zeroLoopPC, ← BitVec.ofNat_add]; congr 1; omega
  have run := CommitGolfCandidate.execute_unit_steps packedWideCommitImage 130 fuel states true (by
    intro i inside
    by_cases store : i < 128
    · refine ⟨.base (zeroStoreAt i), zero_fetch (233331+i) _ (zero_decode_stores ⟨i, store⟩) (by omega) _ ?_, ?_, rfl⟩
      · simp only [states, if_pos (by omega : i ≤ 128)]; exact storePC i (by omega)
      · have valid : memoryArgumentsValid (zeroStores st i) (zeroStoreAt i) = true := by
          have addr := zero_store_address (zeroStores st i) k i store
            (((facts i (by omega)).2.1 .x29).trans at_.cursor)
          simp only [memoryArgumentsValid, memAccess, zeroStoreAt, addr, accessValid, rangeValid, BitVec.toNat_ofNat,
            Bool.and_eq_true, decide_eq_true_eq]
          unfold leafDest
          constructor <;> simp [MEMORY_BYTES] <;> omega
        have e1 : states i = zeroStores st i := by simp only [states, if_pos (by omega : i ≤ 128)]
        have e2 : states (i+1) = zeroStores st (i+1) := by simp only [states, if_pos (by omega : i+1 ≤ 128)]
        rw [e1, e2]
        unfold zeroStoreAt at valid ⊢
        simp only [ordinaryStep, valid, ite_true]
        rfl
    · by_cases adv : i = 128
      · subst adv
        refine ⟨.base zeroAdvance, zero_fetch 233459 _ zero_decode_advance (by decide) _ ?_, ?_, rfl⟩
        · exact storePC 128 le_rfl
        · show ordinaryStep (zeroStores st 128) (.base zeroAdvance) = some (execInstrBr (zeroStores st 128) zeroAdvance)
          unfold zeroAdvance; rfl
      · have last : i = 129 := by omega
        subst last
        refine ⟨.base zeroBranch, zero_fetch 233460 _ zero_decode_branch (by decide) _ ?_, ?_, rfl⟩
        · show (execInstrBr (zeroStores st 128) zeroAdvance).pc = _
          rw [zero_advance_pc, storePC 128 le_rfl]; rfl
        · show ordinaryStep (execInstrBr (zeroStores st 128) zeroAdvance) (.base zeroBranch) = some (zeroBody st)
          unfold zeroBody zeroBranch; rfl)
  exact run

theorem zero_loop_execute (s0 : MachineState) (step : s0.getReg .x31 = 4096)
    (stop : s0.getReg .x30 = cursorWord (2^17)) :
    ∀ (n k : Nat) (st : MachineState), ZeroAt s0 k st → (0 < n → st.pc = zeroLoopPC) → k + n = 2^17 →
      ∀ fuel, execute packedWideCommitImage (130*n+fuel) st true =
        (do let result ← execute packedWideCommitImage fuel (zeroLoop n st) true
            return result.charge (130*n) 0) := by
  intro n
  induction n with
  | zero =>
    intro k st _ _ _ fuel
    simp [zeroLoop, Execution.charge]
  | succ n ih =>
    intro k st at_ pc sum fuel
    have bound : k < 2^17 := by omega
    have here := pc (by omega)
    rw [show 130*(n+1)+fuel = 130+(130*n+fuel) by omega, zero_body_steps s0 st k bound at_ here]
    have next := zero_body_at s0 st k bound at_ step
    have nextPC : 0 < n → (zeroBody st).pc = zeroLoopPC := by
      intro positive
      rw [zero_body_pc s0 st k bound at_ step stop here, if_neg (by omega)]
    rw [ih (k+1) (zeroBody st) next nextPC (by omega) fuel]
    simp only [zeroLoop, bind_assoc, pure_bind, Execution.charge]
    simp only [show ∀ c, 130 + (130*n+c) = 130*(n+1)+c from fun c => by omega, Nat.zero_add]

theorem zero_loop_post (s0 : MachineState) (step : s0.getReg .x31 = 4096)
    (stop : s0.getReg .x30 = cursorWord (2^17)) :
    ∀ (n k : Nat) (st : MachineState), ZeroAt s0 k st → (0 < n → st.pc = zeroLoopPC) → k + n = 2^17 → 0 < n →
      ZeroAt s0 (2^17) (zeroLoop n st) ∧ (zeroLoop n st).pc = zeroExitPC := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ impossible; omega
  | succ n ih =>
    intro k st at_ pc sum _
    have bound : k < 2^17 := by omega
    have here := pc (by omega)
    have next := zero_body_at s0 st k bound at_ step
    have nextPC := zero_body_pc s0 st k bound at_ step stop here
    by_cases last : n = 0
    · subst last
      have full : k + 1 = 2^17 := by omega
      rw [full] at next
      rw [if_pos full] at nextPC
      exact ⟨next, nextPC⟩
    · exact ih (k+1) (zeroBody st) next (fun _ => by rw [nextPC, if_neg (by omega)]) (by omega) (by omega)

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


theorem lui_mem (t : MachineState) (rd : Reg) (i : BitVec 20) : (execInstrBr t (.LUI rd i)).mem = t.mem := by
  cases rd <;> rfl
theorem lui_pc (t : MachineState) (rd : Reg) (i : BitVec 20) : (execInstrBr t (.LUI rd i)).pc = t.pc + 4 := by
  cases rd <;> rfl
theorem lui_reg (t : MachineState) (rd r : Reg) (i : BitVec 20) (ne : rd ≠ r) :
    (execInstrBr t (.LUI rd i)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]

def zeroSetupAt (s : MachineState) (i : Nat) : MachineState :=
  (zeroSetupOps.take i).foldl execInstrBr (execInstrBr s zeroJump)
def zeroLoopEntry (s : MachineState) : MachineState := zeroSetupAt s 6
def zeroTail (t : MachineState) : MachineState := (parentSetupOps.drop 1).foldl execInstrBr t
def zeroLoopExit (s : MachineState) : MachineState := zeroLoop (2^17) (zeroLoopEntry s)
def zeroA (s : MachineState) : MachineState := execInstrBr (zeroLoopExit s) zeroSource
def zeroB (s : MachineState) : MachineState := execInstrBr (zeroA s) zeroBack
def zeroTailAt (s : MachineState) (i : Nat) : MachineState := ((parentSetupOps.drop 1).take i).foldl execInstrBr (zeroB s)
def zeroEntry (s : MachineState) : MachineState := zeroTail (zeroB s)

def zeroEntryCost : Nat := 17039373

attribute [irreducible] zeroLoop zeroLoopExit

theorem zero_tail_mem (t : MachineState) : (zeroTail t).mem = t.mem := by
  simp only [zeroTail, parentSetupOps, List.drop, List.foldl, sub_mem, addi_mem]

def Kept (r : Reg) : Prop := r ≠ .x29 ∧ r ≠ .x30 ∧ r ≠ .x31

section
variable (s : MachineState) (atLeaves : s.pc = 184608)
  (stride : s.getReg .x19 = 536870912) (stop : s.getReg .x21 = wordAddress (leafDest (2^24)))
include atLeaves stride stop

theorem zero_setup_facts :
    (zeroLoopEntry s).getReg .x29 = cursorWord 0 ∧ (zeroLoopEntry s).getReg .x30 = cursorWord (2^17) ∧
    (zeroLoopEntry s).getReg .x31 = 4096 ∧ (∀ r, Kept r → (zeroLoopEntry s).getReg r = s.getReg r) ∧
    (zeroLoopEntry s).mem = s.mem ∧ (zeroLoopEntry s).pc = zeroLoopPC := by
  unfold zeroLoopEntry zeroSetupAt zeroSetupOps zeroJump
  simp only [List.take, List.foldl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lui_reg _ _ _ _ (by decide), addi_reg _ _ _ _ _ (by decide), addi_reg _ _ _ _ _ (by decide),
      addi_dest _ _ _ _ (by decide), addi_dest _ _ _ _ (by decide), sub_dest _ _ _ _ (by decide), jal_reg, jal_reg,
      stop, stride]
    unfold cursorWord wordAddress leafDest
    rw [show signExtend12 (2047 : BitVec 12) = BitVec.ofNat 64 2047 by decide,
      show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 by decide,
      show (536870912 : Word) = BitVec.ofNat 64 536870912 from rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · rw [lui_reg _ _ _ _ (by decide), addi_dest _ _ _ _ (by decide), addi_dest _ _ _ _ (by decide),
      addi_reg _ _ _ _ _ (by decide), addi_reg _ _ _ _ _ (by decide), sub_reg _ _ _ _ _ (by decide), jal_reg, stop]
    unfold cursorWord wordAddress leafDest
    rw [show signExtend12 (2047 : BitVec 12) = BitVec.ofNat 64 2047 by decide,
      show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 by decide]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (r := .x31) (by decide)]
    decide
  · intro r ⟨n29, n30, n31⟩
    rw [lui_reg _ _ _ _ (Ne.symm n31), addi_reg _ _ _ _ _ (Ne.symm n30), addi_reg _ _ _ _ _ (Ne.symm n30),
      addi_reg _ _ _ _ _ (Ne.symm n29), addi_reg _ _ _ _ _ (Ne.symm n29), sub_reg _ _ _ _ _ (Ne.symm n29), jal_reg]
  · rw [lui_mem, addi_mem, addi_mem, addi_mem, addi_mem, sub_mem, jal_mem]
  · rw [lui_pc, addi_pc, addi_pc, addi_pc, addi_pc, sub_pc, jal_pc, atLeaves]; rfl

theorem zero_loop_exit_post :
    ZeroAt (zeroLoopEntry s) (2^17) (zeroLoopExit s) ∧ (zeroLoopExit s).pc = zeroExitPC := by
  obtain ⟨c29, c30, c31, _, _, pc⟩ := zero_setup_facts s atLeaves stride stop
  have entry : ZeroAt (zeroLoopEntry s) 0 (zeroLoopEntry s) := ⟨c29, fun _ _ => rfl, (zeroed_memory_zero _).symm⟩
  unfold zeroLoopExit
  exact zero_loop_post _ c31 c30 (2^17) 0 _ entry (fun _ => pc) (by omega) (by decide)

theorem zero_entry_mem : (zeroEntry s).mem = zeroedMemory s.mem (2^24) := by
  have post := zero_loop_exit_post s atLeaves stride stop
  have setup := zero_setup_facts s atLeaves stride stop
  unfold zeroEntry zeroB zeroA zeroBack zeroSource
  rw [zero_tail_mem, jal_mem, addi_mem, post.1.mem, setup.2.2.2.2.1]
  rfl

theorem zero_exit_reg (r : Reg) (kept : Kept r) : (zeroLoopExit s).getReg r = s.getReg r := by
  have post := zero_loop_exit_post s atLeaves stride stop
  rw [post.1.regs r kept.1]
  exact (zero_setup_facts s atLeaves stride stop).2.2.2.1 r kept

end

private theorem set_reg_get (t : MachineState) (rd rs : Reg) (value : Word) :
    (t.setReg rd value).getReg rs = if rd = rs ∧ rd ≠ .x0 then value else t.getReg rs := by
  by_cases same : rd = rs
  · subst rs
    by_cases zero : rd = .x0
    · subst rd; rfl
    · simp [zero, MachineState.getReg_setReg_eq]
  · simp [same, MachineState.getReg_setReg_ne]

def AgreeOff29 (t u : MachineState) : Prop := ∀ r, Kept r → t.getReg r = u.getReg r

theorem agree_addi {t u : MachineState} (h : AgreeOff29 t u) (rd a : Reg) (i : BitVec 12) (ha : Kept a) :
    AgreeOff29 (execInstrBr t (.ADDI rd a i)) (execInstrBr u (.ADDI rd a i)) := by
  intro r hr
  simp only [execInstrBr, MachineState.getReg_setPC, set_reg_get, h a ha, h r hr]

theorem agree_sub {t u : MachineState} (h : AgreeOff29 t u) (rd a b : Reg) (ha : Kept a) (hb : Kept b) :
    AgreeOff29 (execInstrBr t (.SUB rd a b)) (execInstrBr u (.SUB rd a b)) := by
  intro r hr
  simp only [execInstrBr, MachineState.getReg_setPC, set_reg_get, h a ha, h b hb, h r hr]

theorem zero_entry_agree (s : MachineState) (atLeaves : s.pc = 184608)
    (stride : s.getReg .x19 = 536870912) (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) :
    AgreeOff29 (zeroEntry s) (parentSetup s 5) := by
  have exit_ : AgreeOff29 (zeroLoopExit s) s := zero_exit_reg s atLeaves stride stop
  have a := agree_addi exit_ .x10 .x21 4032 (by unfold Kept; decide)
  have b : AgreeOff29 (execInstrBr (execInstrBr (zeroLoopExit s) zeroSource) zeroBack)
      (execInstrBr s (.ADDI .x10 .x21 4032)) := by
    intro r hr
    unfold zeroBack zeroSource
    rw [jal_reg]
    exact a r hr
  unfold zeroEntry zeroB zeroA zeroTail parentSetup parentSetupOps
  simp only [List.drop, List.take, List.foldl]
  exact agree_addi (agree_addi (agree_addi (agree_sub b .x12 .x21 .x19 (by unfold Kept; decide) (by unfold Kept; decide))
    .x12 .x12 4064 (by unfold Kept; decide)) .x11 .x0 64 (by unfold Kept; decide)) .x13 .x0 0 (by unfold Kept; decide)

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
  have apc : (zeroA s).pc = BitVec.ofNat 64 (4096+4*233462) := by
    unfold zeroA zeroSource; rw [addi_pc, exitPC]; rfl
  have stepA : ordinaryStep (zeroLoopExit s) (.base zeroSource) = some (zeroA s) := by
    unfold zeroA zeroSource; rfl
  have stepB : ordinaryStep (zeroA s) (.base zeroBack) = some (zeroB s) := by
    unfold zeroB zeroBack; rfl
  have fA := zero_fetch 233461 _ zero_decode_source (by decide) _ exitPC
  have fB := zero_fetch 233462 _ zero_decode_back (by decide) _ apc
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
  have setup := zero_setup_facts s atLeaves stride stop
  have post := zero_loop_exit_post s atLeaves stride stop
  obtain ⟨c29, c30, c31, _, _, lpc⟩ := setup
  have entry : ZeroAt (zeroLoopEntry s) 0 (zeroLoopEntry s) := ⟨c29, fun _ _ => rfl, (zeroed_memory_zero _).symm⟩
  have jpc : (execInstrBr s zeroJump).pc = BitVec.ofNat 64 (4096+4*233325) := by
    unfold zeroJump; rw [jal_pc, atLeaves]; rfl
  have fJ := zero_fetch 45128 _ zero_decode_jump (by decide) s (by rw [atLeaves]; rfl)
  have stepJ : ordinaryStep s (.base zeroJump) = some (execInstrBr s zeroJump) := by unfold zeroJump; rfl
  have setupPC (i : Nat) (h : i < 6) : (zeroSetupAt s i).pc = BitVec.ofNat 64 (4096+4*(233325+i)) := by
    interval_cases i <;> simp only [zeroSetupAt, zeroSetupOps, List.take, List.foldl, addi_pc, sub_pc, jpc] <;> rfl
  have setupStep (i : Nat) (h : i < 6) : ordinaryStep (zeroSetupAt s i) (.base ((zeroSetupOps[i]?).getD .EBREAK)) =
      some (zeroSetupAt s (i+1)) := by
    interval_cases i <;>
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, zeroSetupOps, zeroSetupAt, List.take,
        List.foldl, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, ite_true]
  have setupRun := CommitGolfCandidate.execute_unit_steps packedWideCommitImage 6 (130*2^17+(2+(4+fuel)))
    (zeroSetupAt s) true (by
      intro i inside
      refine ⟨_, zero_fetch (233325+i) _ (zero_decode_setup ⟨i, inside⟩) (by omega) _ (setupPC i inside),
        setupStep i inside, ?_⟩
      interval_cases i <;> rfl)
  have loopRun := zero_loop_execute _ c31 c30 (2^17) 0 (zeroLoopEntry s) entry (fun _ => lpc) (by omega) (2+(4+fuel))
  have exitEq : zeroLoop (2^17) (zeroLoopEntry s) = zeroLoopExit s := by unfold zeroLoopExit; rfl
  have apc : (zeroA s).pc = BitVec.ofNat 64 (4096+4*233462) := by
    unfold zeroA zeroSource; rw [addi_pc, post.2]; rfl
  have bpc : (zeroB s).pc = BitVec.ofNat 64 (4096+4*45129) := by
    unfold zeroB zeroBack; rw [jal_pc, apc]; rfl
  have setup0 : zeroSetupAt s 0 = execInstrBr s zeroJump := rfl
  have setup6 : zeroSetupAt s 6 = zeroLoopEntry s := rfl
  rw [show zeroEntryCost+fuel = (6+(130*2^17+(2+(4+fuel))))+1 by unfold zeroEntryCost; omega,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fJ stepJ, ← setup0, setupRun, setup6]
  simp only [bind_assoc, pure_bind]
  rw [loopRun, exitEq]
  simp only [bind_assoc, pure_bind]
  rw [zero_exit_steps s post.2]
  simp only [bind_assoc, pure_bind]
  rw [zero_tail_steps s bpc]
  simp only [bind_assoc, pure_bind, Execution.charge, instructionCycles, zeroJump, zeroEntryCost, Nat.zero_add]
  have arith : ∀ c : Nat, 1 + (6 + (130 * 2 ^ 17 + (2 + (4 + c)))) = 17039373 + c := fun c => by omega
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
  · rw [agree _ (by unfold Kept; decide)]; exact old.1.source
  · rw [agree _ (by unfold Kept; decide)]; exact old.1.target
  · rw [agree _ (by unfold Kept; decide)]; exact old.1.selector
  · rw [agree _ (by unfold Kept; decide)]; exact old.1.size
  · rw [agree _ (by unfold Kept; decide)]; exact old.1.primitive
  · rw [agree _ (by unfold Kept; decide)]; exact old.1.heap
  · rw [agree _ (by unfold Kept; decide)]; exact old.2.2

end TwoPermutationPrototype.RV64
