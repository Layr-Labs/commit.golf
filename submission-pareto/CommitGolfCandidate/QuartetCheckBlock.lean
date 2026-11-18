import CommitGolfCandidate.QuartetCheckBlockCopy
import CommitGolfCandidate.TwoPermutationPackedLowerRecursion
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationPackedCapBytes
import CommitGolfCandidate.TwoPermutationPackedInputFrame
import CommitGolfCandidate.TwoPermutationCheckerLowerRun
import CommitGolfCandidate.QuadReplay
import CommitGolfCandidate.QuartetRVLeafFields

/-! The whole quartet block, from word 58 to the lower-loop head at word 63: the four slot fills at
`13312+72`, the one permutation call over the 72 zero bytes and four digests with its output at
`x23-168` for an even group (the node, reply bytes `168..200`, lands at 12288) or at `x23` for an odd
group (reply bytes `0..32`), the heap index `2^22 + ⌊i/4⌋`, and the restored compression setup. -/

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_recorded_bind check_recorded_map)

set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-- What the quartet block reads at word 58. -/
structure QuartetEntry (ordinal : Nat) (index : Index) (s : MachineState) : Prop where
  pc : s.pc = 0x10e8
  node : s.getReg .x6 = BitVec.ofNat 64 index.val
  proof : s.getReg .x21 = BitVec.ofNat 64 (checkProofByte ordinal)
  heapBase : s.getReg .x20 = BitVec.ofNat 64 (LENGTH/4)
  digest : s.getReg .x23 = 12288
  pair : s.getReg .x24 = 12544
  selector : s.getReg .x5 = 0
  syscallBytes : s.getReg .x11 = 200
  syscallSelector : s.getReg .x13 = 1
  zeroPrefix : ∀ w, 1664 ≤ w → w < 1673 → memoryView s w = 0
  room : checkProofByte ordinal + 534 ≤ MEMORY_BYTES

theorem q_head_valid₁ : 1 ≤ 1 ∧ 1 ≤ 3 := by decide
theorem q_head_valid₂ : 1 ≤ 2 ∧ 2 ≤ 3 := by decide
theorem q_head_valid₃ : 1 ≤ 3 ∧ 3 ≤ 3 := by decide

def qS1 (s : MachineState) := straight qEnterCode s 2
def qS2 (s : MachineState) := straight qSlotCode (qS1 s) 6
def qS3 (s : MachineState) := qLeafCopied (qS2 s)
def qHead (j : Nat) (s : MachineState) := straight (qHeadCode j) s 3
def qCopy (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) (s : MachineState) := qSiblingCopied j valid (qHead j s)
def qFill (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) (s : MachineState) := straight qAdvanceCode (qCopy j valid s) 1
def qF1 (s : MachineState) := qFill 1 q_head_valid₁ (qS3 s)
def qF2 (s : MachineState) := qFill 2 q_head_valid₂ (qF1 s)
def qF3 (s : MachineState) := qFill 3 q_head_valid₃ (qF2 s)
/-- The state at word 569, before the parity branch. -/
def qP (s : MachineState) := straight qParityCode (qF3 s) 3
def qB (s : MachineState) := qBranch (qP s)
/-- Whether the quartet's group `⌊i/4⌋` is odd, as the machine reads it from `x6` at the entry. -/
def qOdd (s : MachineState) : Bool := s.getReg .x6 &&& 4 != 0
def qCallState (s : MachineState) : MachineState := if qOdd s then qB s else straight qEvenCode (qB s) 1
def qCallSteps (s : MachineState) : Nat := if qOdd s then 128 else 129
/-- The call's output word: `x23` for an odd group, `x23-168` for an even group. -/
def qOutWord (s : MachineState) : Nat := if qOdd s then 1536 else 1515
def qInput (s : MachineState) : Block := packBuffer (window (memoryView (qCallState s)) 1664)
def qQuartet (s : MachineState) : BitVec 1024 := readBuffer (qCallState s) 13384 128
def qReplyState (s : MachineState) (reply : Block) := writeBits (qCallState s) (wordAddress (qOutWord s)) reply
def qFinal (s : MachineState) (reply : Block) :=
  straight qLowerCode (straight qExitCode (qReturn (qReplyState s reply)) 3) 3

/-! ### The group parity -/

theorem group_parity_bit (i : Nat) : (i &&& 4 = 0) ↔ i / 4 % 2 = 0 := by
  have bit : i.testBit 2 = decide (i / 4 % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  have four : (4 : Nat).testBit 2 = true := by decide
  constructor
  · intro zero
    have t := congrArg (fun n => n.testBit 2) zero
    simp only [Nat.testBit_and, four, Bool.and_true, bit] at t
    have : ¬ (i / 4 % 2 = 1) := by simpa using t
    omega
  · intro even
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and]
    by_cases k2 : k = 2
    · subst k2
      rw [bit]
      simp [show ¬ (i / 4 % 2 = 1) by omega]
    · have off : (4 : Nat).testBit k = false := by
        rw [show (4 : Nat) = 2^2 from rfl, Nat.testBit_two_pow]
        simpa using (Ne.symm k2)
      rw [off, Bool.and_false]
      simp

theorem q_odd_index {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    qOdd s = decide (index.val / 4 % 2 = 1) := by
  have bound : index.val < 16777216 := index.isLt
  have small : index.val &&& 4 ≤ 4 := Nat.and_le_right
  have word : s.getReg .x6 &&& 4 = BitVec.ofNat 64 (index.val &&& 4) := by
    rw [entry.node, BitVec.ofNat_and] <;> rfl
  have zero : (s.getReg .x6 &&& 4 = 0) ↔ index.val / 4 % 2 = 0 := by
    rw [word, ← group_parity_bit]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show index.val &&& 4 < 2^64 by omega)] at this
      exact this
    · intro h
      simp [h]
  unfold qOdd
  by_cases even : index.val / 4 % 2 = 0
  · have z := zero.mpr even
    rw [z]
    simp [show ¬ (index.val / 4 % 2 = 1) by omega]
  · have nz : ¬ (s.getReg .x6 &&& 4 = 0) := fun h => even (zero.mp h)
    have odd : index.val / 4 % 2 = 1 := by omega
    rw [show (s.getReg .x6 &&& 4 != 0) = true by simpa using nz]
    simp [odd]


/-! ### Register bookkeeping -/

private theorem slot_selector (index : Index) :
    (BitVec.ofNat 64 index.val &&& 3) = BitVec.ofNat 64 (index.val % 4) :=
  QuartetRV.low_selector index

/-- The slot base computed by the head of slot `j` from the low two index bits. -/
theorem slot_target (r j : Nat) (hr : r < 4) (hj : j < 4) :
    BitVec.ofNat 64 13312 + ((BitVec.ofNat 64 r ^^^ (BitVec.ofNat 12 j).signExtend 64) <<< 5) =
      BitVec.ofNat 64 (13312 + 32*(r ^^^ j)) := by
  interval_cases r <;> interval_cases j <;> decide

theorem slot_target_zero (r : Nat) (hr : r < 4) :
    BitVec.ofNat 64 13312 + ((BitVec.ofNat 64 r ^^^ 0) <<< 5) = BitVec.ofNat 64 (13312 + 32*r) := by
  interval_cases r <;> decide

structure QuartetRegs (ordinal : Nat) (index : Index) (entry state : MachineState) (pc : Nat) (proofOffset : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*pc)
  base : state.getReg .x10 = BitVec.ofNat 64 13312
  selector : state.getReg .x7 = BitVec.ofNat 64 (index.val % 4)
  proof : state.getReg .x21 = BitVec.ofNat 64 (checkProofByte ordinal + proofOffset)
  kept : ∀ r, r ≠ .x10 → r ≠ .x7 → r ≠ .x28 → r ≠ .x31 → r ≠ .x21 → state.getReg r = entry.getReg r

theorem q_s2_regs {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    QuartetRegs ordinal index s (qS2 s) 373 16 ∧
      (qS2 s).getReg .x28 = BitVec.ofNat 64 (13312 + 32*(index.val % 4)) ∧ (qS2 s).mem = s.mem := by
  obtain ⟨p1, m1, x21, k1⟩ := q_enter_post s entry.pc
  obtain ⟨p2, m2, x10, x7, x28, k2⟩ := q_slot_post (qS1 s)
  have node : (qS1 s).getReg .x6 = BitVec.ofNat 64 index.val := (k1 .x6 (by decide)).trans entry.node
  refine ⟨⟨?_, x10, ?_, ?_, ?_⟩, ?_, ?_⟩
  · change (qS2 s).pc = _
    rw [show qS2 s = straight qSlotCode (qS1 s) 6 from rfl, p2]
    change (straight qEnterCode s 2).pc + 24 = _
    rw [p1]; rfl
  · change (straight qSlotCode (qS1 s) 6).getReg .x7 = _
    rw [x7, node, slot_selector]
  · change (straight qSlotCode (qS1 s) 6).getReg .x21 = _
    rw [k2 .x21 (by decide) (by decide) (by decide)]
    change (straight qEnterCode s 2).getReg .x21 = _
    rw [x21, entry.proof]
    change BitVec.ofNat 64 (checkProofByte ordinal) + BitVec.ofNat 64 16 = _
    rw [← BitVec.ofNat_add]
  · intro r a b c d e
    change (straight qSlotCode (qS1 s) 6).getReg r = _
    rw [k2 r a b c]
    exact k1 r e
  · change (straight qSlotCode (qS1 s) 6).getReg .x28 = _
    rw [x28, node, slot_selector]
    exact slot_target_zero _ (Nat.mod_lt _ (by decide))
  · change (straight qSlotCode (qS1 s) 6).mem = _
    rw [m2]; exact m1


theorem check_proof_even (ordinal : Nat) : checkProofByte ordinal % 2 = 0 := by
  unfold checkProofByte; omega

theorem q_s3_regs {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    QuartetRegs ordinal index s (qS3 s) (qHeadStart 1) 16 := by
  obtain ⟨⟨pc, base, sel, proof, kept⟩, _, _⟩ := q_s2_regs entry
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (qLeafCopied (qS2 s)).pc = _
    rw [q_leaf_copied_pc, pc]; rfl
  · exact (q_leaf_copied_register _ _ (by decide)).trans base
  · exact (q_leaf_copied_register _ _ (by decide)).trans sel
  · exact (q_leaf_copied_register _ _ (by decide)).trans proof
  · intro r a b c d e
    exact (q_leaf_copied_register _ _ d).trans (kept r a b c d e)

theorem q_head_regs (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) {ordinal : Nat} {index : Index} {s state : MachineState}
    (pre : QuartetRegs ordinal index s state (qHeadStart j) (16+32*(j-1))) :
    (qHead j state).pc = BitVec.ofNat 64 (4096+4*(qHeadStart j+3)) ∧
      (qHead j state).getReg .x28 = BitVec.ofNat 64 (13312 + 32*((index.val % 4) ^^^ j)) ∧
      ∀ r, r ≠ .x28 → (qHead j state).getReg r = state.getReg r := by
  obtain ⟨pc, mem, x28, kept⟩ := q_head_post j state
  refine ⟨?_, ?_, kept⟩
  · change (straight (qHeadCode j) state 3).pc = _
    rw [pc, pre.pc]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 12 = _
    rw [← BitVec.ofNat_add]
    congr 1
  · change (straight (qHeadCode j) state 3).getReg .x28 = _
    rw [x28, pre.base, pre.selector]
    exact slot_target _ _ (Nat.mod_lt _ (by decide)) (by omega)

theorem q_copy_ready (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) {ordinal : Nat} {index : Index} {s state : MachineState}
    (entry : QuartetEntry ordinal index s)
    (pre : QuartetRegs ordinal index s state (qHeadStart j) (16+32*(j-1))) :
    QuartetCheckCopy.CopyReady (qSiblingCode j valid) (qHead j state)
      (checkProofByte ordinal + (16+32*(j-1))) (13384 + 32*((index.val % 4) ^^^ j)) 0 := by
  obtain ⟨pc, x28, kept⟩ := q_head_regs j valid pre
  have room := entry.room
  have bound : (index.val % 4) ^^^ j < 4 := Nat.xor_lt_two_pow (n := 2) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (qHead j state).pc = BitVec.ofNat 64 (4096+4*(qHeadStart j+3+2*0))
    rw [pc]
  · change (qHead j state).getReg .x21 = _
    rw [kept .x21 (by decide), pre.proof]
  · change (qHead j state).getReg .x28 + BitVec.ofNat 64 72 = _
    rw [x28, ← BitVec.ofNat_add]
    congr 1
    omega
  · change checkProofByte ordinal + (16+32*(j-1)) + 2*16 ≤ MEMORY_BYTES
    omega
  · change 13384 + 32*((index.val % 4) ^^^ j) + 2*16 ≤ MEMORY_BYTES
    unfold MEMORY_BYTES; omega
  · have := check_proof_even ordinal; omega
  · omega

theorem q_fill_regs (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) {ordinal : Nat} {index : Index} {s state : MachineState}
    (entry : QuartetEntry ordinal index s)
    (pre : QuartetRegs ordinal index s state (qHeadStart j) (16+32*(j-1))) :
    QuartetRegs ordinal index s (qFill j valid state) (qHeadStart j+36) (16+32*j) := by
  obtain ⟨hpc, x28, hkept⟩ := q_head_regs j valid pre
  have ready := q_copy_ready j valid entry pre
  obtain ⟨apc, _, ax21, akept⟩ := q_advance_post (qCopy j valid state)
  have cpc : (qCopy j valid state).pc = BitVec.ofNat 64 (4096+4*(qHeadStart j+35)) := by
    have := QuartetCheckCopy.copy_field_pc _ _ _ _ ready
    simpa [qCopy, qSiblingCopied, qSiblingCode] using this
  have ckept (r : Reg) (h : r ≠ .x31) : (qCopy j valid state).getReg r = (qHead j state).getReg r :=
    QuartetCheckCopy.copy_field_register _ _ r h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (straight qAdvanceCode (qCopy j valid state) 1).pc = _
    rw [apc, cpc]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]
    congr 1
  · change (straight qAdvanceCode (qCopy j valid state) 1).getReg .x10 = _
    rw [akept .x10 (by decide), ckept .x10 (by decide), hkept .x10 (by decide), pre.base]
  · change (straight qAdvanceCode (qCopy j valid state) 1).getReg .x7 = _
    rw [akept .x7 (by decide), ckept .x7 (by decide), hkept .x7 (by decide), pre.selector]
  · change (straight qAdvanceCode (qCopy j valid state) 1).getReg .x21 = _
    rw [ax21, ckept .x21 (by decide), hkept .x21 (by decide), pre.proof]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · intro r a b c d e
    change (straight qAdvanceCode (qCopy j valid state) 1).getReg r = _
    rw [akept r e, ckept r d, hkept r c]
    exact pre.kept r a b c d e

theorem q_f3_regs {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    QuartetRegs ordinal index s (qF3 s) 489 112 := by
  have r1 := q_fill_regs 1 q_head_valid₁ entry (q_s3_regs entry)
  have r2 := q_fill_regs 2 q_head_valid₂ entry r1
  exact q_fill_regs 3 q_head_valid₃ entry r2


theorem q_access (a : Nat) (aligned : a % 8 = 0) (bounded : a + 8 ≤ 2^36) :
    accessValid (BitVec.ofNat 64 a) 8 = true := by
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a < 2^64),
    Bool.and_eq_true, decide_eq_true_eq, MEMORY_BYTES]
  omega

theorem q_s2_hop {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    GroupHop s (qS3 s) 16 := by
  obtain ⟨p1, _, _, _⟩ := q_enter_post s entry.pc
  have h1 := execute_q_enter s entry.pc
  have h2 := execute_q_slot (qS1 s) p1
  obtain ⟨⟨pc2, _, _, _, kept2⟩, x28, _⟩ := q_s2_regs entry
  have x23 : (qS2 s).getReg .x23 = 12288 :=
    (kept2 .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans entry.digest
  have bound : index.val % 4 < 4 := Nat.mod_lt _ (by decide)
  have h3 := execute_q_leaf_copy (qS2 s) pc2
    (fun j => by
      rw [x23]
      change accessValid (BitVec.ofNat 64 12288 + BitVec.ofNat 64 (8*j.val)) 8 = true
      rw [← BitVec.ofNat_add]
      exact q_access _ (by omega) (by have := j.isLt; omega))
    (fun j => by
      rw [x28, ← BitVec.ofNat_add]
      exact q_access _ (by omega) (by have := j.isLt; omega))
  exact (h1.thenDo h2).thenDo h3

theorem q_fill_hop (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) {ordinal : Nat} {index : Index} {s state : MachineState}
    (entry : QuartetEntry ordinal index s)
    (pre : QuartetRegs ordinal index s state (qHeadStart j) (16+32*(j-1))) :
    GroupHop state (qFill j valid state) 36 := by
  have h1 := execute_q_head j valid state pre.pc
  have ready := q_copy_ready j valid entry pre
  have h2 : GroupHop (qHead j state) (qCopy j valid state) 32 := by
    intro fuel
    have := QuartetCheckCopy.copy_field_execute _ _ _ _ ready fuel false
    simpa [qCopy, qSiblingCopied, qSiblingCode] using this
  have cpc : (qCopy j valid state).pc = BitVec.ofNat 64 (4096+4*(qHeadStart j+35)) := by
    have := QuartetCheckCopy.copy_field_pc _ _ _ _ ready
    simpa [qCopy, qSiblingCopied, qSiblingCode] using this
  have h3 := execute_q_advance j valid (qCopy j valid state) cpc
  exact (h1.thenDo h2).thenDo h3

theorem q_f3_hop {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    GroupHop s (qF3 s) 124 := by
  have r3 := q_s3_regs entry
  have r1 := q_fill_regs 1 q_head_valid₁ entry r3
  have r2 := q_fill_regs 2 q_head_valid₂ entry r1
  have h0 := q_s2_hop entry
  have h1 := q_fill_hop 1 q_head_valid₁ entry r3
  have h2 := q_fill_hop 2 q_head_valid₂ entry r1
  have h3 := q_fill_hop 3 q_head_valid₃ entry r2
  exact ((h0.thenDo h1).thenDo h2).thenDo h3

/-! ### The parity block -/

theorem q_p_regs {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    (qP s).pc = BitVec.ofNat 64 (4096+4*569) ∧ (qP s).mem = (qF3 s).mem ∧
      (qP s).getReg .x28 = s.getReg .x6 &&& 4 ∧ (qP s).getReg .x12 = 12288 ∧
      ∀ r, r ≠ .x28 → r ≠ .x12 → (qP s).getReg r = (qF3 s).getReg r := by
  have f3 := q_f3_regs entry
  obtain ⟨pc, mem, x28, x12, kept⟩ := q_parity_post (qF3 s) f3.pc
  refine ⟨pc, mem, ?_, ?_, kept⟩
  · rw [show qP s = straight qParityCode (qF3 s) 3 from rfl, x28,
      f3.kept .x6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [show qP s = straight qParityCode (qF3 s) 3 from rfl, x12,
      f3.kept .x23 (by decide) (by decide) (by decide) (by decide) (by decide), entry.digest]

theorem q_odd_branch {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    (qP s).getReg .x28 = 0 ↔ qOdd s = false := by
  rw [(q_p_regs entry).2.2.1]
  unfold qOdd
  constructor
  · intro zero; rw [zero]; rfl
  · intro odd
    simpa using odd

theorem q_call_hop {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    GroupHop s (qCallState s) (qCallSteps s) := by
  have h0 := q_f3_hop entry
  obtain ⟨ppc, _, _, _, _⟩ := q_p_regs entry
  have h1 := execute_q_parity (qF3 s) (q_f3_regs entry).pc
  have h2 := execute_q_branch (qP s) ppc
  obtain ⟨bpc, _, _⟩ := q_branch_post (qP s) ppc
  have h12 := (h0.thenDo h1).thenDo h2
  cases odd : qOdd s
  · have zero : (qP s).getReg .x28 = 0 := (q_odd_branch entry).mpr odd
    rw [if_pos zero] at bpc
    have h3 := execute_q_even (qB s) bpc
    rw [show qCallState s = straight qEvenCode (qB s) 1 by simp [qCallState, odd],
      show qCallSteps s = 124+3+1+1 by simp [qCallSteps, odd]]
    exact h12.thenDo h3
  · rw [show qCallState s = qB s by simp [qCallState, odd],
      show qCallSteps s = 124+3+1 by simp [qCallSteps, odd]]
    exact h12

theorem q_call_regs {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    (qCallState s).pc = BitVec.ofNat 64 (4096+4*571) ∧
      (qCallState s).getReg .x10 = wordAddress 1664 ∧ (qCallState s).getReg .x12 = wordAddress (qOutWord s) ∧
      (qCallState s).getReg .x5 = 0 ∧ (qCallState s).getReg .x11 = 200 ∧ (qCallState s).getReg .x13 = 1 ∧
      (qCallState s).getReg .x21 = BitVec.ofNat 64 (checkProofByte ordinal + 112) ∧
      (qCallState s).mem = (qF3 s).mem ∧
      ∀ r, r ≠ .x10 → r ≠ .x7 → r ≠ .x28 → r ≠ .x31 → r ≠ .x21 → r ≠ .x12 →
        (qCallState s).getReg r = s.getReg r := by
  have f3 := q_f3_regs entry
  obtain ⟨ppc, pmem, _, px12, pkept⟩ := q_p_regs entry
  obtain ⟨bpc, bmem, bregs⟩ := q_branch_post (qP s) ppc
  -- registers of the branch state
  have bkeep (r : Reg) (a : r ≠ .x10) (b : r ≠ .x7) (c : r ≠ .x28) (d : r ≠ .x31) (e : r ≠ .x21) (f : r ≠ .x12) :
      (qB s).getReg r = s.getReg r :=
    (bregs r).trans ((pkept r c f).trans (f3.kept r a b c d e))
  have b10 : (qB s).getReg .x10 = wordAddress 1664 :=
    (bregs .x10).trans ((pkept .x10 (by decide) (by decide)).trans f3.base)
  have b21 : (qB s).getReg .x21 = BitVec.ofNat 64 (checkProofByte ordinal + 112) :=
    (bregs .x21).trans ((pkept .x21 (by decide) (by decide)).trans f3.proof)
  have b5 := (bkeep .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans entry.selector
  have b11 := (bkeep .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    entry.syscallBytes
  have b13 := (bkeep .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    entry.syscallSelector
  have b23 := (bkeep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    entry.digest
  have bmem' : (qB s).mem = (qF3 s).mem := bmem.trans pmem
  cases odd : qOdd s
  · have zero : (qP s).getReg .x28 = 0 := (q_odd_branch entry).mpr odd
    rw [if_pos zero] at bpc
    obtain ⟨epc, emem, ex12, ekept⟩ := q_even_post (qB s)
    have state : qCallState s = straight qEvenCode (qB s) 1 := by simp [qCallState, odd]
    have out : qOutWord s = 1515 := by simp [qOutWord, odd]
    rw [state, out]
    refine ⟨?_, (ekept .x10 (by decide)).trans b10, ?_, (ekept .x5 (by decide)).trans b5,
      (ekept .x11 (by decide)).trans b11, (ekept .x13 (by decide)).trans b13, (ekept .x21 (by decide)).trans b21,
      emem.trans bmem', fun r a b c d e f => (ekept r f).trans (bkeep r a b c d e f)⟩
    · rw [epc, show (qB s).pc = BitVec.ofNat 64 (4096+4*570) from bpc]; decide
    · rw [ex12, b23]; decide
  · have nonzero : (qP s).getReg .x28 ≠ 0 := fun h => by
      have := (q_odd_branch entry).mp h
      rw [odd] at this
      exact Bool.noConfusion this
    rw [if_neg nonzero] at bpc
    have state : qCallState s = qB s := by simp [qCallState, odd]
    have out : qOutWord s = 1536 := by simp [qOutWord, odd]
    rw [state, out]
    exact ⟨bpc, b10, (bregs .x12).trans px12, b5, b11, b13, b21, bmem', bkeep⟩

theorem q_reply_pc {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s)
    (reply : Block) : (qReplyState s reply).pc = BitVec.ofNat 64 (4096+4*572) := by
  unfold qReplyState writeBits
  change (qCallState s).pc + 4 = _
  rw [(q_call_regs entry).1]; rfl

theorem q_tail_hop {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s)
    (reply : Block) : GroupHop (qReplyState s reply) (qFinal s reply) 7 := by
  have pc := q_reply_pc entry reply
  have h0 := execute_q_return (qReplyState s reply) pc
  have rpc := (q_return_post (qReplyState s reply)).1
  have h1 := execute_q_exit (qReturn (qReplyState s reply)) rpc
  have h2 := execute_q_lower (straight qExitCode (qReturn (qReplyState s reply)) 3) (q_exit_post _ rpc).1
  exact (h0.thenDo h1).thenDo h2

theorem q_out_bound (s : MachineState) : qOutWord s + 25 ≤ 2^33 := by
  unfold qOutWord; split <;> decide

attribute [local irreducible] execute in
theorem q_execute {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s)
    (fuel : Nat) :
    execute packedImage (qCallSteps s + 1 + 7 + fuel) s false = (do
      let reply ← World.query (.inr (.inr (.inl (qInput s))))
      let result ← execute packedImage fuel (qFinal s reply) false
      return result.charge (qCallSteps s + 8 + 7) 1) := by
  obtain ⟨pc, x10, x12, x5, x11, x13, _, _, _⟩ := q_call_regs entry
  have call := execute_permutation_call packedImage (7+fuel) (qCallState s) false 1664 (qOutWord s)
    (by decide) (q_out_bound s) x10 x12 x5 x11 x13 (q_call_fetch _ pc)
  rw [show qCallSteps s + 1 + 7 + fuel = qCallSteps s + ((7+fuel)+1) by omega, q_call_hop entry, call]
  simp only [bind_assoc, pure_bind]
  unfold qInput
  apply bind_congr_of_forall_mem_support
  intro reply _
  change Block at reply
  rw [show writeBits (qCallState s) (wordAddress (qOutWord s)) reply = qReplyState s reply from rfl,
    q_tail_hop entry reply fuel]
  simp [Execution.charge, ← Nat.add_assoc]


/-! ### Memory: the four slots, the zero prefix, and the frame -/

private theorem distinct_addresses (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (ne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro same
  have := congrArg BitVec.toNat same
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact ne this

/-- A byte-level frame outside a 32-byte target gives a word-level frame outside its words. -/
private theorem slot_word_frame (before after : MachineState) (target : Nat) (aligned : target % 8 = 0)
    (fits : target + 32 ≤ 2^36)
    (frame : ∀ q : Word, (∀ i<32, q≠BitVec.ofNat 64 (target+i)) → after.getByte q=before.getByte q)
    (w : Nat) (bounded : w < 2^33) (outside : w < target/8 ∨ target/8 + 4 ≤ w) :
    memoryView after w = memoryView before w := by
  apply word_eq_of_byte_frame
  intro i small
  apply frame
  intro i' inside
  exact distinct_addresses _ _ (by omega) (by omega) (by omega)

private theorem copy_read_bytes (before after : MachineState) (source target : Nat)
    (copied : ∀ i<32, after.getByte (BitVec.ofNat 64 (target+i))=before.getByte (BitVec.ofNat 64 (source+i))) :
    readBuffer after target 32 = readBuffer before source 32 := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat _)
  apply Finset.sum_congr rfl
  intro i inside
  rw [copied i (Finset.mem_range.mp inside)]

theorem q_fill_memory (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) {ordinal : Nat} {index : Index} {s state : MachineState}
    (entry : QuartetEntry ordinal index s)
    (pre : QuartetRegs ordinal index s state (qHeadStart j) (16+32*(j-1))) :
    readBuffer (qFill j valid state) (13384 + 32*((index.val % 4) ^^^ j)) 32 =
        readBuffer state (checkProofByte ordinal + (16+32*(j-1))) 32 ∧
      ∀ w < 2^33, (w < 1673 + 4*((index.val % 4) ^^^ j) ∨ 1673 + 4*((index.val % 4) ^^^ j) + 4 ≤ w) →
        memoryView (qFill j valid state) w = memoryView state w := by
  have ready := q_copy_ready j valid entry pre
  have room := entry.room
  have bound : (index.val % 4) ^^^ j < 4 := Nat.xor_lt_two_pow (n := 2) (by omega) (by omega)
  obtain ⟨copied, frame⟩ := q_sibling_bytes j valid (qHead j state) _ _ ready (by
    unfold checkProofByte; omega)
  have headMem : (qHead j state).mem = state.mem := (q_head_post j state).2.1
  have advMem : (qFill j valid state).mem = (qCopy j valid state).mem := (q_advance_post (qCopy j valid state)).2.1
  have sameAfter (a : Nat) (n : Nat) : readBuffer (qFill j valid state) a n = readBuffer (qCopy j valid state) a n :=
    read_buffer_memory_congr _ _ advMem a n
  constructor
  · rw [sameAfter]
    exact (copy_read_bytes _ _ _ _ copied).trans (read_buffer_memory_congr _ _ headMem _ _)
  · intro w bounded outside
    have viewAfter : memoryView (qFill j valid state) w = memoryView (qCopy j valid state) w := by
      unfold memoryView; simp only [MachineState.getMem, advMem]
    have viewHead : memoryView (qHead j state) w = memoryView state w := by
      unfold memoryView; simp only [MachineState.getMem, headMem]
    rw [viewAfter, ← viewHead]
    exact slot_word_frame _ _ _ (by omega) (by unfold MEMORY_BYTES at room; omega) frame w bounded (by omega)

theorem q_leaf_memory {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    readBuffer (qS3 s) (13384 + 32*(index.val % 4)) 32 = readBuffer s 12288 32 ∧
      ∀ w < 2^33, (w < 1673 + 4*(index.val % 4) ∨ 1673 + 4*(index.val % 4) + 4 ≤ w) →
        memoryView (qS3 s) w = memoryView s w := by
  obtain ⟨⟨_, _, _, _, kept⟩, x28, mem2⟩ := q_s2_regs entry
  have x23 : (qS2 s).getReg .x23 = BitVec.ofNat 64 12288 :=
    (kept .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans entry.digest
  have r := index.val % 4
  have bound : index.val % 4 < 4 := Nat.mod_lt _ (by decide)
  have dest : (qS2 s).getReg .x28 + 72#64 = BitVec.ofNat 64 (13384 + 32*(index.val % 4)) := by
    rw [x28]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 72 = _; rw [← BitVec.ofNat_add]; congr 1; omega
  have separate : ∀ i j : Fin 4, (qS2 s).getReg .x23+BitVec.ofNat 64 (8*i.val) ≠
      ((qS2 s).getReg .x28+72#64)+BitVec.ofNat 64 (8*j.val) := by
    intro i j
    rw [x23, dest, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact distinct_addresses _ _ (by omega) (by omega) (by omega)
  have mem3 := q_leaf_copied_memory (qS2 s) separate
  rw [x23, dest] at mem3
  constructor
  · have bytes := Opening.four_word_store_bytes (qS2 s) 12288 (13384 + 32*(index.val % 4))
      (by decide) (by omega) (by unfold MEMORY_BYTES; omega)
    calc readBuffer (qS3 s) (13384 + 32*(index.val % 4)) 32
        = readBuffer (Opening.fourWordStore (qS2 s) (BitVec.ofNat 64 12288)
            (BitVec.ofNat 64 (13384 + 32*(index.val % 4)))) (13384 + 32*(index.val % 4)) 32 :=
          read_buffer_memory_congr _ _ mem3 _ _
      _ = readBuffer (qS2 s) 12288 32 := bytes
      _ = readBuffer s 12288 32 := read_buffer_memory_congr _ _ mem2 _ _
  · intro w bounded outside
    have words : memoryView (qS3 s) w = (Opening.fourWordStore (qS2 s) (BitVec.ofNat 64 12288)
        (BitVec.ofNat 64 (13384 + 32*(index.val % 4)))).getMem (wordAddress w) := by
      change (qLeafCopied (qS2 s)).getMem (wordAddress w) = _
      simp only [MachineState.getMem, mem3]
    rw [words, Opening.four_word_store_outside]
    · unfold memoryView; simp only [MachineState.getMem, mem2]
    · intro i
      rw [← BitVec.ofNat_add]
      unfold wordAddress
      exact distinct_addresses _ _ (by omega) (by have := i.isLt; omega) (by have := i.isLt; omega)


private theorem xor_small (r j : Nat) (hr : r < 4) (hj : j < 4) : r ^^^ j < 4 :=
  Nat.xor_lt_two_pow (n := 2) (by omega) (by omega)

private theorem xor_distinct : ∀ r < 4, ∀ j < 4, ∀ j' < 4, j ≠ j' → r ^^^ j ≠ r ^^^ j' := by decide

private theorem view_of_mem {a b : MachineState} (same : a.mem = b.mem) (w : Nat) :
    memoryView a w = memoryView b w := by
  unfold memoryView; simp only [MachineState.getMem, same]

theorem q_call_memory {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    readBuffer (qCallState s) (13384+32*(index.val % 4)) 32 = readBuffer s 12288 32 ∧
      (∀ j, 1 ≤ j → j ≤ 3 → readBuffer (qCallState s) (13384+32*((index.val % 4) ^^^ j)) 32 =
        readBuffer s (checkProofByte ordinal + (16+32*(j-1))) 32) ∧
      (∀ w < 2^33, (w < 1673 ∨ 1689 ≤ w) → memoryView (qCallState s) w = memoryView s w) := by
  have r3 := q_s3_regs entry
  have r1 := q_fill_regs 1 q_head_valid₁ entry r3
  have r2 := q_fill_regs 2 q_head_valid₂ entry r1
  obtain ⟨leafRead, leafFrame⟩ := q_leaf_memory entry
  obtain ⟨read1, frame1⟩ := q_fill_memory 1 q_head_valid₁ entry r3
  obtain ⟨read2, frame2⟩ := q_fill_memory 2 q_head_valid₂ entry r1
  obtain ⟨read3, frame3⟩ := q_fill_memory 3 q_head_valid₃ entry r2
  have callMem : (qCallState s).mem = (qF3 s).mem := (q_call_regs entry).2.2.2.2.2.2.2.1
  have room := entry.room
  have card : checkProofByte ordinal ≥ 13824430176 := by unfold checkProofByte; omega
  have hr : index.val % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize index.val % 4 = r at hr leafRead leafFrame read1 frame1 read2 frame2 read3 frame3 ⊢
  have x1 := xor_small r 1 hr (by decide)
  have x2 := xor_small r 2 hr (by decide)
  have x3 := xor_small r 3 hr (by decide)
  have d01 := xor_distinct r hr 0 (by decide) 1 (by decide) (by decide)
  have d02 := xor_distinct r hr 0 (by decide) 2 (by decide) (by decide)
  have d03 := xor_distinct r hr 0 (by decide) 3 (by decide) (by decide)
  have d12 := xor_distinct r hr 1 (by decide) 2 (by decide) (by decide)
  have d13 := xor_distinct r hr 1 (by decide) 3 (by decide) (by decide)
  have d23 := xor_distinct r hr 2 (by decide) 3 (by decide) (by decide)
  simp only [Nat.xor_zero] at d01 d02 d03
  -- every word outside the slot area survives all four fills
  have survive (w : Nat) (bounded : w < 2^33)
      (o1 : w < 1673 + 4*(r ^^^ 1) ∨ 1673 + 4*(r ^^^ 1) + 4 ≤ w)
      (o2 : w < 1673 + 4*(r ^^^ 2) ∨ 1673 + 4*(r ^^^ 2) + 4 ≤ w)
      (o3 : w < 1673 + 4*(r ^^^ 3) ∨ 1673 + 4*(r ^^^ 3) + 4 ≤ w) :
      memoryView (qCallState s) w = memoryView (qS3 s) w :=
    (view_of_mem callMem w).trans ((frame3 w bounded o3).trans ((frame2 w bounded o2).trans (frame1 w bounded o1)))
  refine ⟨?_, ?_, ?_⟩
  · rw [show 13384+32*r = 8*(1673+4*r) by omega, Checker.aligned_digest_frame (qS3 s) (qCallState s) (1673+4*r) ?_]
    · rw [show 8*(1673+4*r) = 13384+32*r by omega]; exact leafRead
    · intro o small
      apply survive _ (by omega) <;> omega
  · intro j lo hi
    -- the proof bytes were untouched before the copy that read them
    have proofSafe (a : MachineState) (frameA : ∀ w < 2^33, w < 1673 ∨ 1689 ≤ w → memoryView a w = memoryView s w) :
        readBuffer a (checkProofByte ordinal + (16+32*(j-1))) 32 = readBuffer s (checkProofByte ordinal + (16+32*(j-1))) 32 := by
      apply buffer_byte_frame
      intro i small
      unfold MEMORY_BYTES at room
      exact frameA _ (by omega) (Or.inr (by omega))
    have s3Frame : ∀ w < 2^33, w < 1673 ∨ 1689 ≤ w → memoryView (qS3 s) w = memoryView s w :=
      fun w b o => leafFrame w b (by omega)
    have f1Frame : ∀ w < 2^33, w < 1673 ∨ 1689 ≤ w → memoryView (qF1 s) w = memoryView s w :=
      fun w b o => (frame1 w b (by omega)).trans (s3Frame w b o)
    have f2Frame : ∀ w < 2^33, w < 1673 ∨ 1689 ≤ w → memoryView (qF2 s) w = memoryView s w :=
      fun w b o => (frame2 w b (by omega)).trans (f1Frame w b o)
    interval_cases j
    · rw [show 13384+32*(r ^^^ 1) = 8*(1673+4*(r ^^^ 1)) by omega,
        Checker.aligned_digest_frame (qF1 s) (qCallState s) (1673+4*(r ^^^ 1)) ?_]
      · rw [show 8*(1673+4*(r ^^^ 1)) = 13384+32*(r ^^^ 1) by omega]
        exact read1.trans (proofSafe _ s3Frame)
      · intro o small
        exact (view_of_mem callMem _).trans ((frame3 _ (by omega) (by omega)).trans (frame2 _ (by omega) (by omega)))
    · rw [show 13384+32*(r ^^^ 2) = 8*(1673+4*(r ^^^ 2)) by omega,
        Checker.aligned_digest_frame (qF2 s) (qCallState s) (1673+4*(r ^^^ 2)) ?_]
      · rw [show 8*(1673+4*(r ^^^ 2)) = 13384+32*(r ^^^ 2) by omega]
        exact read2.trans (proofSafe _ f1Frame)
      · intro o small
        exact (view_of_mem callMem _).trans (frame3 _ (by omega) (by omega))
    · rw [show 13384+32*(r ^^^ 3) = 8*(1673+4*(r ^^^ 3)) by omega,
        Checker.aligned_digest_frame (qF3 s) (qCallState s) (1673+4*(r ^^^ 3)) ?_]
      · rw [show 8*(1673+4*(r ^^^ 3)) = 13384+32*(r ^^^ 3) by omega]
        exact read3.trans (proofSafe _ f2Frame)
      · intro o small
        exact view_of_mem callMem _
  · intro w bounded outside
    exact (survive w bounded (by omega) (by omega) (by omega)).trans (leafFrame w bounded (by omega))


/-! ### The permutation input is the quartet behind 72 zero bytes -/

theorem read_zero_words (c : MachineState) (base n : Nat)
    (zero : ∀ w, base ≤ w → w < base + n → memoryView c w = 0) :
    readBuffer c (8*base) (8*n) = 0 := by
  unfold readBuffer
  have bytes : ∀ i ∈ Finset.range (8*n),
      (c.getByte (BitVec.ofNat 64 (8*base+i))).toNat * 2^(8*i) = 0 := by
    intro i inside
    have small := Finset.mem_range.mp inside
    have aligned := aligned_byte c (base + i/8) (i%8) (by omega)
    rw [show 8*(base+i/8) + i%8 = 8*base+i by omega,
      show 8*(base+i/8) + 8*(i%8/8) = 8*(base+i/8) by omega] at aligned
    have word : c.getMem (BitVec.ofNat 64 (8*(base+i/8))) = 0 := zero _ (by omega) (by omega)
    rw [aligned, word]
    simp [extractByte]
  rw [Finset.sum_eq_zero bytes]
  rfl

theorem block_split (x : BitVec 1600) : x = x.extractLsb' 576 1024 ++ x.extractLsb' 0 576 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  rw [BitVec.getLsbD_append]
  by_cases low : i < 576
  · simp only [low, decide_true, ite_true, BitVec.getLsbD_extractLsb', Nat.zero_add, Bool.true_and]
  · simp only [low, decide_false, ite_false, BitVec.getLsbD_extractLsb']
    have upper : i - 576 < 1024 := by omega
    simp only [upper, decide_true, Bool.true_and]
    congr 1
    omega

theorem q_input_enc {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    qInput s = quartetEncode (qQuartet s) := by
  have frame := (q_call_memory entry).2.2
  have prefixZero : readBuffer (qCallState s) 13312 72 = 0 := by
    have := read_zero_words (qCallState s) 1664 9 (fun w lo hi => by
      rw [frame w (by omega) (Or.inl (by omega))]
      exact entry.zeroPrefix w lo (by omega))
    simpa using this
  have whole : qInput s = readBuffer (qCallState s) 13312 200 := by
    unfold qInput
    exact (read_permutation_window (qCallState s) 1664).symm
  rw [whole, block_split (readBuffer (qCallState s) 13312 200)]
  have high : (readBuffer (qCallState s) 13312 200).extractLsb' 576 1024 = readBuffer (qCallState s) 13384 128 :=
    read_buffer_slice (qCallState s) 13312 200 72 128 (by decide)
  have low : (readBuffer (qCallState s) 13312 200).extractLsb' 0 576 = readBuffer (qCallState s) 13312 72 :=
    read_buffer_slice (qCallState s) 13312 200 0 72 (by decide)
  rw [high, low, prefixZero]
  rfl

theorem q_quartet_slot {ordinal : Nat} {index : Index} {s : MachineState} (k : Nat) (small : k < 4) :
    (qQuartet s).extractLsb' (256*k) 256 = readBuffer (qCallState s) (13384+32*k) 32 := by
  have slice := read_buffer_slice (qCallState s) 13384 128 (32*k) 32 (by omega)
  rw [show 8*(32*k) = 256*k by omega] at slice
  exact slice

/-- The four slots of the hashed quartet: the leaf digest at `index % 4`, proof siblings elsewhere. -/
theorem q_quartet_slots {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s) :
    (qQuartet s).extractLsb' (256*(index.val % 4)) 256 = readBuffer s 12288 32 ∧
      ∀ j, 1 ≤ j → j ≤ 3 →
        (qQuartet s).extractLsb' (256*((index.val % 4) ^^^ j)) 256 =
          readBuffer s (checkProofByte ordinal + (16+32*(j-1))) 32 := by
  obtain ⟨leaf, siblings, _⟩ := q_call_memory entry
  have hr : index.val % 4 < 4 := Nat.mod_lt _ (by decide)
  refine ⟨(q_quartet_slot (ordinal := ordinal) (index := index) _ hr).trans leaf, fun j lo hi => ?_⟩
  exact (q_quartet_slot (ordinal := ordinal) (index := index) _ (xor_small _ _ hr (by omega))).trans (siblings j lo hi)

/-! ### The block's end state -/

theorem q_final_regs {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s)
    (reply : Block) :
    LowerCursor ordinal index 0 (qFinal s reply) ∧ LowerSaved s (qFinal s reply) := by
  obtain ⟨_, _, _, _, _, _, x21, _, callKept⟩ := q_call_regs entry
  obtain ⟨tpc, _, treg⟩ := q_return_post (qReplyState s reply)
  obtain ⟨epc, _, ex6, ekept⟩ := q_exit_post (qReturn (qReplyState s reply)) tpc
  obtain ⟨lpc, _, x11, x13, x29, lkept⟩ := q_lower_post (straight qExitCode (qReturn (qReplyState s reply)) 3) epc
  have replyReg (r : Reg) : (qReplyState s reply).getReg r = (qCallState s).getReg r := writeBits_register _ _ _ r
  have keep (r : Reg) (a : r ≠ .x10) (b : r ≠ .x7) (c : r ≠ .x28) (d : r ≠ .x31) (e : r ≠ .x21) (g : r ≠ .x12)
      (h : r ≠ .x6) (i : r ≠ .x11) (k : r ≠ .x13) (l : r ≠ .x29) : (qFinal s reply).getReg r = s.getReg r :=
    (lkept r i k l).trans ((ekept r h).trans ((treg r).trans ((replyReg r).trans (callKept r a b c d e g))))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, x11, x13⟩, ?_⟩
  · simpa [qFinal] using lpc
  · change (straight qLowerCode (straight qExitCode (qReturn (qReplyState s reply)) 3) 3).getReg .x6 = _
    rw [lkept .x6 (by decide) (by decide) (by decide), ex6, treg, treg, replyReg, replyReg,
      callKept .x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      callKept .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      entry.node, entry.heapBase, QuartetRV.quarter_shift, ← BitVec.ofNat_add, QuartetCheck.lower_node_two]
    congr 1
    change index.val/4 + 4194304 = 4194304 + index.val/4
    omega
  · change (straight qLowerCode (straight qExitCode (qReturn (qReplyState s reply)) 3) 3).getReg .x21 = _
    rw [lkept .x21 (by decide) (by decide) (by decide), ekept .x21 (by decide), treg, replyReg, x21]
    rfl
  · change (straight qLowerCode (straight qExitCode (qReturn (qReplyState s reply)) 3) 3).getReg .x29 = _
    rw [x29]; rfl
  · exact (keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans entry.digest
  · exact (keep .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans entry.pair
  · exact (keep .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans entry.selector
  · intro r saved
    unfold RecordSaved at saved
    apply keep r <;>
      rcases saved with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- The quartet node the block leaves at 12288: reply bytes `168..200` (even group) or `0..32` (odd). -/
theorem q_final_memory {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s)
    (reply : Block) :
    (∀ w < 2^33, (w < 1515 ∨ 1561 ≤ w) → (w < 1673 ∨ 1690 ≤ w) → memoryView (qFinal s reply) w = memoryView s w) ∧
      readBuffer (qFinal s reply) 12288 32 = quartetNode (index.val / 4) reply := by
  obtain ⟨tpc, tmem, _⟩ := q_return_post (qReplyState s reply)
  have exitMem := (q_exit_post (qReturn (qReplyState s reply)) tpc).2.1
  have lowerMem := (q_lower_post (straight qExitCode (qReturn (qReplyState s reply)) 3) (q_exit_post _ tpc).1).2.1
  have fMem : (qFinal s reply).mem = (qReplyState s reply).mem := lowerMem.trans (exitMem.trans tmem)
  have parity := q_odd_index entry
  change BitVec 1600 at reply
  constructor
  · intro w bounded scratch slots
    rw [view_of_mem fMem w]
    change memoryView (writeBits (qCallState s) (wordAddress (qOutWord s)) reply) w = _
    rw [permutation_write_memory (qCallState s) (qOutWord s) w reply (q_out_bound s) bounded, writeWindow,
      dite_eq_right (show ¬(qOutWord s ≤ w ∧ w < qOutWord s + 25) by unfold qOutWord; split <;> omega)]
    exact (q_call_memory entry).2.2 w bounded (by omega)
  · rw [read_buffer_memory_congr _ _ fMem]
    unfold qReplyState
    by_cases even : index.val / 4 % 2 = 0
    · have out : qOutWord s = 1515 := by
        unfold qOutWord; rw [parity]; simp [show ¬ (index.val / 4 % 2 = 1) by omega]
      rw [out]; unfold quartetNode; rw [if_pos even]
      exact write_bits_digest (qCallState s) 12120 168 reply (by decide) (by decide)
    · have out : qOutWord s = 1536 := by
        unfold qOutWord; rw [parity]; simp [show index.val / 4 % 2 = 1 by omega]
      rw [out]; unfold quartetNode; rw [if_neg even]
      exact write_bits_digest (qCallState s) 12288 0 reply (by decide) (by decide)

theorem q_steps_bound (s : MachineState) : qCallSteps s + 1 + 7 ≤ 137 := by
  unfold qCallSteps; split <;> omega

/-! ### The quartet block as a record segment -/

def qQuery (s : MachineState) : OracleComp World MachineState := do
  let reply ← World.query (.inr (.inr (.inl (qInput s))))
  return qFinal s reply

def quartetBlock (oracle : Oracle) (s : MachineState) : RecordBlock :=
  let reply := oracle.permutation (qInput s)
  ⟨qFinal s reply, qCallSteps s + 1 + 7, qCallSteps s + 8 + 7, [.permutation (qInput s) reply]⟩

attribute [local irreducible] execute in
theorem quartet_block_run {ordinal : Nat} {index : Index} {s : MachineState} (entry : QuartetEntry ordinal index s)
    (oracle : Oracle) (fuel : Nat) :
    let block := quartetBlock oracle s
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel block.state false))
    checkEvaluation oracle (recordRows (execute packedImage (block.steps+fuel) s false)) =
      ((tail.1.1.charge block.cycles 1, block.rows++tail.1.2), 1+tail.2) := by
  intro block tail
  have run : execute packedImage (qCallSteps s + 1 + 7 + fuel) s false = (do
      let next ← qQuery s
      let result ← execute packedImage fuel next false
      return result.charge (qCallSteps s + 8 + 7) 1) := by
    rw [q_execute entry fuel]
    simp only [qQuery, bind_assoc, pure_bind]
  have rows : checkEvaluation oracle (recordRows (qQuery s)) =
      ((qFinal s (oracle.permutation (qInput s)), [.permutation (qInput s) (oracle.permutation (qInput s))]), 1) := by
    simp only [qQuery, record_rows_query, check_evaluation_public_bind, check_evaluation_map, record_rows_pure,
      check_evaluation_pure]
    rfl
  change checkEvaluation oracle (recordRows (execute packedImage (qCallSteps s + 1 + 7 + fuel) s false)) = _
  rw [run, check_recorded_bind, rows]
  simp only [bind_pure_comp, check_recorded_map]
  rfl

end TwoPermutationPrototype.Packed.Checker
