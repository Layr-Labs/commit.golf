import CommitGolfCandidate.K3OpenCapSpec
import CommitGolfCandidate.GroupOpenSiblingRun
import CommitGolfCandidate.GroupOpenFields
import CommitGolfCandidate.GroupOpenCapCopy

/-! T238 cap emit, the part both node kinds share: `x7 := x25+32·node`, the alignment-dispatched 28-byte copy,
`lhu x31,28(x7)` and the `jal` to WK (word 855); `CapCopy.cycles dest+4` cycles.
Also the single-step, halfword and position helpers the two emit cases use. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
open Opening (capDigestAddress cap_digest_bounds)

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

/-- One unit-cost row instruction at its word. -/
theorem row_step (state : MachineState) (index : Nat) (instruction : Instr) (bounded : index < 896)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (openingImage.code[index]?).bind Opening.decodeBase = some instruction)
    (kind : rowInstr instruction = true) (valid : memoryArgumentsValid state instruction = true) :
    RunsOpeningBlock state (execInstrBr state instruction) 1 ∧
      (execInstrBr state instruction).pc = rowNext (index, instruction) := by
  refine ⟨fun fuel coins => ?_, row_pc state (index, instruction) kind pc⟩
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (packed_fetch_base _ _ _ bounded pc decoded)
    (row_ordinary _ _ kind valid), row_cycles _ kind]

/-- One `beq` at its word. -/
theorem beq_step (state : MachineState) (index : Nat) (rs1 rs2 : Reg) (offset : BitVec 13) (bounded : index < 896)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (openingImage.code[index]?).bind Opening.decodeBase = some (.BEQ rs1 rs2 offset)) :
    RunsOpeningBlock state (execInstrBr state (.BEQ rs1 rs2 offset)) 1 := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (packed_fetch_base _ _ _ bounded pc decoded)
    (show ordinaryStep state (.base (.BEQ rs1 rs2 offset)) = some (execInstrBr state (.BEQ rs1 rs2 offset)) from rfl)]
  rfl

theorem half_split (x : BitVec 16) : x.extractLsb' 8 8 ++ x.extractLsb' 0 8 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases low : i < 8
  · simp [low]
  · have high : i - 8 < 8 := by omega
    have back : 8 + (i - 8) = i := by omega
    simp [low, high, back]


theorem align_any (q : Nat) (fit : q < 2^64) : (alignToDword (BitVec.ofNat 64 q)).toNat = q - q % 8 := by
  let word : Word := BitVec.ofNat 64 q
  let aligned := alignToDword word
  have wordAsNat : word.toNat = q := by
    simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  have alignedAtMost : aligned.toNat ≤ q := by
    rw [show aligned.toNat = word.toNat &&& (~~~7#64).toNat by exact BitVec.toNat_and _ _]
    exact Nat.and_le_left.trans (le_of_eq wordAsNat)
  have offset : byteOffset word = q % 8 := byte_offset_nat q fit
  have whole := congrArg BitVec.toNat (alignToDword_add_byteOffset word)
  change (aligned+BitVec.ofNat 64 (byteOffset word)).toNat = word.toNat at whole
  rw [BitVec.toNat_add, wordAsNat, BitVec.toNat_ofNat, offset, Nat.mod_eq_of_lt (by omega : q % 8 < 2^64)] at whole
  have small : aligned.toNat < 2^64 := aligned.isLt
  change aligned.toNat = _
  omega

theorem emit_dword_same (a b : Nat) (fa : a < 2^64) (fb : b < 2^64) (same : a - a % 8 = b - b % 8) :
    alignToDword (BitVec.ofNat 64 a) = alignToDword (BitVec.ofNat 64 b) :=
  BitVec.eq_of_toNat_eq (by rw [align_any a fa, align_any b fb]; exact same)

private theorem emit_shift_extract (x : BitVec 16) (k : Nat) : x.extractLsb' k 8 = (x >>> k).truncate 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, BitVec.truncate, BitVec.toNat_setWidth]

/-- The two bytes of an aligned halfword load. -/
theorem emit_half_bytes (s : MachineState) (a : Nat) (even : a % 2 = 0) (fit : a+2 ≤ 2^64) :
    (s.getHalfword (BitVec.ofNat 64 a)).extractLsb' 0 8 = s.getByte (BitVec.ofNat 64 a) ∧
    (s.getHalfword (BitVec.ofNat 64 a)).extractLsb' 8 8 = s.getByte (BitVec.ofNat 64 (a+1)) := by
  have oa := byte_offset_nat a (by omega)
  have ob := byte_offset_nat (a+1) (by omega)
  constructor
  · have low := ProjectedHalfword.load_byte s (BitVec.ofNat 64 a) (BitVec.ofNat 64 a) rfl rfl
    rw [oa, show a % 8 % 2 = 0 by omega, Nat.zero_mul] at low
    rw [emit_shift_extract]
    exact low
  · have high := ProjectedHalfword.load_byte s (BitVec.ofNat 64 a) (BitVec.ofNat 64 (a+1))
      (emit_dword_same _ _ (by omega) (by omega) (by omega)) (by rw [oa, ob]; omega)
    rw [ob, show (a+1) % 8 % 2 = 1 by omega, Nat.one_mul] at high
    rw [emit_shift_extract]
    exact high

/-- The bytes an aligned halfword store leaves. -/
theorem emit_stored_byte (s : MachineState) (a b : Nat) (v : BitVec 16) (even : a % 2 = 0)
    (fit : a+2 ≤ 2^64) (small : b < 2) :
    (s.setHalfword (BitVec.ofNat 64 a) v).getByte (BitVec.ofNat 64 (a+b)) = v.extractLsb' (8*b) 8 := by
  have oa := byte_offset_nat a (by omega)
  have ob := byte_offset_nat (a+b) (by omega)
  have cond : alignToDword (BitVec.ofNat 64 (a+b)) = alignToDword (BitVec.ofNat 64 a) ∧
      byteOffset (BitVec.ofNat 64 (a+b)) / 2 = byteOffset (BitVec.ofNat 64 a) / 2 :=
    ⟨emit_dword_same _ _ (by omega) (by omega) (by omega), by rw [oa, ob]; omega⟩
  rw [ProjectedHalfword.store_byte, if_pos cond, ob, show (a+b) % 8 % 2 = b by omega, emit_shift_extract,
    Nat.mul_comm]

theorem half_at_eq (s : MachineState) (a : Nat) (even : a % 2 = 0) (fit : a+8 ≤ 2^64) :
    halfAt s a = s.getHalfword (BitVec.ofNat 64 a) := by
  obtain ⟨low, high⟩ := emit_half_bytes s a even (by omega)
  unfold halfAt
  rw [← low, ← high, half_split]

theorem append_low_byte (x y : BitVec 8) : (x ++ y).extractLsb' 0 8 = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.zero_add]
  simp [hi]

theorem append_high_byte (x y : BitVec 8) : (x ++ y).extractLsb' 8 8 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have back : 8 + i - 8 = i := by omega
  have above : ¬(8 + i < 8) := by omega
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, back]
  simp [hi, above]

theorem emit_byte_of_mem {s t : MachineState} (same : s.mem = t.mem) (q : Word) : s.getByte q = t.getByte q := by
  simp only [MachineState.getByte, MachineState.getMem, same]

/-- An emit step that keeps the fixed registers and the words below the proof keeps the cap position. -/
theorem cap_position_kept {groups : List Nat} {before after : MachineState} {node dest dest' : Nat}
    (position : CapPosition groups before node dest)
    (regs : ∀ r, r ≠ .x7 → r ≠ .x21 → r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
      after.getReg r = before.getReg r)
    (words : ∀ a < Opening.proofBase, after.getMem (BitVec.ofNat 64 a) = before.getMem (BitVec.ofNat 64 a))
    (destWord : after.getReg .x21 = BitVec.ofNat 64 dest') : CapPosition groups after node dest' := by
  refine ⟨?_, (regs .x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    position.nodeWord, destWord⟩
  apply position.context.of_preserved
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      exact regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro n _ inside
    have below : Opening.markBase+8*n < Opening.proofBase := by
      have small := Opening.marks_before_trapdoor
      have heap : Opening.trapdoorBase ≤ Opening.proofBase := by decide
      omega
    exact words _ below

/-- Compute the source pointer, copy 28 bytes and load the final halfword at word 696. -/
theorem cap_emit_prefix (groups : List Nat) (state : MachineState) (node dest : Nat)
    (bounded : node < 512) (position : CapPosition groups state node dest) (pc : state.pc = 0x1a70)
    (separate : Opening.proofBase ≤ dest) (aligned : dest % 2 = 0) (fits : dest+30 ≤ MEMORY_BYTES) :
    ∃ mid, RunsOpeningBlock state mid (CapCopy.cycles dest+3) ∧ mid.pc = BitVec.ofNat 64 (4096+4*697) ∧
      mid.getReg .x21 = BitVec.ofNat 64 dest ∧
      mid.getReg .x31 = (halfAt state (capDigestAddress node+28)).zeroExtend 64 ∧
      (∀ r, r ≠ .x7 → r ≠ .x31 → mid.getReg r = state.getReg r) ∧
      (∀ b < 28, mid.getByte (BitVec.ofNat 64 (dest+b)) =
        state.getByte (BitVec.ofNat 64 (capDigestAddress node+b))) ∧
      (∀ a < 2^64, (a < dest ∨ dest+28 ≤ a) →
        mid.getByte (BitVec.ofNat 64 a) = state.getByte (BitVec.ofNat 64 a)) ∧
      (∀ a < Opening.proofBase, mid.getMem (BitVec.ofNat 64 a) = state.getMem (BitVec.ofNat 64 a)) := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  obtain ⟨srcAlign, srcBelow⟩ := cap_digest_bounds node bounded
  have initial := cap_source_post state
  let s1 := capSource state
  have source : s1.getReg .x7 = BitVec.ofNat 64 (capDigestAddress node) := by
    rw [initial.2.2.1, position.context.heap, position.nodeWord, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 Opening.trapdoorBase + BitVec.ofNat 64 node * BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm node, ← BitVec.ofNat_add]
    rfl
  have destination : s1.getReg .x21 = BitVec.ofNat 64 dest :=
    (initial.2.2.2 .x21 (by decide)).trans position.destWord
  have setupRun : RunsOpeningBlock state s1 2 := fun fuel coins => execute_cap_source state pc fuel coins
  have sa : capDigestAddress node%8=0 := srcAlign
  obtain ⟨s2, place⟩ := CapCopy.copy s1 (capDigestAddress node) dest
    (by rw [initial.1, pc]; rfl) source destination sa aligned (by omega) (by omega)
  have copy : ByteCopy s1 s2 (capDigestAddress node) dest 28 := place.bytes
  have pc2 := place.pc
  have reg2 := place.regs
  have capRun := place.run
  have frame2 : ∀ a < 2^64, (a < dest ∨ dest+28 ≤ a) →
      s2.getByte (BitVec.ofNat 64 a) = state.getByte (BitVec.ofNat 64 a) := by
    intro a small away
    have ne : ∀ i < 28, BitVec.ofNat 64 a ≠ BitVec.ofNat 64 (dest+i) := fun i hi e => by
      have := Opening.nat_address_injective small (by omega) e
      omega
    rw [copy.frame _ ne]
    exact emit_byte_of_mem initial.2.1 _
  have addr3 : s2.getReg .x7 + signExtend12 (28#12) = BitVec.ofNat 64 (capDigestAddress node+28) := by
    rw [reg2 .x7 (by decide), source, show signExtend12 (28#12) = BitVec.ofNat 64 28 by decide,
      ← BitVec.ofNat_add]
  have step3 := row_step s2 696 (.LHU .x31 .x7 28#12) (by decide) pc2 (by decide +kernel) rfl
    (by change accessValid (s2.getReg .x7 + signExtend12 (28#12)) 2 = true
        rw [addr3]; exact half_access _ (by omega) (by omega))
  let s3 := execInstrBr s2 (.LHU .x31 .x7 28#12)
  have mem4 : s3.mem = s2.mem := by simp [s3, execInstrBr]
  have reg4 (r : Reg) (keep : r ≠ .x31) : s3.getReg r = s2.getReg r := by
    simp [s3, execInstrBr, Ne.symm keep]
  have top4 : s3.getReg .x31 = (s2.getHalfword (BitVec.ofNat 64 (capDigestAddress node+28))).zeroExtend 64 := by
    rw [← addr3]
    simp [s3, execInstrBr]
  have half2 : s2.getHalfword (BitVec.ofNat 64 (capDigestAddress node+28)) = halfAt state (capDigestAddress node+28) := by
    rw [← half_at_eq s2 (capDigestAddress node+28) (by omega) (by omega)]
    unfold halfAt
    rw [frame2 (capDigestAddress node+28+1) (by omega) (Or.inl (by omega)),
      frame2 (capDigestAddress node+28) (by omega) (Or.inl (by omega))]
  refine ⟨s3, ?_, step3.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert (setupRun.next capRun).next step3.1 using 1 <;> omega
  · rw [reg4 .x21 (by decide), reg2 .x21 (by decide), destination]
  · rw [top4, half2]
  · intro r a b
    rw [reg4 r b, reg2 r b]
    exact initial.2.2.2 r a
  · intro b inside
    rw [emit_byte_of_mem mem4, copy.copied b inside]
    exact emit_byte_of_mem initial.2.1 _
  · intro a small away
    rw [emit_byte_of_mem mem4]
    exact frame2 a small away
  · intro a below
    have stable : s2.getMem (BitVec.ofNat 64 a) = s1.getMem (BitVec.ofNat 64 a) :=
      place.below _ (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a<2^64 by omega)]
        have : Opening.proofBase%8=0 := by decide
        omega)
    have m1 : s1.mem = state.mem := initial.2.1
    calc s3.getMem (BitVec.ofNat 64 a) = s2.getMem (BitVec.ofNat 64 a) := by
          simp only [MachineState.getMem, mem4]
      _ = s1.getMem (BitVec.ofNat 64 a) := stable
      _ = state.getMem (BitVec.ofNat 64 a) := by simp only [MachineState.getMem, m1]

end TwoPermutationPrototype.GroupedOpening
