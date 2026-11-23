import CommitGolfCandidate.TwoPermutationPackedCapRoot
import CommitGolfCandidate.TwoPermutationPackedCapHashFrame
import CommitGolfCandidate.TwoPermutationPackedCapSegment
import CommitGolfCandidate.ProjectedHalfword

/-! # One-byte search: the search block (check words 1163..1220)

Reached on a root mismatch (`0x222c`). It rejects unless the proof end `x22` is `proofBase + 72160`; picks u from the
marks of leaves 510 and 511 (rejecting when both are marked); then for g = 1..255 writes g into bits 230..237 of u's
slot, recomputes u's ancestors with the walk's compression and 238-bit mask, and accepts when the root slot equals
the commitment. This file covers the entry, the pick and a trial's head; `TwoPermutationPackedSearchClimb` the climb step,
`TwoPermutationPackedSearchRun` the compare, accept and next, `TwoPermutationPackedSearchLoop` the loop. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt write_bits_word_outside)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-! ### The words -/

theorem searchCode1163 : (packedImage.code[1163]?).bind decodeInstruction = some (.base (.LUI .x7 421890)) := rfl
theorem searchCode1164 : (packedImage.code[1164]?).bind decodeInstruction = some (.base (.ADDI .x7 .x7 1352)) := rfl
theorem searchCode1165 : (packedImage.code[1165]?).bind decodeInstruction = some (.base (.SLLI .x7 .x7 3)) := rfl
theorem searchCode1166 : (packedImage.code[1166]?).bind decodeInstruction = some (.base (.BNE .x22 .x7 4984)) := rfl
theorem searchCode1167 : (packedImage.code[1167]?).bind decodeInstruction = some (.base (.ADDI .x7 .x26 2047)) := rfl
theorem searchCode1168 : (packedImage.code[1168]?).bind decodeInstruction = some (.base (.LD .x28 .x7 2041)) := rfl
theorem searchCode1169 : (packedImage.code[1169]?).bind decodeInstruction = some (.base (.LD .x29 .x7 2033)) := rfl
theorem searchCode1170 : (packedImage.code[1170]?).bind decodeInstruction = some (.base (.ADDI .x6 .x0 511)) := rfl
theorem searchCode1171 : (packedImage.code[1171]?).bind decodeInstruction = some (.base (.BEQ .x28 .x0 16)) := rfl
theorem searchCode1172 : (packedImage.code[1172]?).bind decodeInstruction = some (.base (.BNE .x29 .x0 4960)) := rfl
theorem searchCode1173 : (packedImage.code[1173]?).bind decodeInstruction = some (.base (.ADDI .x6 .x0 510)) := rfl
theorem searchCode1174 : (packedImage.code[1174]?).bind decodeInstruction = some (.base (.JAL .x0 12)) := rfl
theorem searchCode1175 : (packedImage.code[1175]?).bind decodeInstruction = some (.base (.BNE .x29 .x0 8)) := rfl
theorem searchCode1176 : (packedImage.code[1176]?).bind decodeInstruction = some (.base (.ADDI .x6 .x0 255)) := rfl
theorem searchCode1177 : (packedImage.code[1177]?).bind decodeInstruction = some (.base (.ADDI .x18 .x6 0)) := rfl
theorem searchCode1178 : (packedImage.code[1178]?).bind decodeInstruction = some (.base (.ADDI .x19 .x0 1)) := rfl
theorem searchCode1179 : (packedImage.code[1179]?).bind decodeInstruction = some (.base (.ADDI .x5 .x0 0)) := rfl
theorem searchCode1180 : (packedImage.code[1180]?).bind decodeInstruction = some (.base (.ADDI .x11 .x0 64)) := rfl
theorem searchCode1181 : (packedImage.code[1181]?).bind decodeInstruction = some (.base (.ADDI .x13 .x0 0)) := rfl
theorem searchCode1182 : (packedImage.code[1182]?).bind decodeInstruction = some (.base (.SLLI .x7 .x18 5)) := rfl
theorem searchCode1183 : (packedImage.code[1183]?).bind decodeInstruction = some (.base (.ADD .x7 .x25 .x7)) := rfl
theorem searchCode1184 : (packedImage.code[1184]?).bind decodeInstruction = some (.base (.LHU .x28 .x7 28)) := rfl
theorem searchCode1185 : (packedImage.code[1185]?).bind decodeInstruction = some (.base (.ANDI .x28 .x28 63)) := rfl
theorem searchCode1186 : (packedImage.code[1186]?).bind decodeInstruction = some (.base (.SLLI .x29 .x19 6)) := rfl
theorem searchCode1187 : (packedImage.code[1187]?).bind decodeInstruction = some (.base (.OR .x28 .x28 .x29)) := rfl
theorem searchCode1188 : (packedImage.code[1188]?).bind decodeInstruction = some (.base (.SH .x7 .x28 28)) := rfl
theorem searchCode1189 : (packedImage.code[1189]?).bind decodeInstruction = some (.base (.ADDI .x6 .x18 0)) := rfl
theorem searchCode1190 : (packedImage.code[1190]?).bind decodeInstruction = some (.base (.SRLI .x6 .x6 1)) := rfl
theorem searchCode1191 : (packedImage.code[1191]?).bind decodeInstruction = some (.base (.SLLI .x10 .x6 6)) := rfl
theorem searchCode1192 : (packedImage.code[1192]?).bind decodeInstruction = some (.base (.ADD .x10 .x25 .x10)) := rfl
theorem searchCode1193 : (packedImage.code[1193]?).bind decodeInstruction = some (.base (.SLLI .x12 .x6 5)) := rfl
theorem searchCode1194 : (packedImage.code[1194]?).bind decodeInstruction = some (.base (.ADD .x12 .x25 .x12)) := rfl
theorem searchCode1195 : (packedImage.code[1195]?).bind decodeInstruction = some (.base (.ECALL)) := rfl
theorem searchCode1196 : (packedImage.code[1196]?).bind decodeInstruction = some (.base (.LHU .x31 .x12 28)) := rfl
theorem searchCode1197 : (packedImage.code[1197]?).bind decodeInstruction = some (.base (.SLLI .x31 .x31 50)) := rfl
theorem searchCode1198 : (packedImage.code[1198]?).bind decodeInstruction = some (.base (.SRLI .x31 .x31 50)) := rfl
theorem searchCode1199 : (packedImage.code[1199]?).bind decodeInstruction = some (.base (.SW .x12 .x31 28)) := rfl
theorem searchCode1200 : (packedImage.code[1200]?).bind decodeInstruction = some (.base (.ADDI .x7 .x0 1)) := rfl
theorem searchCode1201 : (packedImage.code[1201]?).bind decodeInstruction = some (.base (.BNE .x6 .x7 8148)) := rfl
theorem searchCode1202 : (packedImage.code[1202]?).bind decodeInstruction = some (.base (.LD .x29 .x25 32)) := rfl
theorem searchCode1203 : (packedImage.code[1203]?).bind decodeInstruction = some (.base (.LD .x30 .x9 0)) := rfl
theorem searchCode1204 : (packedImage.code[1204]?).bind decodeInstruction = some (.base (.BNE .x29 .x30 52)) := rfl
theorem searchCode1205 : (packedImage.code[1205]?).bind decodeInstruction = some (.base (.LD .x29 .x25 40)) := rfl
theorem searchCode1206 : (packedImage.code[1206]?).bind decodeInstruction = some (.base (.LD .x30 .x9 8)) := rfl
theorem searchCode1207 : (packedImage.code[1207]?).bind decodeInstruction = some (.base (.BNE .x29 .x30 40)) := rfl
theorem searchCode1208 : (packedImage.code[1208]?).bind decodeInstruction = some (.base (.LD .x29 .x25 48)) := rfl
theorem searchCode1209 : (packedImage.code[1209]?).bind decodeInstruction = some (.base (.LD .x30 .x9 16)) := rfl
theorem searchCode1210 : (packedImage.code[1210]?).bind decodeInstruction = some (.base (.BNE .x29 .x30 28)) := rfl
theorem searchCode1211 : (packedImage.code[1211]?).bind decodeInstruction = some (.base (.LD .x29 .x25 56)) := rfl
theorem searchCode1212 : (packedImage.code[1212]?).bind decodeInstruction = some (.base (.LD .x30 .x9 24)) := rfl
theorem searchCode1213 : (packedImage.code[1213]?).bind decodeInstruction = some (.base (.BNE .x29 .x30 16)) := rfl
theorem searchCode1214 : (packedImage.code[1214]?).bind decodeInstruction = some (.base (.ADDI .x5 .x0 1)) := rfl
theorem searchCode1215 : (packedImage.code[1215]?).bind decodeInstruction = some (.base (.ADDI .x10 .x0 0)) := rfl
theorem searchCode1216 : (packedImage.code[1216]?).bind decodeInstruction = some (.base (.ECALL)) := rfl
theorem searchCode1217 : (packedImage.code[1217]?).bind decodeInstruction = some (.base (.ADDI .x19 .x19 1)) := rfl
theorem searchCode1218 : (packedImage.code[1218]?).bind decodeInstruction = some (.base (.ADDI .x7 .x0 256)) := rfl
theorem searchCode1219 : (packedImage.code[1219]?).bind decodeInstruction = some (.base (.BNE .x19 .x7 8044)) := rfl
theorem searchCode1220 : (packedImage.code[1220]?).bind decodeInstruction = some (.base (.JAL .x0 2093728)) := rfl

/-- The pc of check word `w`. -/
abbrev spc (w : Nat) : Word := BitVec.ofNat 64 (4096+4*w)

/-- The instructions of the search other than `ECALL`. -/
def searchKind : Instr → Bool
  | .ADDI .. | .LUI .. | .ADD .. | .SLLI .. | .SRLI .. | .ANDI .. | .OR .. | .LD .. | .LHU .. | .SH .. | .SW ..
  | .BEQ .. | .BNE .. | .JAL .. => true
  | _ => false

attribute [local irreducible] execute

@[local simp] private theorem search_reg_zero (s : MachineState) : s.getReg .x0 = 0#64 := rfl
@[local simp] private theorem search_sext_zero : signExtend12 (0#12) = 0#64 := by decide

/-- One ordinary search instruction. -/
theorem search_step (s : MachineState) (w : Nat) (op : Instr) (here : s.pc = spc w) (bound : w < 2^40)
    (code : (packedImage.code[w]?).bind decodeInstruction = some (.base op))
    (kind : searchKind op = true) (valid : memoryArgumentsValid s op = true) :
    Hop s (execInstrBr s op) 1 1 := by
  have f := wide_image_fetch packedImage s w op bound here code
  have step : ordinaryStep s (.base op) = some (execInstrBr s op) := by
    cases op <;> simp_all [searchKind, ordinaryStep]
  have cyc : instructionCycles (.base op) = 1 := by
    cases op <;> first | (simp [searchKind] at kind; done) | rfl
  intro fuel
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ f step, cyc]

/-- The search instructions that fall through to the next word. -/
def straightKind : Instr → Bool
  | .ADDI .. | .LUI .. | .ADD .. | .SLLI .. | .SRLI .. | .ANDI .. | .OR .. | .LD .. | .LHU .. | .SH .. | .SW .. => true
  | _ => false

theorem straight_pc (s : MachineState) (op : Instr) (kind : straightKind op = true) :
    (execInstrBr s op).pc = s.pc+4 := by
  cases op <;> first | (simp [straightKind] at kind; done) | rfl

private theorem reg_setReg (s : MachineState) (rd rs : Reg) (v : Word) :
    (s.setReg rd v).getReg rs = if rd = rs ∧ rd ≠ .x0 then v else s.getReg rs :=
  Opening.getReg_setReg s rd rs v

theorem mem_setReg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

theorem view_of_mem {a b : MachineState} (same : a.mem = b.mem) (word : Nat) :
    memoryView a word = memoryView b word := by
  simp only [memoryView, MachineState.getMem, same]

@[simp] theorem reg_setMem (s : MachineState) (a v : Word) (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
  cases r <;> rfl

theorem bne_pc (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).pc = if s.getReg a = s.getReg b then s.pc+4 else s.pc+signExtend13 d := by
  simp only [execInstrBr, bne_iff_ne]
  by_cases eq : s.getReg a = s.getReg b <;> simp [eq]

theorem beq_pc (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BEQ a b d)).pc = if s.getReg a = s.getReg b then s.pc+signExtend13 d else s.pc+4 := by
  simp only [execInstrBr, beq_iff_eq]
  by_cases eq : s.getReg a = s.getReg b <;> simp [eq]

theorem branch_reg (s : MachineState) (a b r : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).getReg r = s.getReg r ∧ (execInstrBr s (.BEQ a b d)).getReg r = s.getReg r := by
  constructor <;> simp only [execInstrBr] <;> split <;> rfl

theorem branch_mem (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).mem = s.mem ∧ (execInstrBr s (.BEQ a b d)).mem = s.mem := by
  constructor <;> simp only [execInstrBr] <;> split <;> rfl

/-! ### Entry (1163..1166): the proof end -/

/-- `proofBase + 72160`, the only proof end the search accepts. -/
abbrev searchEnd : Word := BitVec.ofNat 64 (13824430176+72160)

def entryState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr s (.LUI .x7 421890)) (.ADDI .x7 .x7 1352)) (.SLLI .x7 .x7 3)

theorem search_entry_facts (s : MachineState) :
    (entryState s).getReg .x7 = searchEnd ∧ (entryState s).pc = s.pc+4+4+4 ∧ (entryState s).mem = s.mem ∧
      ∀ r, r ≠ .x7 → (entryState s).getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [entryState, execInstrBr, reg_setReg] <;> decide
  · simp only [entryState]
    rw [straight_pc _ _ (by rfl), straight_pc _ _ (by rfl), straight_pc _ _ (by rfl)]
  · rfl
  · intro r ne
    simp [entryState, execInstrBr, reg_setReg, Ne.symm ne]

theorem entry_hop (s : MachineState) (here : s.pc = spc 1163) : Hop s (entryState s) 3 3 := by
  let s1 := execInstrBr s (.LUI .x7 421890)
  let s2 := execInstrBr s1 (.ADDI .x7 .x7 1352)
  have p1 : s1.pc = spc 1164 := by rw [straight_pc s _ (by rfl), here]; decide
  have p2 : s2.pc = spc 1165 := by rw [straight_pc s1 _ (by rfl), p1]; decide
  have a := search_step s 1163 _ here (by decide) searchCode1163 rfl rfl
  have b := search_step s1 1164 _ p1 (by decide) searchCode1164 rfl rfl
  have c := search_step s2 1165 _ p2 (by decide) searchCode1165 rfl rfl
  exact (a.thenDo b).thenDo c

/-- After the entry check: reject (pc 364) when the proof end is not `searchEnd`, else word 1167. -/
def entryBranch (s : MachineState) : MachineState := execInstrBr (entryState s) (.BNE .x22 .x7 4984)

theorem entry_branch (s : MachineState) (here : s.pc = spc 1163) :
    Hop s (entryBranch s) 4 4 ∧
      (entryBranch s).pc = (if s.getReg .x22 = searchEnd then spc 1167 else spc 364) ∧
      (entryBranch s).mem = s.mem ∧ ∀ r, r ≠ .x7 → (entryBranch s).getReg r = s.getReg r := by
  obtain ⟨x7, pc, mem, regs⟩ := search_entry_facts s
  have pcE : (entryState s).pc = spc 1166 := by rw [pc, here]; decide
  have d := search_step _ 1166 _ pcE (by decide) searchCode1166 rfl rfl
  refine ⟨(entry_hop s here).thenDo d, ?_, ?_, ?_⟩
  · unfold entryBranch
    rw [bne_pc, x7, regs .x22 (by decide), pcE]
    by_cases h : s.getReg .x22 = searchEnd
    · rw [if_pos h, if_pos h]
      decide
    · rw [if_neg h, if_neg h]
      decide
  · unfold entryBranch
    rw [(branch_mem _ _ _ _).1, mem]
  · intro r ne
    unfold entryBranch
    rw [(branch_reg _ _ _ _ _).1, regs r ne]

/-! ### The pick (1167..1181): u from the marks of leaves 510 and 511 -/

/-- The mark doubleword of cap node `n` (the mark table is at 4096). -/
def markWord (s : MachineState) (n : Nat) : Word := s.getMem (BitVec.ofNat 64 (4096+8*n))

/-- u = 511 when only 511 is unmarked, 510 when only 510 is, 255 when both are; none when both are marked. -/
def pickU (s : MachineState) : Option Nat :=
  if markWord s 511 = 0 then (if markWord s 510 = 0 then some 255 else some 511)
  else (if markWord s 510 = 0 then some 510 else none)

/-- What a trial needs at word 1182: u in `x18`, g in `x19`, the compression selectors, and the bases. -/
structure TrialReady (s : MachineState) (u g claim : Nat) : Prop where
  pc : s.pc = spc 1182
  node : s.getReg .x18 = BitVec.ofNat 64 u
  trial : s.getReg .x19 = BitVec.ofNat 64 g
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0
  roots : s.getReg .x25 = 16384#64
  commitment : s.getReg .x9 = wordAddress claim

def pickHead (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.ADDI .x7 .x26 2047)) (.LD .x28 .x7 2041))
    (.LD .x29 .x7 2033)) (.ADDI .x6 .x0 511)

theorem pick_head (s : MachineState) (here : s.pc = spc 1167) (marks : s.getReg .x26 = 4096#64) :
    Hop s (pickHead s) 4 4 ∧ (pickHead s).pc = spc 1171 ∧ (pickHead s).mem = s.mem ∧
      (pickHead s).getReg .x28 = markWord s 511 ∧ (pickHead s).getReg .x29 = markWord s 510 ∧
      (pickHead s).getReg .x6 = 511#64 ∧
      ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → (pickHead s).getReg r = s.getReg r := by
  let s1 := execInstrBr s (.ADDI .x7 .x26 2047)
  let s2 := execInstrBr s1 (.LD .x28 .x7 2041)
  let s3 := execInstrBr s2 (.LD .x29 .x7 2033)
  have x7 : s1.getReg .x7 = 6143#64 := by simp [s1, execInstrBr, reg_setReg, marks] <;> decide
  have x7' : s2.getReg .x7 = 6143#64 := by simp [s2, execInstrBr, reg_setReg, x7]
  have p1 : s1.pc = spc 1168 := by rw [straight_pc _ _ (by rfl), here]; decide
  have p2 : s2.pc = spc 1169 := by rw [straight_pc _ _ (by rfl), p1]; decide
  have p3 : s3.pc = spc 1170 := by rw [straight_pc _ _ (by rfl), p2]; decide
  have m1 : s1.mem = s.mem := rfl
  have m2 : s2.mem = s.mem := rfl
  have a := search_step s 1167 _ here (by decide) searchCode1167 rfl rfl
  have b := search_step s1 1168 _ p1 (by decide) searchCode1168 rfl (by
    simp [memoryArgumentsValid, memAccess, x7] <;> decide)
  have c := search_step s2 1169 _ p2 (by decide) searchCode1169 rfl (by
    simp [memoryArgumentsValid, memAccess, x7'] <;> decide)
  have d := search_step s3 1170 _ p3 (by decide) searchCode1170 rfl rfl
  have m28 : s2.getReg .x28 = markWord s 511 := by
    have e : s2.getReg .x28 = s1.getMem (s1.getReg .x7 + signExtend12 2041) := by
      simp [s2, execInstrBr, reg_setReg]
    rw [e, x7, show (6143#64 : Word) + signExtend12 2041 = BitVec.ofNat 64 (4096+8*511) by decide]
    unfold markWord MachineState.getMem
    rw [m1]
  have m29 : s3.getReg .x29 = markWord s 510 := by
    have e : s3.getReg .x29 = s2.getMem (s2.getReg .x7 + signExtend12 2033) := by
      simp [s3, execInstrBr, reg_setReg]
    rw [e, x7', show (6143#64 : Word) + signExtend12 2033 = BitVec.ofNat 64 (4096+8*510) by decide]
    unfold markWord MachineState.getMem
    rw [m2]
  have k28 : s3.getReg .x28 = markWord s 511 := by
    rw [← m28]
    simp [s3, execInstrBr, reg_setReg]
  refine ⟨((a.thenDo b).thenDo c).thenDo d, by
    show (execInstrBr s3 (.ADDI .x6 .x0 511)).pc = _
    rw [straight_pc _ _ (by rfl), p3]; decide, rfl, ?_, ?_, ?_, ?_⟩
  · show (execInstrBr s3 (.ADDI .x6 .x0 511)).getReg .x28 = _
    rw [← k28]
    simp [execInstrBr, reg_setReg]
  · show (execInstrBr s3 (.ADDI .x6 .x0 511)).getReg .x29 = _
    rw [← m29]
    simp [execInstrBr, reg_setReg]
  · show (execInstrBr s3 (.ADDI .x6 .x0 511)).getReg .x6 = _
    simp [execInstrBr, reg_setReg] <;> decide
  · intro r a6 a7 a28 a29
    simp [pickHead, execInstrBr, reg_setReg, Ne.symm a6, Ne.symm a7, Ne.symm a28, Ne.symm a29]

/-- 1177..1181: `x18 := x6`, `x19 := 1`, `x5 := 0`, `x11 := 64`, `x13 := 0`. -/
def pickInit (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.ADDI .x18 .x6 0)) (.ADDI .x19 .x0 1))
    (.ADDI .x5 .x0 0)) (.ADDI .x11 .x0 64)) (.ADDI .x13 .x0 0)

theorem pick_init (s : MachineState) (here : s.pc = spc 1177) :
    Hop s (pickInit s) 5 5 ∧ (pickInit s).pc = spc 1182 ∧ (pickInit s).mem = s.mem ∧
      (pickInit s).getReg .x18 = s.getReg .x6 ∧ (pickInit s).getReg .x19 = 1#64 ∧
      (pickInit s).getReg .x5 = 0 ∧ (pickInit s).getReg .x11 = 64 ∧ (pickInit s).getReg .x13 = 0 ∧
      ∀ r, r ≠ .x18 → r ≠ .x19 → r ≠ .x5 → r ≠ .x11 → r ≠ .x13 → (pickInit s).getReg r = s.getReg r := by
  let s1 := execInstrBr s (.ADDI .x18 .x6 0)
  let s2 := execInstrBr s1 (.ADDI .x19 .x0 1)
  let s3 := execInstrBr s2 (.ADDI .x5 .x0 0)
  let s4 := execInstrBr s3 (.ADDI .x11 .x0 64)
  have p1 : s1.pc = spc 1178 := by rw [straight_pc _ _ (by rfl), here]; decide
  have p2 : s2.pc = spc 1179 := by rw [straight_pc _ _ (by rfl), p1]; decide
  have p3 : s3.pc = spc 1180 := by rw [straight_pc _ _ (by rfl), p2]; decide
  have p4 : s4.pc = spc 1181 := by rw [straight_pc _ _ (by rfl), p3]; decide
  have a := search_step s 1177 _ here (by decide) searchCode1177 rfl rfl
  have b := search_step s1 1178 _ p1 (by decide) searchCode1178 rfl rfl
  have c := search_step s2 1179 _ p2 (by decide) searchCode1179 rfl rfl
  have d := search_step s3 1180 _ p3 (by decide) searchCode1180 rfl rfl
  have e := search_step s4 1181 _ p4 (by decide) searchCode1181 rfl rfl
  refine ⟨(((a.thenDo b).thenDo c).thenDo d).thenDo e, by
    show (execInstrBr s4 (.ADDI .x13 .x0 0)).pc = _
    rw [straight_pc _ _ (by rfl), p4]; decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pickInit, execInstrBr, reg_setReg]
  · simp [pickInit, execInstrBr, reg_setReg] <;> decide
  · simp [pickInit, execInstrBr, reg_setReg] <;> decide
  · simp [pickInit, execInstrBr, reg_setReg] <;> decide
  · simp [pickInit, execInstrBr, reg_setReg] <;> decide
  · intro r a b c d e
    simp [pickInit, execInstrBr, reg_setReg, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e]

theorem jal_pc (s : MachineState) (d : BitVec 21) : (execInstrBr s (.JAL .x0 d)).pc = s.pc + signExtend21 d := rfl

theorem jal_facts (s : MachineState) (d : BitVec 21) :
    (execInstrBr s (.JAL .x0 d)).mem = s.mem ∧ ∀ r, (execInstrBr s (.JAL .x0 d)).getReg r = s.getReg r := by
  refine ⟨rfl, fun r => ?_⟩
  simp [execInstrBr, reg_setReg]

/-- The pick: reject at 364 when both leaves are marked (6 steps), else a trial-ready state for g = 1 with the
memory unchanged. -/
theorem search_pick (s : MachineState) (claim : Nat) (here : s.pc = spc 1167) (marks : s.getReg .x26 = 4096#64)
    (roots : s.getReg .x25 = 16384#64) (commitment : s.getReg .x9 = wordAddress claim) :
    (pickU s = none → ∃ t, Hop s t 6 6 ∧ t.pc = spc 364) ∧
    (∀ u, pickU s = some u → ∃ t c, c ≤ 13 ∧ Hop s t c c ∧ TrialReady t u 1 claim ∧ t.mem = s.mem) := by
  obtain ⟨hop, hpc, hmem, h28, h29, h6, hregs⟩ := pick_head s here marks
  let b1 := execInstrBr (pickHead s) (.BEQ .x28 .x0 16)
  have s1171 := search_step (pickHead s) 1171 _ hpc (by decide) searchCode1171 rfl rfl
  have b1pc : b1.pc = if markWord s 511 = 0 then spc 1175 else spc 1172 := by
    show (execInstrBr (pickHead s) _).pc = _
    rw [beq_pc, h28, hpc]
    by_cases z : markWord s 511 = 0
    · rw [if_pos (by rw [z]; rfl), if_pos z]; decide
    · rw [if_neg (by intro e; exact z (e.trans rfl)), if_neg z]; decide
  have b1mem : b1.mem = s.mem := ((branch_mem _ _ _ _).2).trans hmem
  have b1reg (r : Reg) : b1.getReg r = (pickHead s).getReg r := (branch_reg _ _ _ _ _).2
  -- registers that survive the pick
  have keep (t : MachineState) (r : Reg) (t_eq : t.getReg r = (pickHead s).getReg r) (n6 : r ≠ .x6) (n7 : r ≠ .x7)
      (n28 : r ≠ .x28) (n29 : r ≠ .x29) : t.getReg r = s.getReg r := t_eq.trans (hregs r n6 n7 n28 n29)
  -- finishing from a state at 1177 with the chosen node in x6
  have finish (t : MachineState) (c u : Nat) (tpc : t.pc = spc 1177) (tc : Hop s t c c) (cb : c ≤ 8)
      (tmem : t.mem = s.mem) (t6 : t.getReg .x6 = BitVec.ofNat 64 u)
      (tregs : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → t.getReg r = s.getReg r) :
      ∃ t c, c ≤ 13 ∧ Hop s t c c ∧ TrialReady t u 1 claim ∧ t.mem = s.mem := by
    obtain ⟨ihop, ipc, imem, i18, i19, i5, i11, i13, iregs⟩ := pick_init t tpc
    refine ⟨pickInit t, c+5, by omega, tc.thenDo ihop, ⟨ipc, i18.trans t6, i19, i5, i11, i13, ?_, ?_⟩,
      imem.trans tmem⟩
    · rw [iregs .x25 (by decide) (by decide) (by decide) (by decide) (by decide),
        tregs .x25 (by decide) (by decide) (by decide) (by decide), roots]
    · rw [iregs .x9 (by decide) (by decide) (by decide) (by decide) (by decide),
        tregs .x9 (by decide) (by decide) (by decide) (by decide), commitment]
  constructor
  · intro none_
    unfold pickU at none_
    by_cases z11 : markWord s 511 = 0
    · rw [if_pos z11] at none_
      split at none_ <;> cases none_
    · rw [if_neg z11] at none_
      by_cases z10 : markWord s 510 = 0
      · rw [if_pos z10] at none_; cases none_
      · have pc1172 : b1.pc = spc 1172 := by rw [b1pc, if_neg z11]
        let c2 := execInstrBr b1 (.BNE .x29 .x0 4960)
        have step := search_step b1 1172 _ pc1172 (by decide) searchCode1172 rfl rfl
        refine ⟨c2, (hop.thenDo s1171).thenDo step, ?_⟩
        show (execInstrBr b1 _).pc = _
        rw [bne_pc, b1reg, h29, pc1172, if_neg (by intro e; exact z10 (e.trans rfl))]
        decide
  · intro u some_
    unfold pickU at some_
    by_cases z11 : markWord s 511 = 0
    · rw [if_pos z11] at some_
      have pc1175 : b1.pc = spc 1175 := by rw [b1pc, if_pos z11]
      let c2 := execInstrBr b1 (.BNE .x29 .x0 8)
      have step := search_step b1 1175 _ pc1175 (by decide) searchCode1175 rfl rfl
      have c2mem : c2.mem = s.mem := ((branch_mem _ _ _ _).1).trans b1mem
      have c2reg (r : Reg) : c2.getReg r = (pickHead s).getReg r := ((branch_reg _ _ _ _ _).1).trans (b1reg r)
      by_cases z10 : markWord s 510 = 0
      · rw [if_pos z10] at some_
        cases some_
        have c2pc : c2.pc = spc 1176 := by
          show (execInstrBr b1 _).pc = _
          rw [bne_pc, b1reg, h29, pc1175, if_pos (by rw [z10]; rfl)]
          decide
        let c3 := execInstrBr c2 (.ADDI .x6 .x0 255)
        have step2 := search_step c2 1176 _ c2pc (by decide) searchCode1176 rfl rfl
        refine finish c3 (4+1+1+1) 255 (by rw [straight_pc _ _ (by rfl), c2pc]; decide)
          (((hop.thenDo s1171).thenDo step).thenDo step2) (by omega) c2mem ?_ ?_
        · simp [c3, execInstrBr, reg_setReg] <;> decide
        · intro r a b c d
          rw [show c3.getReg r = c2.getReg r by simp [c3, execInstrBr, reg_setReg, Ne.symm a]]
          exact keep c2 r (c2reg r) a b c d
      · rw [if_neg z10] at some_
        cases some_
        have c2pc : c2.pc = spc 1177 := by
          show (execInstrBr b1 _).pc = _
          rw [bne_pc, b1reg, h29, pc1175, if_neg (by intro e; exact z10 (e.trans rfl))]
          decide
        refine finish c2 (4+1+1) 511 c2pc ((hop.thenDo s1171).thenDo step) (by omega) c2mem ?_ ?_
        · rw [c2reg, h6]
        · intro r a b c d
          exact keep c2 r (c2reg r) a b c d
    · rw [if_neg z11] at some_
      have pc1172 : b1.pc = spc 1172 := by rw [b1pc, if_neg z11]
      by_cases z10 : markWord s 510 = 0
      · rw [if_pos z10] at some_
        cases some_
        let c2 := execInstrBr b1 (.BNE .x29 .x0 4960)
        have step := search_step b1 1172 _ pc1172 (by decide) searchCode1172 rfl rfl
        have c2pc : c2.pc = spc 1173 := by
          show (execInstrBr b1 _).pc = _
          rw [bne_pc, b1reg, h29, pc1172, if_pos (by rw [z10]; rfl)]
          decide
        have c2mem : c2.mem = s.mem := ((branch_mem _ _ _ _).1).trans b1mem
        have c2reg (r : Reg) : c2.getReg r = (pickHead s).getReg r := ((branch_reg _ _ _ _ _).1).trans (b1reg r)
        let c3 := execInstrBr c2 (.ADDI .x6 .x0 510)
        let c4 := execInstrBr c3 (.JAL .x0 12)
        have c3pc : c3.pc = spc 1174 := by rw [straight_pc _ _ (by rfl), c2pc]; decide
        have step2 := search_step c2 1173 _ c2pc (by decide) searchCode1173 rfl rfl
        have step3 := search_step c3 1174 _ c3pc (by decide) searchCode1174 rfl rfl
        have c3reg (r : Reg) (n : r ≠ .x6) : c3.getReg r = c2.getReg r := by
          simp [c3, execInstrBr, reg_setReg, Ne.symm n]
        refine finish c4 (4+1+1+1+1) 510 (by rw [jal_pc, c3pc]; decide)
          ((((hop.thenDo s1171).thenDo step).thenDo step2).thenDo step3) (by omega)
          (((jal_facts _ _).1).trans c2mem) ?_ ?_
        · rw [(jal_facts _ _).2]
          simp [c3, execInstrBr, reg_setReg] <;> decide
        · intro r a b c d
          rw [(jal_facts _ _).2, c3reg r a]
          exact keep c2 r (c2reg r) a b c d
      · rw [if_neg z10] at some_
        cases some_

/-! ### A trial's head (1182..1189): bits 230..237 of u's slot become g -/

/-- The halfword holding bits 224..239 of slot `n`. -/
abbrev topHalf (n : Nat) : Word := BitVec.ofNat 64 (16384+32*n+28)

/-- The halfword a trial stores over `h`: `h`'s low 6 bits, then `g`. -/
def patchHalf (h : BitVec 16) (g : Word) : BitVec 16 :=
  ((h.zeroExtend 64 &&& signExtend12 63) ||| (g <<< (6 : BitVec 6).toNat)).truncate 16

def trialHead (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr s
    (.SLLI .x7 .x18 5)) (.ADD .x7 .x25 .x7)) (.LHU .x28 .x7 28)) (.ANDI .x28 .x28 63)) (.SLLI .x29 .x19 6))
    (.OR .x28 .x28 .x29)) (.SH .x7 .x28 28)) (.ADDI .x6 .x18 0)

theorem slot_base (u : Nat) (hu : u < 512) :
    16384#64 + (BitVec.ofNat 64 u <<< (5 : BitVec 6).toNat) = BitVec.ofNat 64 (16384+32*u) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 16384 + BitVec.ofNat 64 u * BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  congr 1
  omega

theorem top_half_addr (u : Nat) (hu : u < 512) :
    BitVec.ofNat 64 (16384+32*u) + signExtend12 28 = topHalf u := by
  rw [show signExtend12 28 = BitVec.ofNat 64 28 from rfl, ← BitVec.ofNat_add]

theorem set_half_mem {a b : MachineState} (same : a.mem = b.mem) (addr : Word) (v : BitVec 16) :
    (a.setHalfword addr v).mem = (b.setHalfword addr v).mem := by
  simp only [MachineState.setHalfword, MachineState.setMem, MachineState.getMem, same]

theorem get_half_mem {a b : MachineState} (same : a.mem = b.mem) (addr : Word) :
    a.getHalfword addr = b.getHalfword addr := by
  simp only [MachineState.getHalfword, MachineState.getMem, same]

theorem trial_head (s : MachineState) {u g claim : Nat} (ready : TrialReady s u g claim) (hu : u < 512) :
    Hop s (trialHead s) 8 8 ∧ (trialHead s).pc = spc 1190 ∧
      (trialHead s).mem = (s.setHalfword (topHalf u) (patchHalf (s.getHalfword (topHalf u)) (BitVec.ofNat 64 g))).mem ∧
      (trialHead s).getReg .x6 = BitVec.ofNat 64 u ∧
      ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → (trialHead s).getReg r = s.getReg r := by
  let s1 := execInstrBr s (.SLLI .x7 .x18 5)
  let s2 := execInstrBr s1 (.ADD .x7 .x25 .x7)
  let s3 := execInstrBr s2 (.LHU .x28 .x7 28)
  let s4 := execInstrBr s3 (.ANDI .x28 .x28 63)
  let s5 := execInstrBr s4 (.SLLI .x29 .x19 6)
  let s6 := execInstrBr s5 (.OR .x28 .x28 .x29)
  let s7 := execInstrBr s6 (.SH .x7 .x28 28)
  have p1 : s1.pc = spc 1183 := by rw [straight_pc _ _ (by rfl), ready.pc]; decide
  have p2 : s2.pc = spc 1184 := by rw [straight_pc _ _ (by rfl), p1]; decide
  have p3 : s3.pc = spc 1185 := by rw [straight_pc _ _ (by rfl), p2]; decide
  have p4 : s4.pc = spc 1186 := by rw [straight_pc _ _ (by rfl), p3]; decide
  have p5 : s5.pc = spc 1187 := by rw [straight_pc _ _ (by rfl), p4]; decide
  have p6 : s6.pc = spc 1188 := by rw [straight_pc _ _ (by rfl), p5]; decide
  have p7 : s7.pc = spc 1189 := by rw [straight_pc _ _ (by rfl), p6]; decide
  have x7 : s2.getReg .x7 = BitVec.ofNat 64 (16384+32*u) := by
    have e : s2.getReg .x7 = s.getReg .x25 + (s.getReg .x18 <<< (5 : BitVec 6).toNat) := by
      simp [s2, s1, execInstrBr, reg_setReg]
    rw [e, ready.roots, ready.node, slot_base u hu]
  have addr2 : s2.getReg .x7 + signExtend12 28 = topHalf u := by rw [x7, top_half_addr u hu]
  have keep7 (t : MachineState) (e : t.getReg .x7 = s2.getReg .x7) : t.getReg .x7 + signExtend12 28 = topHalf u := by
    rw [e, addr2]
  have x7_6 : s6.getReg .x7 = s2.getReg .x7 := by simp [s6, s5, s4, s3, execInstrBr, reg_setReg]
  have m6 : s6.mem = s.mem := rfl
  have valid : accessValid (topHalf u) 2 = true := access_ofNat _ 2 (by unfold MEMORY_BYTES; omega) (by omega)
  have a1 := search_step s 1182 _ ready.pc (by decide) searchCode1182 rfl rfl
  have a2 := search_step s1 1183 _ p1 (by decide) searchCode1183 rfl rfl
  have a3 := search_step s2 1184 _ p2 (by decide) searchCode1184 rfl (by
    simp only [memoryArgumentsValid, memAccess, addr2]; exact valid)
  have a4 := search_step s3 1185 _ p3 (by decide) searchCode1185 rfl rfl
  have a5 := search_step s4 1186 _ p4 (by decide) searchCode1186 rfl rfl
  have a6 := search_step s5 1187 _ p5 (by decide) searchCode1187 rfl rfl
  have a7 := search_step s6 1188 _ p6 (by decide) searchCode1188 rfl (by
    simp only [memoryArgumentsValid, memAccess, keep7 s6 x7_6]; exact valid)
  have a8 := search_step s7 1189 _ p7 (by decide) searchCode1189 rfl rfl
  have x28 : s6.getReg .x28 =
      ((s.getHalfword (topHalf u)).zeroExtend 64 &&& signExtend12 63) ||| (BitVec.ofNat 64 g <<< (6 : BitVec 6).toNat) := by
    have e : s6.getReg .x28 = ((s2.getHalfword (s2.getReg .x7 + signExtend12 28)).zeroExtend 64 &&& signExtend12 63) |||
        (s.getReg .x19 <<< (6 : BitVec 6).toNat) := by
      simp [s6, s5, s4, s3, execInstrBr, reg_setReg]
      simp [s2, s1, execInstrBr, reg_setReg]
    rw [e, addr2, get_half_mem (show s2.mem = s.mem from rfl), ready.trial]
  refine ⟨((((((a1.thenDo a2).thenDo a3).thenDo a4).thenDo a5).thenDo a6).thenDo a7).thenDo a8,
    by show (execInstrBr s7 (.ADDI .x6 .x18 0)).pc = _; rw [straight_pc _ _ (by rfl), p7]; decide, ?_, ?_, ?_⟩
  · show (execInstrBr s7 _).mem = _
    show (s6.setHalfword (s6.getReg .x7 + signExtend12 28) ((s6.getReg .x28).truncate 16)).mem = _
    rw [keep7 s6 x7_6, x28, set_half_mem m6]
    rfl
  · show (execInstrBr s7 (.ADDI .x6 .x18 0)).getReg .x6 = _
    have e : s7.getReg .x18 = s.getReg .x18 := by
      simp [s7, s6, s5, s4, s3, s2, s1, execInstrBr, reg_setReg, MachineState.setHalfword]
    simp [execInstrBr, reg_setReg, e, ready.node]
  · intro r a b c d
    simp [trialHead, execInstrBr, reg_setReg, MachineState.setHalfword, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

end TwoPermutationPrototype.Packed.Checker
