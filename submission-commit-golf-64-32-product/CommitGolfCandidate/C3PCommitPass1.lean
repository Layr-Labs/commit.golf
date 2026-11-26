import CommitGolfCandidate.C3PCommitFetch
import CommitGolfCandidate.C3CommitMemory
import CommitGolfCandidate.TwoPermutationOpeningBlocks

/-! # Pass 1 of the paired commit: three compressions per leaf, in place

For the pair with even leaf at message word `E` and odd leaf at `O = E + 32`, entered with
`a0 = E - 32` (word):

* `addi a0,a0,448 ; addi a2,a0,32 ; ecall`: `r_e = C(v_e[192..256))` at `E + 28`;
* `addi a0,a0,-192 ; addi a2,a0,192 ; ecall`: `q_e = C(v_e[0..64))` at `E + 24`;
* `addi a0,a0,192 ; ecall`: `z_e = C(q_e ‖ r_e)` at `E + 24`;
* `addi a0,a0,64 ; addi a2,a0,0 ; ecall`: `q_o = C(v_o[0..64))` at `O`;
* `addi a0,a0,192 ; addi a2,a0,-160 ; ecall`: `r_o = C(v_o[192..256))` at `O + 4`;
* `addi a0,a0,-192 ; ecall`: `z_o = C(q_o ‖ r_o)` at `O + 4`.

16 steps, 58 cycles, 6 calls; `a0` ends at `O`, the next pair's `E - 32`. -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.C3Leaves (execute_compression_on compression_write_memory address_up
  address_down addi_mem addi_pc)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000
attribute [local irreducible] execute packedWideCommitImage

theorem cpc_next (k : Nat) : cpc k + 4 = cpc (k + 1) := by
  unfold cpc
  rw [show (4 : Word) = BitVec.ofNat 64 4 by rfl, ← BitVec.ofNat_add]
  show BitVec.ofNat 64 _ = BitVec.ofNat 64 _
  congr 1

theorem charge_charge (r : Execution) (a b c d : Nat) : (r.charge a b).charge c d = r.charge (c + a) (d + b) := by
  simp only [Execution.charge, Nat.add_assoc]

theorem ordinary_c (st next : MachineState) (instr : Instr) (fuel : Nat)
    (fetched : fetch packedWideCommitImage st = some (.base instr)) (stepped : ordinaryStep st (.base instr) = some next)
    (unit : instructionCycles (.base instr) = 1) :
    execute packedWideCommitImage (1 + fuel) st true =
      (do let result ← execute packedWideCommitImage fuel next true; return result.charge 1 0) := by
  rw [Nat.add_comm 1 fuel, CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fetched stepped, unit]

/-! ### Two kinds of segments, on abstract states -/

/-- `addi a0,a0,i1 ; addi a2,a0,i2`. -/
def seg2 (t : MachineState) (i1 i2 : BitVec 12) : MachineState :=
  execInstrBr (execInstrBr t (.ADDI .x10 .x10 i1)) (.ADDI .x12 .x10 i2)

/-- `addi a0,a0,i1`. -/
def seg1 (t : MachineState) (i1 : BitVec 12) : MachineState := execInstrBr t (.ADDI .x10 .x10 i1)

theorem seg2_facts (t : MachineState) (i1 i2 : BitVec 12) :
    (seg2 t i1 i2).getReg .x10 = t.getReg .x10 + signExtend12 i1 ∧
    (seg2 t i1 i2).getReg .x12 = t.getReg .x10 + signExtend12 i1 + signExtend12 i2 ∧
    (seg2 t i1 i2).mem = t.mem ∧ (seg2 t i1 i2).pc = t.pc + 4 + 4 ∧
    ∀ g, g ≠ .x10 → g ≠ .x12 → (seg2 t i1 i2).getReg g = t.getReg g := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · simp only [seg2, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC, reduceCtorEq, false_and,
      true_and, ne_eq, not_false_eq_true, ↓reduceIte, and_self]
  · simp only [seg2, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC, reduceCtorEq, false_and,
      true_and, ne_eq, not_false_eq_true, ↓reduceIte, and_self]
  · rw [seg2, addi_mem, addi_mem]
  · intro g a b
    simp [seg2, execInstrBr, Opening.getReg_setReg, Ne.symm a, Ne.symm b]

theorem seg1_facts (t : MachineState) (i1 : BitVec 12) :
    (seg1 t i1).getReg .x10 = t.getReg .x10 + signExtend12 i1 ∧
    (seg1 t i1).mem = t.mem ∧ (seg1 t i1).pc = t.pc + 4 ∧
    ∀ g, g ≠ .x10 → (seg1 t i1).getReg g = t.getReg g := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp only [seg1, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC, reduceCtorEq, false_and,
      true_and, ne_eq, not_false_eq_true, ↓reduceIte, and_self]
  · rw [seg1, addi_mem]
  · intro g a
    simp [seg1, execInstrBr, Opening.getReg_setReg, Ne.symm a]

theorem run_seg2 (t : MachineState) (k : Nat) (i1 i2 : BitVec 12) (X : Nat) (pc : t.pc = cpc k)
    (f1 : ∀ u : MachineState, u.pc = cpc k → fetch packedWideCommitImage u = some (.base (.ADDI .x10 .x10 i1)))
    (f2 : ∀ u : MachineState, u.pc = cpc (k + 1) →
      fetch packedWideCommitImage u = some (.base (.ADDI .x12 .x10 i2))) :
    execute packedWideCommitImage (2 + X) t true =
      (do let r ← execute packedWideCommitImage X (seg2 t i1 i2) true; return r.charge 2 0) := by
  let m := execInstrBr t (.ADDI .x10 .x10 i1)
  have mpc : m.pc = cpc (k + 1) := by rw [addi_pc, pc, cpc_next]
  rw [show 2 + X = 1 + (1 + X) by omega,
    ordinary_c t m _ _ (f1 t pc) rfl rfl, ordinary_c m (seg2 t i1 i2) _ _ (f2 m mpc) rfl rfl]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]

theorem run_seg1 (t : MachineState) (k : Nat) (i1 : BitVec 12) (X : Nat) (pc : t.pc = cpc k)
    (f1 : ∀ u : MachineState, u.pc = cpc k → fetch packedWideCommitImage u = some (.base (.ADDI .x10 .x10 i1))) :
    execute packedWideCommitImage (1 + X) t true =
      (do let r ← execute packedWideCommitImage X (seg1 t i1) true; return r.charge 1 0) := by
  exact ordinary_c t (seg1 t i1) _ _ (f1 t pc) rfl rfl

/-! ### One pair -/

/-- The state after one pair's pass 1, given the six compression answers. -/
def p1s1 (s : MachineState) : MachineState := seg2 s 448 32
def p1w1 (s : MachineState) (E : Nat) (a1 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState := writeBits (p1s1 s) (wordAddress (E + 28)) a1
def p1s2 (s : MachineState) (E : Nat) (a1 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState := seg2 (p1w1 s E a1) 3904 192
def p1w2 (s : MachineState) (E : Nat) (a1 a2 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState :=
  writeBits (p1s2 s E a1) (wordAddress (E + 24)) a2
def p1s3 (s : MachineState) (E : Nat) (a1 a2 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState := seg1 (p1w2 s E a1 a2) 192
def p1w3 (s : MachineState) (E : Nat) (a1 a2 a3 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState :=
  writeBits (p1s3 s E a1 a2) (wordAddress (E + 24)) a3
def p1s4 (s : MachineState) (E : Nat) (a1 a2 a3 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState := seg2 (p1w3 s E a1 a2 a3) 64 0
def p1w4 (s : MachineState) (E : Nat) (a1 a2 a3 a4 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState :=
  writeBits (p1s4 s E a1 a2 a3) (wordAddress (E + 32)) a4
def p1s5 (s : MachineState) (E : Nat) (a1 a2 a3 a4 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState := seg2 (p1w4 s E a1 a2 a3 a4) 192 3936
def p1w5 (s : MachineState) (E : Nat) (a1 a2 a3 a4 a5 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState :=
  writeBits (p1s5 s E a1 a2 a3 a4) (wordAddress (E + 36)) a5
def p1s6 (s : MachineState) (E : Nat) (a1 a2 a3 a4 a5 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState := seg1 (p1w5 s E a1 a2 a3 a4 a5) 3904
def p1w6 (s : MachineState) (E : Nat) (a1 a2 a3 a4 a5 a6 : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState :=
  writeBits (p1s6 s E a1 a2 a3 a4 a5) (wordAddress (E + 36)) a6

/-- One pair's pass 1 as an oracle computation; the queries read the states above. -/
def p1PairTrace (s : MachineState) (E : Nat) : OracleComp World MachineState := do
  let a1 ← World.query (.inr (.inl (readBuffer (p1s1 s) (8 * (E + 24)) 64)))
  let a2 ← World.query (.inr (.inl (readBuffer (p1s2 s E a1) (8 * E) 64)))
  let a3 ← World.query (.inr (.inl (readBuffer (p1s3 s E a1 a2) (8 * (E + 24)) 64)))
  let a4 ← World.query (.inr (.inl (readBuffer (p1s4 s E a1 a2 a3) (8 * (E + 32)) 64)))
  let a5 ← World.query (.inr (.inl (readBuffer (p1s5 s E a1 a2 a3 a4) (8 * (E + 56)) 64)))
  let a6 ← World.query (.inr (.inl (readBuffer (p1s6 s E a1 a2 a3 a4 a5) (8 * (E + 32)) 64)))
  return p1w6 s E a1 a2 a3 a4 a5 a6

structure P1PairReady (s : MachineState) (p E : Nat) : Prop where
  pc : s.pc = cpc (p1Index p)
  source : s.getReg .x10 = wordAddress (E - 32)
  low : 32 ≤ E
  bound : E + 64 ≤ 2 ^ 33
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0
  pair : p < 1024

private theorem imm448 : signExtend12 (448 : BitVec 12) = BitVec.ofNat 64 (8 * 56) := by decide
private theorem imm32 : signExtend12 (32 : BitVec 12) = BitVec.ofNat 64 (8 * 4) := by decide
private theorem imm192 : signExtend12 (192 : BitVec 12) = BitVec.ofNat 64 (8 * 24) := by decide
private theorem imm64 : signExtend12 (64 : BitVec 12) = BitVec.ofNat 64 (8 * 8) := by decide
private theorem imm0 : signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 (8 * 0) := by decide
private theorem immm192 : signExtend12 (3904 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 24) := by decide
private theorem immm160 : signExtend12 (3936 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 20) := by decide

/-- Registers and pc of every intermediate state, for every answer. -/
theorem p1_pair_regs (s : MachineState) (p E : Nat) (r : P1PairReady s p E) (a1 a2 a3 a4 a5 a6 : BitVec COMPRESSION_OUTPUT_LENGTH) :
    (p1s1 s).getReg .x10 = wordAddress (E + 24) ∧ (p1s1 s).getReg .x12 = wordAddress (E + 28) ∧
    (p1s2 s E a1).getReg .x10 = wordAddress E ∧ (p1s2 s E a1).getReg .x12 = wordAddress (E + 24) ∧
    (p1s3 s E a1 a2).getReg .x10 = wordAddress (E + 24) ∧ (p1s3 s E a1 a2).getReg .x12 = wordAddress (E + 24) ∧
    (p1s4 s E a1 a2 a3).getReg .x10 = wordAddress (E + 32) ∧
    (p1s4 s E a1 a2 a3).getReg .x12 = wordAddress (E + 32) ∧
    (p1s5 s E a1 a2 a3 a4).getReg .x10 = wordAddress (E + 56) ∧
    (p1s5 s E a1 a2 a3 a4).getReg .x12 = wordAddress (E + 36) ∧
    (p1s6 s E a1 a2 a3 a4 a5).getReg .x10 = wordAddress (E + 32) ∧
    (p1s6 s E a1 a2 a3 a4 a5).getReg .x12 = wordAddress (E + 36) ∧
    (p1w6 s E a1 a2 a3 a4 a5 a6).getReg .x10 = wordAddress (E + 32) ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 →
      (p1s1 s).getReg g = s.getReg g ∧ (p1s2 s E a1).getReg g = s.getReg g ∧
      (p1s3 s E a1 a2).getReg g = s.getReg g ∧ (p1s4 s E a1 a2 a3).getReg g = s.getReg g ∧
      (p1s5 s E a1 a2 a3 a4).getReg g = s.getReg g ∧ (p1s6 s E a1 a2 a3 a4 a5).getReg g = s.getReg g ∧
      (p1w6 s E a1 a2 a3 a4 a5 a6).getReg g = s.getReg g) ∧
    (p1s1 s).pc = cpc (p1Index p + 2) ∧ (p1s2 s E a1).pc = cpc (p1Index p + 5) ∧
    (p1s3 s E a1 a2).pc = cpc (p1Index p + 7) ∧ (p1s4 s E a1 a2 a3).pc = cpc (p1Index p + 10) ∧
    (p1s5 s E a1 a2 a3 a4).pc = cpc (p1Index p + 13) ∧ (p1s6 s E a1 a2 a3 a4 a5).pc = cpc (p1Index p + 15) ∧
    (p1w6 s E a1 a2 a3 a4 a5 a6).pc = cpc (p1Index (p + 1)) := by
  have low := r.low
  have wr (t : MachineState) (d : Word) (a : BitVec COMPRESSION_OUTPUT_LENGTH) (g : Reg) : (writeBits t d a).getReg g = t.getReg g :=
    CommitGolfCandidate.writeBits_register _ _ _ _
  have wpc (t : MachineState) (d : Word) (a : BitVec COMPRESSION_OUTPUT_LENGTH) : (writeBits t d a).pc = t.pc + 4 :=
    by simp only [writeBits, MachineState.setPC]
  obtain ⟨s1x10, s1x12, _, s1pc, s1k⟩ := seg2_facts s 448 32
  have v1 : (p1s1 s).getReg .x10 = wordAddress (E + 24) := by
    rw [p1s1, s1x10, r.source, imm448, address_up]; congr 1; omega
  have v1' : (p1s1 s).getReg .x12 = wordAddress (E + 28) := by
    rw [p1s1, s1x12, r.source, imm448, address_up, imm32, address_up]; congr 1; omega
  obtain ⟨s2x10, s2x12, _, s2pc, s2k⟩ := seg2_facts (p1w1 s E a1) 3904 192
  have v2 : (p1s2 s E a1).getReg .x10 = wordAddress E := by
    rw [p1s2, s2x10, p1w1, wr, v1, address_down _ 24 3904 immm192 (by omega) (by norm_num)]; congr 1
  have v2' : (p1s2 s E a1).getReg .x12 = wordAddress (E + 24) := by
    rw [p1s2, s2x12, p1w1, wr, v1, address_down _ 24 3904 immm192 (by omega) (by norm_num), imm192, address_up]
    congr 1 <;> omega
  obtain ⟨s3x10, _, s3pc, s3k⟩ := seg1_facts (p1w2 s E a1 a2) 192
  have v3 : (p1s3 s E a1 a2).getReg .x10 = wordAddress (E + 24) := by
    rw [p1s3, s3x10, p1w2, wr, v2, imm192, address_up]
  have v3' : (p1s3 s E a1 a2).getReg .x12 = wordAddress (E + 24) := by
    rw [p1s3, s3k .x12 (by decide), p1w2, wr, v2']
  obtain ⟨s4x10, s4x12, _, s4pc, s4k⟩ := seg2_facts (p1w3 s E a1 a2 a3) 64 0
  have v4 : (p1s4 s E a1 a2 a3).getReg .x10 = wordAddress (E + 32) := by
    rw [p1s4, s4x10, p1w3, wr, v3, imm64, address_up]
  have v4' : (p1s4 s E a1 a2 a3).getReg .x12 = wordAddress (E + 32) := by
    rw [p1s4, s4x12, p1w3, wr, v3, imm64, address_up, imm0, address_up]
  obtain ⟨s5x10, s5x12, _, s5pc, s5k⟩ := seg2_facts (p1w4 s E a1 a2 a3 a4) 192 3936
  have v5 : (p1s5 s E a1 a2 a3 a4).getReg .x10 = wordAddress (E + 56) := by
    rw [p1s5, s5x10, p1w4, wr, v4, imm192, address_up]
  have v5' : (p1s5 s E a1 a2 a3 a4).getReg .x12 = wordAddress (E + 36) := by
    rw [p1s5, s5x12, p1w4, wr, v4, imm192, address_up, address_down _ 20 3936 immm160 (by omega) (by norm_num)]
    congr 1
  obtain ⟨s6x10, _, s6pc, s6k⟩ := seg1_facts (p1w5 s E a1 a2 a3 a4 a5) 3904
  have v6 : (p1s6 s E a1 a2 a3 a4 a5).getReg .x10 = wordAddress (E + 32) := by
    rw [p1s6, s6x10, p1w5, wr, v5, address_down _ 24 3904 immm192 (by omega) (by norm_num)]
    congr 1
  have v6' : (p1s6 s E a1 a2 a3 a4 a5).getReg .x12 = wordAddress (E + 36) := by
    rw [p1s6, s6k .x12 (by decide), p1w5, wr, v5']
  have pc1 : (p1s1 s).pc = cpc (p1Index p + 2) := by
    rw [p1s1, s1pc, r.pc, cpc_next, cpc_next]
  have pc2 : (p1s2 s E a1).pc = cpc (p1Index p + 5) := by
    rw [p1s2, s2pc, p1w1, wpc, pc1, cpc_next, cpc_next, cpc_next]
  have pc3 : (p1s3 s E a1 a2).pc = cpc (p1Index p + 7) := by
    rw [p1s3, s3pc, p1w2, wpc, pc2, cpc_next, cpc_next]
  have pc4 : (p1s4 s E a1 a2 a3).pc = cpc (p1Index p + 10) := by
    rw [p1s4, s4pc, p1w3, wpc, pc3, cpc_next, cpc_next, cpc_next]
  have pc5 : (p1s5 s E a1 a2 a3 a4).pc = cpc (p1Index p + 13) := by
    rw [p1s5, s5pc, p1w4, wpc, pc4, cpc_next, cpc_next, cpc_next]
  have pc6 : (p1s6 s E a1 a2 a3 a4 a5).pc = cpc (p1Index p + 15) := by
    rw [p1s6, s6pc, p1w5, wpc, pc5, cpc_next, cpc_next]
  refine ⟨v1, v1', v2, v2', v3, v3', v4, v4', v5, v5', v6, v6', by rw [p1w6, wr, v6], ?_, pc1, pc2, pc3, pc4, pc5,
    pc6, ?_⟩
  · intro g a b
    have k1 : (p1s1 s).getReg g = s.getReg g := by rw [p1s1, s1k g a b]
    have k2 : (p1s2 s E a1).getReg g = s.getReg g := by rw [p1s2, s2k g a b, p1w1, wr, k1]
    have k3 : (p1s3 s E a1 a2).getReg g = s.getReg g := by rw [p1s3, s3k g a, p1w2, wr, k2]
    have k4 : (p1s4 s E a1 a2 a3).getReg g = s.getReg g := by rw [p1s4, s4k g a b, p1w3, wr, k3]
    have k5 : (p1s5 s E a1 a2 a3 a4).getReg g = s.getReg g := by rw [p1s5, s5k g a b, p1w4, wr, k4]
    have k6 : (p1s6 s E a1 a2 a3 a4 a5).getReg g = s.getReg g := by rw [p1s6, s6k g a, p1w5, wr, k5]
    exact ⟨k1, k2, k3, k4, k5, k6, by rw [p1w6, wr, k6]⟩
  · rw [p1w6, wpc, pc6, cpc_next]
    congr 1 <;> (unfold p1Index; omega)

theorem p1w1_eq (s : MachineState) (E : Nat) (a1 : BitVec COMPRESSION_OUTPUT_LENGTH) :
    writeBits (p1s1 s) (wordAddress (E + 28)) a1 = p1w1 s E a1 := rfl
theorem p1w2_eq (s : MachineState) (E : Nat) (a1 a2 : BitVec COMPRESSION_OUTPUT_LENGTH) :
    writeBits (p1s2 s E a1) (wordAddress (E + 24)) a2 = p1w2 s E a1 a2 := rfl
theorem p1w3_eq (s : MachineState) (E : Nat) (a1 a2 a3 : BitVec COMPRESSION_OUTPUT_LENGTH) :
    writeBits (p1s3 s E a1 a2) (wordAddress (E + 24)) a3 = p1w3 s E a1 a2 a3 := rfl
theorem p1w4_eq (s : MachineState) (E : Nat) (a1 a2 a3 a4 : BitVec COMPRESSION_OUTPUT_LENGTH) :
    writeBits (p1s4 s E a1 a2 a3) (wordAddress (E + 32)) a4 = p1w4 s E a1 a2 a3 a4 := rfl
theorem p1w5_eq (s : MachineState) (E : Nat) (a1 a2 a3 a4 a5 : BitVec COMPRESSION_OUTPUT_LENGTH) :
    writeBits (p1s5 s E a1 a2 a3 a4) (wordAddress (E + 36)) a5 = p1w5 s E a1 a2 a3 a4 a5 := rfl
theorem p1w6_eq (s : MachineState) (E : Nat) (a1 a2 a3 a4 a5 a6 : BitVec COMPRESSION_OUTPUT_LENGTH) :
    writeBits (p1s6 s E a1 a2 a3 a4 a5) (wordAddress (E + 36)) a6 = p1w6 s E a1 a2 a3 a4 a5 a6 := rfl

theorem p1_w_pcs (s : MachineState) (p E : Nat) (r : P1PairReady s p E) (a1 a2 a3 a4 a5 : BitVec COMPRESSION_OUTPUT_LENGTH) :
    (p1w1 s E a1).pc = cpc (p1Index p + 3) ∧ (p1w2 s E a1 a2).pc = cpc (p1Index p + 6) ∧
    (p1w3 s E a1 a2 a3).pc = cpc (p1Index p + 8) ∧ (p1w4 s E a1 a2 a3 a4).pc = cpc (p1Index p + 11) ∧
    (p1w5 s E a1 a2 a3 a4 a5).pc = cpc (p1Index p + 14) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, pc1, pc2, pc3, pc4, pc5, _, _⟩ :=
    p1_pair_regs s p E r a1 a2 a3 a4 a5 0
  have wpc (t : MachineState) (d : Word) (a : BitVec COMPRESSION_OUTPUT_LENGTH) : (writeBits t d a).pc = t.pc + 4 :=
    by simp only [writeBits, MachineState.setPC]
  exact ⟨by rw [p1w1, wpc, pc1, cpc_next], by rw [p1w2, wpc, pc2, cpc_next], by rw [p1w3, wpc, pc3, cpc_next],
    by rw [p1w4, wpc, pc4, cpc_next], by rw [p1w5, wpc, pc5, cpc_next]⟩

attribute [local irreducible] p1w1 p1w2 p1w3 p1w4 p1w5 p1w6

theorem execute_p1_pair (s : MachineState) (p E : Nat) (r : P1PairReady s p E) (fuel : Nat) :
    execute packedWideCommitImage (16 + fuel) s true =
      (do let t ← p1PairTrace s E
          let res ← execute packedWideCommitImage fuel t true
          return res.charge 58 6) := by
  have hp := r.pair
  have low := r.low
  have bd := r.bound
  have F (k : Nat) (hk : k < 16) (u : MachineState) (h : u.pc = cpc (p1Index p + k)) :
      fetch packedWideCommitImage u = some (.base (opAt p1Ops k)) := fetch_p1 p hp k hk u h
  have R := p1_pair_regs s p E r
  have WP := p1_w_pcs s p E r
  have sel (g : Reg) (hg : g ≠ .x10 ∧ g ≠ .x12) (a1 a2 a3 a4 a5 : BitVec COMPRESSION_OUTPUT_LENGTH) :=
    (R a1 a2 a3 a4 a5 0).2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg.1 hg.2
  -- segment 1 and call 1
  rw [show 16 + fuel = 2 + ((13 + fuel) + 1) by omega,
    run_seg2 s (p1Index p) 448 32 _ r.pc (F 0 (by decide)) (fun u h => F 1 (by decide) u (by rw [h]))]
  rw [show seg2 s 448 32 = p1s1 s from rfl,
    execute_compression_on _ (13 + fuel) (p1s1 s) true (E + 24) (E + 28) (by omega) (by omega)
      (R 0 0 0 0 0 0).1 (R 0 0 0 0 0 0).2.1
      (((sel .x5 ⟨by decide, by decide⟩ 0 0 0 0 0).1).trans r.selector)
      (((sel .x11 ⟨by decide, by decide⟩ 0 0 0 0 0).1).trans r.size)
      (((sel .x13 ⟨by decide, by decide⟩ 0 0 0 0 0).1).trans r.primitive)
      (F 2 (by decide) _ (R 0 0 0 0 0 0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)]
  simp only [p1PairTrace, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a1 _
  rw [p1w1_eq]
  -- segment 2 and call 2
  rw [show 13 + fuel = 2 + ((10 + fuel) + 1) by omega,
    run_seg2 (p1w1 s E a1) (p1Index p + 3) 3904 192 _ (WP a1 0 0 0 0).1
      (F 3 (by decide)) (fun u h => F 4 (by decide) u (by rw [h])),
    show seg2 (p1w1 s E a1) 3904 192 = p1s2 s E a1 from rfl,
    execute_compression_on _ (10 + fuel) (p1s2 s E a1) true E (E + 24) (by omega) (by omega)
      (R a1 0 0 0 0 0).2.2.1 (R a1 0 0 0 0 0).2.2.2.1
      (((sel .x5 ⟨by decide, by decide⟩ a1 0 0 0 0).2.1).trans r.selector)
      (((sel .x11 ⟨by decide, by decide⟩ a1 0 0 0 0).2.1).trans r.size)
      (((sel .x13 ⟨by decide, by decide⟩ a1 0 0 0 0).2.1).trans r.primitive)
      (F 5 (by decide) _ (R a1 0 0 0 0 0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a2 _
  rw [p1w2_eq]
  -- segment 3 and call 3
  rw [show 10 + fuel = 1 + ((8 + fuel) + 1) by omega,
    run_seg1 (p1w2 s E a1 a2) (p1Index p + 6) 192 _ (WP a1 a2 0 0 0).2.1 (F 6 (by decide)),
    show seg1 (p1w2 s E a1 a2) 192 = p1s3 s E a1 a2 from rfl,
    execute_compression_on _ (8 + fuel) (p1s3 s E a1 a2) true (E + 24) (E + 24) (by omega) (by omega)
      (R a1 a2 0 0 0 0).2.2.2.2.1 (R a1 a2 0 0 0 0).2.2.2.2.2.1
      (((sel .x5 ⟨by decide, by decide⟩ a1 a2 0 0 0).2.2.1).trans r.selector)
      (((sel .x11 ⟨by decide, by decide⟩ a1 a2 0 0 0).2.2.1).trans r.size)
      (((sel .x13 ⟨by decide, by decide⟩ a1 a2 0 0 0).2.2.1).trans r.primitive)
      (F 7 (by decide) _ (R a1 a2 0 0 0 0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a3 _
  rw [p1w3_eq]
  -- segment 4 and call 4
  rw [show 8 + fuel = 2 + ((5 + fuel) + 1) by omega,
    run_seg2 (p1w3 s E a1 a2 a3) (p1Index p + 8) 64 0 _ (WP a1 a2 a3 0 0).2.2.1
      (F 8 (by decide)) (fun u h => F 9 (by decide) u (by rw [h])),
    show seg2 (p1w3 s E a1 a2 a3) 64 0 = p1s4 s E a1 a2 a3 from rfl,
    execute_compression_on _ (5 + fuel) (p1s4 s E a1 a2 a3) true (E + 32) (E + 32) (by omega) (by omega)
      (R a1 a2 a3 0 0 0).2.2.2.2.2.2.1 (R a1 a2 a3 0 0 0).2.2.2.2.2.2.2.1
      (((sel .x5 ⟨by decide, by decide⟩ a1 a2 a3 0 0).2.2.2.1).trans r.selector)
      (((sel .x11 ⟨by decide, by decide⟩ a1 a2 a3 0 0).2.2.2.1).trans r.size)
      (((sel .x13 ⟨by decide, by decide⟩ a1 a2 a3 0 0).2.2.2.1).trans r.primitive)
      (F 10 (by decide) _ (R a1 a2 a3 0 0 0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a4 _
  rw [p1w4_eq]
  -- segment 5 and call 5
  rw [show 5 + fuel = 2 + ((2 + fuel) + 1) by omega,
    run_seg2 (p1w4 s E a1 a2 a3 a4) (p1Index p + 11) 192 3936 _ (WP a1 a2 a3 a4 0).2.2.2.1
      (F 11 (by decide)) (fun u h => F 12 (by decide) u (by rw [h])),
    show seg2 (p1w4 s E a1 a2 a3 a4) 192 3936 = p1s5 s E a1 a2 a3 a4 from rfl,
    execute_compression_on _ (2 + fuel) (p1s5 s E a1 a2 a3 a4) true (E + 56) (E + 36) (by omega) (by omega)
      (R a1 a2 a3 a4 0 0).2.2.2.2.2.2.2.2.1 (R a1 a2 a3 a4 0 0).2.2.2.2.2.2.2.2.2.1
      (((sel .x5 ⟨by decide, by decide⟩ a1 a2 a3 a4 0).2.2.2.2.1).trans r.selector)
      (((sel .x11 ⟨by decide, by decide⟩ a1 a2 a3 a4 0).2.2.2.2.1).trans r.size)
      (((sel .x13 ⟨by decide, by decide⟩ a1 a2 a3 a4 0).2.2.2.2.1).trans r.primitive)
      (F 13 (by decide) _ (R a1 a2 a3 a4 0 0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a5 _
  rw [p1w5_eq]
  -- segment 6 and call 6
  rw [show 2 + fuel = 1 + (fuel + 1) by omega,
    run_seg1 (p1w5 s E a1 a2 a3 a4 a5) (p1Index p + 14) 3904 _ (WP a1 a2 a3 a4 a5).2.2.2.2 (F 14 (by decide)),
    show seg1 (p1w5 s E a1 a2 a3 a4 a5) 3904 = p1s6 s E a1 a2 a3 a4 a5 from rfl,
    execute_compression_on _ fuel (p1s6 s E a1 a2 a3 a4 a5) true (E + 32) (E + 36) (by omega) (by omega)
      (R a1 a2 a3 a4 a5 0).2.2.2.2.2.2.2.2.2.2.1 (R a1 a2 a3 a4 a5 0).2.2.2.2.2.2.2.2.2.2.2.1
      (((sel .x5 ⟨by decide, by decide⟩ a1 a2 a3 a4 a5).2.2.2.2.2.1).trans r.selector)
      (((sel .x11 ⟨by decide, by decide⟩ a1 a2 a3 a4 a5).2.2.2.2.2.1).trans r.size)
      (((sel .x13 ⟨by decide, by decide⟩ a1 a2 a3 a4 a5).2.2.2.2.2.1).trans r.primitive)
      (F 15 (by decide) _ (R a1 a2 a3 a4 a5 0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a6 _
  rw [p1w6_eq]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]

end TwoPermutationPrototype.RV64.C3P
