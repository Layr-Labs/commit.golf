import CommitGolfCandidate.MoonOpenCode
import CommitGolfCandidate.MoonMemory

/-! Core symbolic execution engine, word32 memory semantics, 64-bit tail-packer algebra,
single-instruction step lemmas, and universal parameterized block lemmas (`dwords`, `copy30`,
`copy29`, negative-counter `tailMerge`/`tailPush6`) for the fast opening program. -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

/-! ### 1. Program Counter, Trapdoor Views, CleanTrapdoor, and Deterministic Multi-Step Relation -/

def pcAt (idx : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * idx)

def tdNode (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (l idx : Nat) : Digest :=
  trapdoor.extractLsb' (8 * (levelBase l + nodeOffset l idx)) 256

def tdSalt (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) : Salt192 :=
  trapdoor.extractLsb' (8 * saltOff i) 192

/-- Cleanliness invariant satisfied by every honestly committed trapdoor (`L2..L5` 240-bit clean,
`L6..L23` 238-bit clean). Only needed for output byte equality; termination, exit status, proof
length, and cycle bounds hold unconditionally for arbitrary trapdoors. -/
def CleanTrapdoor (trapdoor : BitVec (8 * submission.sizes.trapdoor)) : Prop :=
  (∀ l, 2 ≤ l → l ≤ 5 → ∀ idx < levelSize l, mask240 (tdNode trapdoor l idx) = tdNode trapdoor l idx) ∧
  (∀ l, 6 ≤ l → l ≤ 23 → ∀ idx < levelSize l, mask238 (tdNode trapdoor l idx) = tdNode trapdoor l idx)

theorem CommittedTrapdoor.clean {h768 : COMPRESSION_INPUT_LENGTH = 768} {c : Compression}
    {msg : Message} {salts : Index → Salt192}
    {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    (htd : CommittedTrapdoor h768 c msg salts trapdoor) :
    CleanTrapdoor trapdoor := by
  let c96 : Comp96 := fun x => c (x.cast h768.symm)
  refine ⟨fun l hl1 hl2 idx hidx => ?_, fun l hl1 hl2 idx hidx => ?_⟩
  · have heq : tdNode trapdoor l idx = nodeVal c96 msg salts l idx := htd.1 l (by omega) idx hidx
    rw [heq]
    exact nodeValFromLeaves_masked c96 _ l idx hl1 (by omega) hidx
  · have heq : tdNode trapdoor l idx = nodeVal c96 msg salts l idx := htd.1 l (by omega) idx hidx
    rw [heq]
    exact nodeValFromLeaves_masked238 c96 _ l idx hl1 hl2 hidx

/-- Deterministic multi-step execution of ordinary instructions in `openImage`. -/
def OpenRuns (s : MachineState) (steps cycles : Nat) (s' : MachineState) : Prop :=
  ∀ fuel : Nat,
    execute openImage (steps + fuel) s true =
      (do let result ← execute openImage fuel s' true
          return result.charge cycles 0)

theorem OpenRuns.refl (s : MachineState) : OpenRuns s 0 0 s := by
  intro fuel
  simp [Execution.charge]

theorem OpenRuns.trans {s s1 s2 : MachineState} {n1 n2 c1 c2 : Nat}
    (h1 : OpenRuns s n1 c1 s1) (h2 : OpenRuns s1 n2 c2 s2) :
    OpenRuns s (n1 + n2) (c1 + c2) s2 := by
  intro fuel
  rw [Nat.add_assoc, h1 (n2 + fuel), h2 fuel]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext result
  simp [Execution.charge, Nat.add_assoc]

theorem OpenRuns.step {s s' : MachineState} {instr : Instruction}
    (hf : fetch openImage s = some instr)
    (hs : ordinaryStep s instr = some s') :
    OpenRuns s 1 (instructionCycles instr) s' := by
  intro fuel
  rw [Nat.add_comm 1 fuel]
  exact execute_ordinary_step openImage instr s s' fuel true hf hs

theorem OpenRuns.halt {s0 sHalt : MachineState} {haltIdx steps cycles totalFuel : Nat}
    (hrun : OpenRuns s0 steps cycles sHalt)
    (hhi : haltIdx < OPEN_CODE_LEN)
    (hi : openInstr haltIdx = .base .ECALL)
    (hpc : sHalt.pc = pcAt haltIdx)
    (hx5 : sHalt.getReg .x5 = 1#64)
    (hx10 : sHalt.getReg .x10 = 0#64)
    (hfuel : steps + 1 ≤ totalFuel) :
    execute openImage totalFuel s0 true =
      pure { exit := .success, state := sHalt, cycles := cycles + 1, oracleCalls := 0 } := by
  have hf : fetch openImage sHalt = some (.base .ECALL) := by
    rw [open_fetch sHalt haltIdx hhi hpc, hi]
  obtain ⟨extra, rfl⟩ : ∃ extra, totalFuel = steps + (extra + 1) :=
    ⟨totalFuel - (steps + 1), by omega⟩
  rw [hrun (extra + 1)]
  have hne0 : ¬ (sHalt.getReg .x5 = (0 : Word)) := by rw [hx5]; decide
  have heq1 : sHalt.getReg .x5 = (1 : Word) := hx5
  have heq0 : sHalt.getReg .x10 = (0 : Word) := hx10
  have h1 : execute openImage (extra + 1) sHalt true =
      pure { exit := .success, state := sHalt, cycles := 1, oracleCalls := 0 } := by
    simp only [execute, hf]
    rw [if_neg hne0, if_pos heq1, if_pos heq0]
  rw [h1, pure_bind]
  rfl

/-! ### 2. MachineState, Word32 Memory, and General BitVec Helpers -/

theorem getReg_setReg_ne' (r r' : Reg) (h : r ≠ r') (s : MachineState) (v : Word) :
    (s.setReg r v).getReg r' = s.getReg r' :=
  MachineState.getReg_setReg_ne s r r' v h

theorem getReg_setMem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

theorem getReg_setByte (s : MachineState) (a : Word) (b : BitVec 8) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by cases r <;> rfl

theorem getReg_setWord32 (s : MachineState) (a : Word) (v : BitVec 32) (r : Reg) :
    (s.setWord32 a v).getReg r = s.getReg r := by cases r <;> rfl

theorem getByte_setReg (s : MachineState) (r : Reg) (v a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setReg]

theorem getByte_setPC (s : MachineState) (v a : Word) :
    (s.setPC v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setPC]

theorem getMem_setWord32_outside (s : MachineState) (addr query : Word) (v : BitVec 32)
    (hne : alignToDword query ≠ alignToDword addr) :
    (s.setWord32 addr v).getMem query = s.getMem query := by
  simp only [MachineState.setWord32]
  have hne' : query ≠ alignToDword addr := by
    intro h; apply hne; rw [h]
    unfold alignToDword
    ext i; simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases (7#64)[i] <;> simp
  exact MachineState.getMem_setMem_ne hne'

private theorem extractByte_replaceWord32_inside (w : Word) (v : BitVec 32)
    (pos j : Nat) (hpos : pos < 2) (hj : j < 4) :
    extractByte (replaceWord32 w pos v) (4 * pos + j) = v.extractLsb' (8 * j) 8 := by
  interval_cases pos <;> interval_cases j <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro b hb <;> interval_cases b <;>
    simp [extractByte, replaceWord32]

private theorem extractByte_replaceWord32_other (w : Word) (v : BitVec 32)
    (pos k : Nat) (hpos : pos < 2) (hk : k < 8)
    (hout : k < 4 * pos ∨ 4 * pos + 4 ≤ k) :
    extractByte (replaceWord32 w pos v) k = extractByte w k := by
  interval_cases pos <;> interval_cases k <;>
    first
    | omega
    | (apply BitVec.eq_of_getLsbD_eq; intro b hb; interval_cases b <;>
       simp [extractByte, replaceWord32])

private theorem byteOffset_eq_mod' (a : Word) : byteOffset a = a.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change a.toNat &&& (2 ^ 3 - 1) = a.toNat % 2 ^ 3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- `SW` at a 4-byte aligned address updates bytes `addr..addr+3` and preserves all other bytes. -/
theorem setWord32_getByte_ofNat (s : MachineState) (addr q : Nat) (v : BitVec 32)
    (halign : addr % 4 = 0) (ha : addr + 4 ≤ 2 ^ 64) (hq : q < 2 ^ 64) :
    (s.setWord32 (BitVec.ofNat 64 addr) v).getByte (BitVec.ofNat 64 q) =
      if h : addr ≤ q ∧ q < addr + 4 then v.extractLsb' (8 * (q - addr)) 8
      else s.getByte (BitVec.ofNat 64 q) := by
  have ha' : addr < 2 ^ 64 := by omega
  have hboA : byteOffset (BitVec.ofNat 64 addr) = addr % 8 := by
    rw [byteOffset_eq_mod', BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha']
  have hboQ : byteOffset (BitVec.ofNat 64 q) = q % 8 := by
    rw [byteOffset_eq_mod', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  have halA : alignToDword (BitVec.ofNat 64 addr) = BitVec.ofNat 64 (8 * (addr / 8)) := by
    have h1 := alignToDword_ofNat_eq (8 * (addr / 8)) (addr % 8) (by omega) (by omega)
    simpa only [show 8 * (addr / 8) + addr % 8 = addr by omega] using h1
  have halQ : alignToDword (BitVec.ofNat 64 q) = BitVec.ofNat 64 (8 * (q / 8)) := by
    have h1 := alignToDword_ofNat_eq (8 * (q / 8)) (q % 8) (by omega) (by omega)
    simpa only [show 8 * (q / 8) + q % 8 = q by omega] using h1
  split_ifs with hin
  · have hsame : q / 8 = addr / 8 := by omega
    have hdw : alignToDword (BitVec.ofNat 64 q) = alignToDword (BitVec.ofNat 64 addr) := by
      rw [halQ, halA, hsame]
    simp only [MachineState.setWord32, MachineState.getByte, hdw, MachineState.getMem_setMem_eq,
      hboA, hboQ]
    have hpos : (addr % 8) / 4 < 2 := by omega
    have hqeq : q % 8 = 4 * ((addr % 8) / 4) + (q - addr) := by omega
    rw [hqeq]
    exact extractByte_replaceWord32_inside _ v _ (q - addr) hpos (by omega)
  · by_cases hsame : q / 8 = addr / 8
    · have hdw : alignToDword (BitVec.ofNat 64 q) = alignToDword (BitVec.ofNat 64 addr) := by
        rw [halQ, halA, hsame]
      simp only [MachineState.setWord32, MachineState.getByte, hdw, MachineState.getMem_setMem_eq,
        hboA, hboQ]
      exact extractByte_replaceWord32_other _ v ((addr % 8) / 4) (q % 8) (by omega) (by omega) (by omega)
    · have hne : alignToDword (BitVec.ofNat 64 q) ≠ alignToDword (BitVec.ofNat 64 addr) := by
        rw [halQ, halA]
        intro heq
        have hn := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 8 * (q / 8) < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 8 * (addr / 8) < 2 ^ 64)] at hn
        omega
      simp only [MachineState.setWord32, MachineState.getByte, MachineState.getMem_setMem_ne hne]

/-- `LWU` at an 8-byte aligned address loads the low 32 bits of the doubleword. -/
theorem getWord32_ofNat_align8 (s : MachineState) (addr : Nat) (halign : addr % 8 = 0)
    (ha : addr < 2 ^ 64) :
    s.getWord32 (BitVec.ofNat 64 addr) = (s.getMem (BitVec.ofNat 64 addr)).truncate 32 := by
  have hbo : byteOffset (BitVec.ofNat 64 addr) = 0 := by
    rw [byteOffset_eq_mod', BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; omega
  have hal : alignToDword (BitVec.ofNat 64 addr) = BitVec.ofNat 64 addr := by
    simpa only [Nat.add_zero] using alignToDword_ofNat_eq addr 0 (by omega) halign
  simp only [MachineState.getWord32, hal, hbo]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp [extractWord32, BitVec.truncate, hb]

theorem truncate32_zeroExtend64 (v : BitVec 32) : (v.zeroExtend 64).truncate 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp [BitVec.truncate, BitVec.zeroExtend, hb]

theorem pcAt_add4 (idx : Nat) : pcAt idx + 4 = pcAt (idx + 1) := by
  unfold pcAt
  change BitVec.ofNat 64 (0x1000 + 4 * idx) + BitVec.ofNat 64 4 = _
  rw [← BitVec.ofNat_add]
  congr 1

theorem bv64_ofNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem bv64_ofNat_sub (a b : Nat) (hle : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have h : BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b = BitVec.ofNat 64 a := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
  have hc := congrArg (fun v : Word => v - BitVec.ofNat 64 b) h.symm
  simpa only [BitVec.add_sub_cancel] using hc

private theorem signExtend_ofNat_nonneg (w k : Nat) (hw : 1 ≤ w) (hw64 : w ≤ 64) (hk : k < 2 ^ (w - 1)) :
    (BitVec.ofNat w k).signExtend 64 = BitVec.ofNat 64 k := by
  have hpow : 2 ^ (w - 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow64 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hw64
  have hmsb : (BitVec.ofNat w k).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ w),
      decide_eq_false_iff_not]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp only [hmsb, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : k < 2 ^ w), Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.add_zero]

private theorem signExtend_ofNat_neg (w k : Nat) (hw : 1 ≤ w) (hw64 : w ≤ 64)
    (hk1 : 0 < k) (hk2 : k ≤ 2 ^ (w - 1)) :
    (BitVec.ofNat w (2 ^ w - k)).signExtend 64 = BitVec.ofNat 64 (2 ^ 64 - k) := by
  have hhalf : 2 ^ w = 2 * 2 ^ (w - 1) := by
    have hw' : w = (w - 1) + 1 := by omega
    conv => lhs; rw [hw']
    rw [Nat.pow_succ, Nat.mul_comm]
  have hpow64 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hw64
  have hmsb : (BitVec.ofNat w (2 ^ w - k)).msb = true := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 2 ^ w - k < 2 ^ w),
      decide_eq_true_eq]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp only [hmsb, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 ^ w - k < 2 ^ w),
    Nat.mod_eq_of_lt (by omega : 2 ^ w - k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 ^ 64 - k < 2 ^ 64)]
  omega

theorem signExtend12_nonneg (k : Nat) (hk : k < 2048) :
    signExtend12 (BitVec.ofNat 12 k) = BitVec.ofNat 64 k :=
  signExtend_ofNat_nonneg 12 k (by omega) (by omega) (by omega)

theorem signExtend12_neg (k : Nat) (hk1 : 0 < k) (hk2 : k ≤ 2048) :
    signExtend12 (BitVec.ofNat 12 (4096 - k)) = BitVec.ofNat 64 (2 ^ 64 - k) :=
  signExtend_ofNat_neg 12 k (by omega) (by omega) hk1 (by omega)

theorem signExtend13_nonneg (k : Nat) (hk : k < 4096) :
    signExtend13 (BitVec.ofNat 13 k) = BitVec.ofNat 64 k :=
  signExtend_ofNat_nonneg 13 k (by omega) (by omega) (by omega)

theorem signExtend13_neg (k : Nat) (hk1 : 0 < k) (hk2 : k ≤ 4096) :
    signExtend13 (BitVec.ofNat 13 (8192 - k)) = BitVec.ofNat 64 (2 ^ 64 - k) :=
  signExtend_ofNat_neg 13 k (by omega) (by omega) hk1 (by omega)

theorem signExtend21_nonneg (k : Nat) (hk : k < 1048576) :
    signExtend21 (BitVec.ofNat 21 k) = BitVec.ofNat 64 k :=
  signExtend_ofNat_nonneg 21 k (by omega) (by omega) (by omega)

theorem signExtend21_neg (k : Nat) (hk1 : 0 < k) (hk2 : k ≤ 1048576) :
    signExtend21 (BitVec.ofNat 21 (2097152 - k)) = BitVec.ofNat 64 (2 ^ 64 - k) :=
  signExtend_ofNat_neg 21 k (by omega) (by omega) hk1 (by omega)

theorem pcAt_add_pos13 (idx tgt : Nat) (h1 : idx ≤ tgt) (h2 : 4 * (tgt - idx) < 4096) :
    pcAt idx + signExtend13 (BitVec.ofNat 13 (4 * (tgt - idx))) = pcAt tgt := by
  rw [signExtend13_nonneg _ h2]
  unfold pcAt
  rw [← BitVec.ofNat_add]
  congr 1; omega

theorem pcAt_add_neg13 (idx tgt : Nat) (h1 : tgt < idx) (h2 : 4 * (idx - tgt) ≤ 4096) :
    pcAt idx + signExtend13 (BitVec.ofNat 13 (8192 - 4 * (idx - tgt))) = pcAt tgt := by
  rw [signExtend13_neg _ (by omega) h2]
  unfold pcAt
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : 0x1000 + 4 * idx + (2 ^ 64 - 4 * (idx - tgt)) = (0x1000 + 4 * tgt) + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

theorem pcAt_add_pos21 (idx tgt : Nat) (h1 : idx ≤ tgt) (h2 : 4 * (tgt - idx) < 1048576) :
    pcAt idx + signExtend21 (BitVec.ofNat 21 (4 * (tgt - idx))) = pcAt tgt := by
  rw [signExtend21_nonneg _ h2]
  unfold pcAt
  rw [← BitVec.ofNat_add]
  congr 1; omega

theorem pcAt_add_neg21 (idx tgt : Nat) (h1 : tgt < idx) (h2 : 4 * (idx - tgt) ≤ 1048576) :
    pcAt idx + signExtend21 (BitVec.ofNat 21 (2097152 - 4 * (idx - tgt))) = pcAt tgt := by
  rw [signExtend21_neg _ (by omega) h2]
  unfold pcAt
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : 0x1000 + 4 * idx + (2 ^ 64 - 4 * (idx - tgt)) = (0x1000 + 4 * tgt) + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

theorem bv64_add_neg (n k : Nat) (hk1 : 0 < k) (hk2 : k ≤ 2048) (hn : k ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (BitVec.ofNat 12 (4096 - k)) = BitVec.ofNat 64 (n - k) := by
  rw [signExtend12_neg k hk1 hk2, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : n + (2 ^ 64 - k) = (n - k) + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

theorem and_not_one_of_even (n : Nat) (heven : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  have hlow : BitVec.ofNat 64 n &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change (n % 2 ^ 64) &&& (2 ^ 1 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]; omega
  have hor : (BitVec.ofNat 64 n &&& ~~~1#64) ||| (BitVec.ofNat 64 n &&& 1#64) =
      BitVec.ofNat 64 n := by
    ext i; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases (1#64 : Word)[i] <;> simp
  simpa only [hlow, BitVec.or_zero] using hor

theorem pcAt_jalr_return (idx : Nat) :
    (pcAt idx + signExtend12 (0#12)) &&& ~~~1#64 = pcAt idx := by
  rw [signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  exact and_not_one_of_even (0x1000 + 4 * idx) (by omega)

theorem bv64_shl (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_mod (a % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod]

theorem bv64_ushr (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a >>> k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem bv64_xor1 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ signExtend12 (1#12) = BitVec.ofNat 64 (a ^^^ 1) := by
  rw [signExtend12_nonneg 1 (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64)]
  have hlt : a ^^^ 1 < 2 ^ 64 := by
    rcases Nat.even_or_odd' a with ⟨q, rfl | rfl⟩
    · rw [xor_one_even]; omega
    · rw [xor_one_odd]; omega
  rw [Nat.mod_eq_of_lt hlt]

theorem bv64_and1 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& signExtend12 (1#12) = BitVec.ofNat 64 (a % 2) := by
  rw [signExtend12_nonneg 1 (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : a % 2 < 2 ^ 64)]
  change a &&& (2 ^ 1 - 1) = a % 2 ^ 1
  exact Nat.and_two_pow_sub_one_eq_mod a 1

theorem bv64_and2 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& signExtend12 (2#12) = BitVec.ofNat 64 (if (a / 2) % 2 = 1 then 2 else 0) := by
  rw [signExtend12_nonneg 2 (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and]
  by_cases hb1 : b = 1
  · subst hb1
    simp only [Nat.testBit_eq_decide_div_mod_eq]
    split_ifs with h <;> simp [h]
  · have h2 : Nat.testBit 2 b = false := by
      simp only [Nat.testBit_eq_decide_div_mod_eq]
      cases b with
      | zero => simp
      | succ b' =>
        cases b' with
        | zero => omega
        | succ b'' =>
          have hpow : 4 ≤ 2 ^ (b'' + 2) := by
            have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (show 2 ≤ b'' + 2 by omega)
            omega
          have hdiv : 2 / 2 ^ (b'' + 2) = 0 := Nat.div_eq_of_lt (by omega)
          simp [hdiv]
    rw [h2, Bool.and_false]
    split_ifs <;> simp [h2]

theorem bv64_ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro heq
  have hn := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hn
  exact hne hn

theorem accessValid_ofNat (a w : Nat) (hle : a + w ≤ 68719476736) (hal : a % w = 0) :
    accessValid (BitVec.ofNat 64 a) w = true := by
  have ha : a < 2 ^ 64 := by omega
  simp only [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, hal⟩

theorem getMem_extractByte {s : MachineState} {addr j : Nat}
    (hal : addr % 8 = 0) (hj : j < 8) :
    (s.getMem (BitVec.ofNat 64 addr)).extractLsb' (8 * j) 8 =
      s.getByte (BitVec.ofNat 64 (addr + j)) := by
  have hd := alignToDword_ofNat_eq addr j hj hal
  have hbo : byteOffset (BitVec.ofNat 64 (addr + j)) = j := by
    rw [byteOffset_eq_mod', BitVec.toNat_ofNat]; omega
  simp only [MachineState.getByte, hd, hbo]
  unfold extractByte
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp [BitVec.truncate, hb, Nat.mul_comm]

theorem extractLsb'_extractLsb' {w : Nat} (x : BitVec w) (a m b k : Nat) (h : b + k ≤ m) :
    (x.extractLsb' a m).extractLsb' b k = x.extractLsb' (a + b) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show b + i < m by omega, Nat.add_assoc]

/-! ### 3. Mask40, Clean240/Clean238, Shift/Byte, Negative Tail Counter, and Pack6 Algebra -/

def mask40Word : Word := BitVec.ofNat 64 (2 ^ 40 - 1)

theorem mask40Word_eq : (1#64 <<< 40) + signExtend12 (4095#12) = mask40Word := by
  rw [show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, bv64_shl, Nat.one_mul]
  exact bv64_add_neg (2 ^ 40) 1 (by omega) (by omega) (by omega)

theorem and_mask40_byte (v : Word) (j : Nat) (hj : j < 8) :
    (v &&& mask40Word).extractLsb' (8 * j) 8 = if j < 5 then v.extractLsb' (8 * j) 8 else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hb, decide_true, Bool.true_and]
  have hm : mask40Word.getLsbD (8 * j + b) = decide (8 * j + b < 40) := by
    unfold mask40Word
    have hlt : 8 * j + b < 64 := by omega
    simp only [BitVec.getLsbD_ofNat, hlt, decide_true, Bool.true_and,
      Nat.testBit_two_pow_sub_one]
  rw [hm]
  by_cases h5 : j < 5
  · rw [if_pos h5, show decide (8 * j + b < 40) = true by simp; omega, Bool.and_true]
    simp [BitVec.getLsbD_extractLsb', hb]
  · rw [if_neg h5, show decide (8 * j + b < 40) = false by simp; omega, Bool.and_false,
      BitVec.getLsbD_zero]

theorem word_or_shl_byte (w v : Word) (r : Nat) (hr : r < 8)
    (hwHi : ∀ j, r ≤ j → j < 8 → w.extractLsb' (8 * j) 8 = 0#8) (j : Nat) (hj : j < 8) :
    (w ||| (v <<< (8 * r))).extractLsb' (8 * j) 8 =
      if j < r then w.extractLsb' (8 * j) 8 else v.extractLsb' (8 * (j - r)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    hb, decide_true, Bool.true_and]
  by_cases hlt : j < r
  · rw [if_pos hlt]
    have hnot : ¬ (8 * r ≤ 8 * j + b) := by omega
    simp [BitVec.getLsbD_extractLsb', hb, hnot]
  · rw [if_neg hlt]
    have hw0 := congrArg (fun x : Byte => x.getLsbD b) (hwHi j (by omega) hj)
    simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, BitVec.getLsbD_zero] at hw0
    have hle : 8 * r ≤ 8 * j + b := by omega
    have hnotlt : ¬ (8 * j + b < 8 * r) := by omega
    have hlt64 : 8 * j + b < 64 := by omega
    have hsub : 8 * j + b - 8 * r = 8 * (j - r) + b := by omega
    rw [hw0]
    simp [hb, hle, hnotlt, hlt64, hsub]

theorem bv_getLsbD_of_ge {w : Nat} (v : BitVec w) (i : Nat) (h : w ≤ i) : v.getLsbD i = false := by
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have hlt : v.toNat < 2 ^ i := Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) h)
  rw [Nat.div_eq_of_lt hlt]; rfl

theorem word_ushr_byte (v : Word) (s : Nat) (hs : s ≤ 8) (j : Nat) (hj : j < 8) :
    (v >>> (8 * s)).extractLsb' (8 * j) 8 =
      if j + s < 8 then v.extractLsb' (8 * (j + s)) 8 else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hb, decide_true, Bool.true_and]
  by_cases hlt : j + s < 8
  · rw [if_pos hlt]
    simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
    congr 1; omega
  · rw [if_neg hlt, BitVec.getLsbD_zero]
    exact bv_getLsbD_of_ge v _ (by omega)

theorem word_shl_ushr_byte (v : Word) (a b : Nat) (ha : a ≤ 8) (hb_le : b ≤ 8) (j : Nat) (hj : j < 8) :
    ((v <<< (8 * a)) >>> (8 * b)).extractLsb' (8 * j) 8 =
      if j + b < 8 ∧ a ≤ j + b then v.extractLsb' (8 * (j + b - a)) 8 else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    hbit, decide_true, Bool.true_and]
  by_cases h : j + b < 8 ∧ a ≤ j + b
  · rw [if_pos h]
    have hlt64 : 8 * b + (8 * j + bit) < 64 := by omega
    have hle : 8 * a ≤ 8 * b + (8 * j + bit) := by omega
    have hsub : 8 * b + (8 * j + bit) - 8 * a = 8 * (j + b - a) + bit := by omega
    simp [BitVec.getLsbD_extractLsb', hbit, hlt64, hle, hsub]
  · rw [if_neg h, BitVec.getLsbD_zero]
    by_cases hlt64 : 8 * b + (8 * j + bit) < 64
    · have hnotle : ¬ (8 * a ≤ 8 * b + (8 * j + bit)) := by omega
      simp [hlt64, hnotle]
    · simp [hlt64]

theorem word_tail6_clean (v : Word) (d : Digest) (hclean : mask238 d = d)
    (hbytes : ∀ j < 3, v.extractLsb' (8 * (5 + j)) 8 = d.extractLsb' (8 * (29 + j)) 8) :
    v >>> 40 = BitVec.ofNat 64 (tail6 d).toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_ushiftRight]
  have hlt64 : (tail6 d).toNat < 64 := (tail6 d).isLt
  by_cases h6 : b < 6
  · have h5 := congrArg (fun x : Byte => x.getLsbD b) (hbytes 0 (by omega))
    simp only [BitVec.getLsbD_extractLsb', show b < 8 by omega, decide_true, Bool.true_and] at h5
    have hrhs : (BitVec.ofNat 64 (tail6 d).toNat).getLsbD b = (tail6 d).getLsbD b := by
      simp only [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (tail6 d).toNat < 2 ^ 64)]
    rw [hrhs]; unfold tail6
    simp only [BitVec.getLsbD_extractLsb', h6, decide_true, Bool.true_and]
    simpa only [show 8 * (5 + 0) + b = 40 + b by omega, show 8 * (29 + 0) + b = 232 + b by omega] using h5
  · have hrhs : (BitVec.ofNat 64 (tail6 d).toNat).getLsbD b = false := by
      simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 64 ≤ 2 ^ b := by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (show 6 ≤ b by omega)
        have : 2 ^ 6 = 64 := by decide
        omega
      simp [Nat.div_eq_of_lt (by omega : (tail6 d).toNat < 2 ^ b)]
    rw [hrhs]
    by_cases h24 : b < 24
    · have hj : b / 8 < 3 := by omega
      have hbi : b % 8 < 8 := by omega
      have hbyte := congrArg (fun x : Byte => x.getLsbD (b % 8)) (hbytes (b / 8) hj)
      simp only [BitVec.getLsbD_extractLsb', hbi, decide_true, Bool.true_and] at hbyte
      have hidx1 : 8 * (5 + b / 8) + b % 8 = 40 + b := by omega
      have hidx2 : 8 * (29 + b / 8) + b % 8 = 232 + b := by omega
      rw [hidx1, hidx2] at hbyte
      rw [hbyte, ← hclean, mask238_getLsbD]
      simp [show ¬ (232 + b < 238) by omega]
    · exact bv_getLsbD_of_ge v _ (by omega)

theorem byte29_clean_zeroExtend (d : Digest) (hclean : mask238 d = d) :
    (d.extractLsb' (8 * 29) 8).zeroExtend 64 = BitVec.ofNat 64 (tail6 d).toNat := by
  have h29 : d.extractLsb' (8 * 29) 8 = 0#2 ++ tail6 d := by
    have h := mask238_byte_29 d
    rwa [hclean] at h
  rw [h29]
  apply BitVec.eq_of_toNat_eq
  have hlt : (tail6 d).toNat < 64 := (tail6 d).isLt
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat,
    Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, Nat.mod_eq_of_lt (by omega : (tail6 d).toNat < 2 ^ 64)]

theorem word_clean240_hi (v : Word) (d : Digest) (hclean : mask240 d = d)
    (hbytes : ∀ j < 2, v.extractLsb' (8 * (6 + j)) 8 = d.extractLsb' (8 * (30 + j)) 8) :
    ∀ j, 6 ≤ j → j < 8 → v.extractLsb' (8 * j) 8 = 0#8 := by
  intro j hj1 hj2
  have h := hbytes (j - 6) (by omega)
  rw [show 6 + (j - 6) = j by omega, show 30 + (j - 6) = 24 + j by omega] at h
  rw [h, ← hclean, mask240_byte_ge30 d (24 + j) (by omega)]
  rfl

/-- Negative 64-bit tail-bit counter `tCnt - 64` in `[-64, -1]` for `tCnt < 64`. -/
def negCnt (c : Nat) : Word := BitVec.ofNat 64 (2 ^ 64 - 64 + c)

theorem negCnt_slt_zero (c : Nat) (hc : c < 64) : BitVec.slt (negCnt c) 0#64 = true := by
  unfold negCnt
  simp only [BitVec.slt, BitVec.toInt, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 64 + c < 2 ^ 64),
    show (0#64 : Word).toNat = 0 from rfl]
  have hnot : ¬ (2 * (2 ^ 64 - 64 + c) < 2 ^ 64) := by omega
  simp only [hnot, ↓reduceIte, decide_eq_true_eq]
  omega

theorem nonneg_not_slt_zero (c : Nat) (hc : c < 64) : BitVec.slt (BitVec.ofNat 64 c) 0#64 = false := by
  simp only [BitVec.slt, BitVec.toInt, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : c < 2 ^ 64),
    show (0#64 : Word).toNat = 0 from rfl]
  have hlt : 2 * c < 2 ^ 64 := by omega
  simp only [hlt, ↓reduceIte, decide_eq_false_iff_not]
  omega

theorem negCnt_add_lt (c b : Nat) (h : c + b < 64) :
    negCnt c + signExtend12 (BitVec.ofNat 12 b) = negCnt (c + b) := by
  rw [signExtend12_nonneg b (by omega)]
  unfold negCnt
  rw [← BitVec.ofNat_add]
  congr 1; omega

theorem negCnt_add_ge (c b : Nat) (hc : c < 64) (hb : b ≤ 64) (hge : 64 ≤ c + b) :
    negCnt c + signExtend12 (BitVec.ofNat 12 b) = BitVec.ofNat 64 (c + b - 64) := by
  rw [signExtend12_nonneg b (by omega)]
  unfold negCnt
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : 2 ^ 64 - 64 + c + b = (c + b - 64) + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

theorem negCnt_sub64 (c : Nat) (hc : c < 64) :
    BitVec.ofNat 64 c + signExtend12 (BitVec.ofNat 12 (4096 - 64)) = negCnt c := by
  rw [signExtend12_neg 64 (by omega) (by omega), ← BitVec.ofNat_add]
  unfold negCnt
  congr 1; omega

theorem negCnt_mod64 (c : Nat) (hc : c < 64) : (negCnt c).toNat % 64 = c := by
  unfold negCnt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 64 + c < 2 ^ 64)]
  omega

theorem zero_sub_negCnt (c : Nat) (hc : c < 64) :
    0#64 - negCnt c = BitVec.ofNat 64 (64 - c) := by
  unfold negCnt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (0#64 : Word).toNat = 0 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 64 + c < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 64 - c < 2 ^ 64)]
  omega

theorem negCnt_add64 (c : Nat) (hc : c < 64) :
    negCnt c + signExtend12 (64#12) = BitVec.ofNat 64 c := by
  have h := negCnt_add_ge c 64 hc (by omega) (by omega)
  simpa only [Nat.add_sub_cancel] using h

/-- Base-256 unique representation for `bytesToNat`. -/
theorem bytesToNat_lt (bs : List Byte) : bytesToNat bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [bytesToNat]
  | cons b rest ih =>
    simp only [bytesToNat_cons, List.length_cons]
    have hb : b.toNat < 256 := b.isLt
    have hpow : 2 ^ (8 * (rest.length + 1)) = 256 * 2 ^ (8 * rest.length) := by
      rw [show 8 * (rest.length + 1) = 8 + 8 * rest.length by omega, Nat.pow_add]
    rw [hpow]; omega

theorem bytesToNat_inj {a b : List Byte} (hlen : a.length = b.length)
    (hval : bytesToNat a = bytesToNat b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bytesToNat_cons] at hval
      have hx : x.toNat < 256 := x.isLt
      have hy : y.toNat < 256 := y.isLt
      have hxy : x = y := BitVec.eq_of_toNat_eq (by omega)
      have hrest : bytesToNat xs = bytesToNat ys := by omega
      rw [hxy, ih hlen hrest]

theorem bitsOf6_append (a b : List (BitVec 6)) :
    bitsOf6 (a ++ b) = bitsOf6 a + 2 ^ (6 * a.length) * bitsOf6 b := by
  induction a with
  | nil => simp [bitsOf6]
  | cons x xs ih =>
    simp only [List.cons_append, bitsOf6_cons, ih, List.length_cons]
    have hpow : 64 * 2 ^ (6 * xs.length) = 2 ^ (6 * (xs.length + 1)) := by
      rw [show 6 * (xs.length + 1) = 6 + 6 * xs.length by omega, Nat.pow_add]
    calc
      x.toNat + 64 * (bitsOf6 xs + 2 ^ (6 * xs.length) * bitsOf6 b)
        = (x.toNat + 64 * bitsOf6 xs) + (64 * 2 ^ (6 * xs.length)) * bitsOf6 b := by ring
      _ = (x.toNat + 64 * bitsOf6 xs) + 2 ^ (6 * (xs.length + 1)) * bitsOf6 b := by rw [hpow]

theorem bytesToNat_append (a b : List Byte) :
    bytesToNat (a ++ b) = bytesToNat a + 2 ^ (8 * a.length) * bytesToNat b := by
  induction a with
  | nil => simp [bytesToNat]
  | cons x xs ih =>
    simp only [List.cons_append, bytesToNat_cons, ih, List.length_cons]
    have hpow : 256 * 2 ^ (8 * xs.length) = 2 ^ (8 * (xs.length + 1)) := by
      rw [show 8 * (xs.length + 1) = 8 + 8 * xs.length by omega, Nat.pow_add]
    calc
      x.toNat + 256 * (bytesToNat xs + 2 ^ (8 * xs.length) * bytesToNat b)
        = (x.toNat + 256 * bytesToNat xs) + (256 * 2 ^ (8 * xs.length)) * bytesToNat b := by ring
      _ = (x.toNat + 256 * bytesToNat xs) + 2 ^ (8 * (xs.length + 1)) * bytesToNat b := by rw [hpow]

theorem bytesToNat_word_bytes (w : Word) :
    bytesToNat ((List.range 8).map fun j => w.extractLsb' (8 * j) 8) = w.toNat := by
  have hstep : ∀ k ≤ 8,
      bytesToNat ((List.range k).map fun j => w.extractLsb' (8 * j) 8) = w.toNat % 2 ^ (8 * k) := by
    intro k hk
    induction k with
    | zero => simp [bytesToNat, Nat.mod_one]
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, bytesToNat_append_singleton,
        List.length_map, List.length_range, ih (by omega)]
      simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      have hdiv : w.toNat / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + w.toNat % 2 ^ (8 * k) =
          w.toNat % 2 ^ (8 * (k + 1)) := by
        have h256 : (2 : Nat) ^ 8 = 256 := by decide
        have hpow : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
          rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, h256]
        have hq := Nat.div_add_mod (w.toNat / 2 ^ (8 * k)) 256
        have hr := Nat.div_add_mod w.toNat (2 ^ (8 * k))
        have hlt : w.toNat / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + w.toNat % 2 ^ (8 * k) < 2 ^ (8 * k) * 256 := by
          have hlt1 : w.toNat % 2 ^ (8 * k) < 2 ^ (8 * k) := Nat.mod_lt _ (Nat.two_pow_pos _)
          have hlt2 : w.toNat / 2 ^ (8 * k) % 256 + 1 ≤ 256 := by omega
          have hmul := Nat.mul_le_mul_right (2 ^ (8 * k)) hlt2
          linarith
        have heq : w.toNat = (w.toNat / 2 ^ (8 * k) / 256) * (2 ^ (8 * k) * 256) +
            (w.toNat / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + w.toNat % 2 ^ (8 * k)) := by
          have hstep1 : 2 ^ (8 * k) * (256 * (w.toNat / 2 ^ (8 * k) / 256) + w.toNat / 2 ^ (8 * k) % 256) +
              w.toNat % 2 ^ (8 * k) = w.toNat := by rw [hq]; exact hr
          linarith
        rw [hpow]
        conv => rhs; rw [heq]
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hlt]
      have h256' : (2 : Nat) ^ 8 = 256 := by decide
      rw [h256']; omega
  simpa only [Nat.mod_eq_of_lt w.isLt] using hstep 8 (Nat.le_refl 8)

theorem word_or_shl_add_low64 (tBuf tCnt val : Nat)
    (hcnt : tCnt < 64) (hbuf : tBuf < 2 ^ tCnt) (hval : val < 2 ^ 64) :
    (BitVec.ofNat 64 tBuf ||| (BitVec.ofNat 64 val <<< tCnt)).toNat =
      (tBuf + val * 2 ^ tCnt) % 2 ^ 64 := by
  have hpow : 2 ^ tCnt ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)
  have htbuf_lt : tBuf < 2 ^ 64 := by omega
  have hshl : (BitVec.ofNat 64 val <<< tCnt).toNat = (val * 2 ^ tCnt) % 2 ^ 64 := by
    rw [bv64_shl, BitVec.toNat_ofNat]
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htbuf_lt, hshl]
  have hmod : (val * 2 ^ tCnt) % 2 ^ 64 = (val % 2 ^ (64 - tCnt)) * 2 ^ tCnt := by
    have h64 : 2 ^ 64 = 2 ^ (64 - tCnt) * 2 ^ tCnt := by
      rw [← Nat.pow_add, show 64 - tCnt + tCnt = 64 by omega]
    rw [h64, Nat.mul_mod_mul_right]
  rw [hmod, ← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hbuf, Nat.shiftLeft_eq]
  have hlt64 : val % 2 ^ (64 - tCnt) * 2 ^ tCnt + tBuf < 2 ^ 64 := by
    have h1 : val % 2 ^ (64 - tCnt) < 2 ^ (64 - tCnt) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : (val % 2 ^ (64 - tCnt) + 1) * 2 ^ tCnt ≤ 2 ^ (64 - tCnt) * 2 ^ tCnt :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : 2 ^ (64 - tCnt) * 2 ^ tCnt = 2 ^ 64 := by
      rw [← Nat.pow_add, show 64 - tCnt + tCnt = 64 by omega]
    linarith
  have hcongr : (tBuf + val * 2 ^ tCnt) % 2 ^ 64 = (val % 2 ^ (64 - tCnt) * 2 ^ tCnt + tBuf) % 2 ^ 64 := by
    rw [Nat.add_comm tBuf, Nat.add_mod, hmod, Nat.mod_eq_of_lt htbuf_lt]
  rw [hcongr, Nat.mod_eq_of_lt hlt64]

theorem tail_hi_ushr (tBuf tCnt val : Nat)
    (hcnt : tCnt < 64) (hbuf : tBuf < 2 ^ tCnt) (hval : val < 2 ^ 64)
    (hpos : 0 < tCnt) :
    (BitVec.ofNat 64 val >>> (64 - tCnt)).toNat = (tBuf + val * 2 ^ tCnt) / 2 ^ 64 := by
  rw [bv64_ushr val (64 - tCnt) hval, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hlt : val / 2 ^ (64 - tCnt) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hval
  rw [Nat.mod_eq_of_lt hlt]
  have h64 : 2 ^ 64 = 2 ^ tCnt * 2 ^ (64 - tCnt) := by
    rw [← Nat.pow_add, show tCnt + (64 - tCnt) = 64 by omega]
  rw [h64, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos tCnt),
    Nat.div_eq_of_lt hbuf, Nat.zero_add]

/-! ### 4. Single-Instruction Step Lemmas for `openImage` -/

theorem step_ADDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.ADDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.ADDI rd rs1 imm)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_ADD {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.ADD rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.ADD rd rs1 rs2)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADD rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_SUB {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.SUB rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.SUB rd rs1 rs2)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SUB rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_SLLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.SLLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.SLLI rd rs1 shamt)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_SRLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.SRLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.SRLI rd rs1 shamt)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_SLL {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.SLL rd rs1 rs2)) :
    OpenRuns s 1 1
      ((s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.SLL rd rs1 rs2)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLL rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_SRL {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.SRL rd rs1 rs2)) :
    OpenRuns s 1 1
      ((s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.SRL rd rs1 rs2)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRL rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_XORI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.XORI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.XORI rd rs1 imm)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.XORI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_ANDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.ANDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.ANDI rd rs1 imm)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ANDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_OR {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.OR rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.OR rd rs1 rs2)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.OR rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_AND {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.AND rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.AND rd rs1 rs2)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.AND rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_LUI {s : MachineState} {idx : Nat} {rd : Reg} {imm : BitVec 20}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.LUI rd imm)) :
    OpenRuns s 1 1
      ((s.setReg rd ((imm.zeroExtend 32 <<< 12).signExtend 64)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.LUI rd imm)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LUI rd imm)) =
      some ((s.setReg rd ((imm.zeroExtend 32 <<< 12).signExtend 64)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd ((imm.zeroExtend 32 <<< 12).signExtend 64)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_AUIPC {s : MachineState} {idx : Nat} {rd : Reg} {imm : BitVec 20}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.AUIPC rd imm)) :
    OpenRuns s 1 1
      ((s.setReg rd (pcAt idx + (imm.zeroExtend 32 <<< 12).signExtend 64)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.AUIPC rd imm)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.AUIPC rd imm)) =
      some ((s.setReg rd (pcAt idx + (imm.zeroExtend 32 <<< 12).signExtend 64)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.pc + (imm.zeroExtend 32 <<< 12).signExtend 64)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_DIVU {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.DIVU rd rs1 rs2)) :
    OpenRuns s 1 4 ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.DIVU rd rs1 rs2)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.DIVU rd rs1 rs2)) =
      some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_LD {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.LD rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    OpenRuns s 1 1 ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.LD rd rs1 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LD rd rs1 off)) =
      some ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
            then some ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_LWU {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.LWU rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 4 = true) :
    OpenRuns s 1 1
      ((s.setReg rd ((s.getWord32 (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.LWU rd rs1 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LWU rd rs1 off)) =
      some ((s.setReg rd ((s.getWord32 (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 4 = true
            then some ((s.setReg rd ((s.getWord32 (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_LBU {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.LBU rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    OpenRuns s 1 1
      ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.LBU rd rs1 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LBU rd rs1 off)) =
      some ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
            then some ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_SD {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.SD rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    OpenRuns s 1 1
      ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.SD rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SD rs1 rs2 off)) =
      some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
            then some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_SW {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.SW rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 4 = true) :
    OpenRuns s 1 1
      ((s.setWord32 (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 32)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.SW rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SW rs1 rs2 off)) =
      some ((s.setWord32 (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 32)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 4 = true
            then some ((s.setWord32 (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 32)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_SB {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.SB rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    OpenRuns s 1 1
      ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.SB rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SB rs1 rs2 off)) =
      some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
            then some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_BEQ_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BEQ rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch openImage s = some (.base (.BEQ rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hcond : (s.getReg rs1 == s.getReg rs2) = true := by rw [heq]; simp
  have hst : ordinaryStep s (.base (.BEQ rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if (s.getReg rs1 == s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

theorem step_BEQ_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BEQ rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.BEQ rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hcond : ¬ ((s.getReg rs1 == s.getReg rs2) = true) := fun h => hne (eq_of_beq h)
  have hst : ordinaryStep s (.base (.BEQ rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if (s.getReg rs1 == s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_BNE_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BNE rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch openImage s = some (.base (.BNE rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hcond : (s.getReg rs1 != s.getReg rs2) = true := by
    cases hb : (s.getReg rs1 == s.getReg rs2) with
    | true => exact absurd (eq_of_beq hb) hne
    | false => simp [bne, hb]
  have hst : ordinaryStep s (.base (.BNE rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if (s.getReg rs1 != s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

theorem step_BNE_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BNE rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.BNE rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hcond : ¬ ((s.getReg rs1 != s.getReg rs2) = true) := by rw [heq]; simp
  have hst : ordinaryStep s (.base (.BNE rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if (s.getReg rs1 != s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_BLT_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BLT rs1 rs2 off))
    (hlt : BitVec.slt (s.getReg rs1) (s.getReg rs2) = true)
    (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch openImage s = some (.base (.BLT rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.BLT rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if BitVec.slt (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hlt, hpc, htgt]
  exact OpenRuns.step hf hst

theorem step_BLT_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BLT rs1 rs2 off))
    (hge : BitVec.slt (s.getReg rs1) (s.getReg rs2) = false) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.BLT rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hnot : ¬ (BitVec.slt (s.getReg rs1) (s.getReg rs2) = true) := by rw [hge]; decide
  have hst : ordinaryStep s (.base (.BLT rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if BitVec.slt (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hnot, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_BLTU_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BLTU rs1 rs2 off))
    (hlt : (s.getReg rs1).toNat < (s.getReg rs2).toNat)
    (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch openImage s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hcond : BitVec.ult (s.getReg rs1) (s.getReg rs2) = true := by
    simp only [BitVec.ult, decide_eq_true_eq]; exact hlt
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

theorem step_BLTU_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BLTU rs1 rs2 off))
    (hle : (s.getReg rs2).toNat ≤ (s.getReg rs1).toNat) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hcond : ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq]; omega
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_BGEU_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BGEU rs1 rs2 off))
    (hle : (s.getReg rs2).toNat ≤ (s.getReg rs1).toNat)
    (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch openImage s = some (.base (.BGEU rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hcond : ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq]; omega
  have hst : ordinaryStep s (.base (.BGEU rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true)
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

theorem step_BGEU_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.BGEU rs1 rs2 off))
    (hlt : (s.getReg rs1).toNat < (s.getReg rs2).toNat) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch openImage s = some (.base (.BGEU rs1 rs2 off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hult : BitVec.ult (s.getReg rs1) (s.getReg rs2) = true := by
    simp only [BitVec.ult, decide_eq_true_eq]; exact hlt
  have hcond : ¬ ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true) := fun h => h hult
  have hst : ordinaryStep s (.base (.BGEU rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true)
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

theorem step_JAL {s : MachineState} {idx tgt : Nat} {rd : Reg} {off : BitVec 21}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.JAL rd off))
    (htgt : pcAt idx + signExtend21 off = pcAt tgt) :
    OpenRuns s 1 1 ((s.setReg rd (pcAt (idx + 1))).setPC (pcAt tgt)) := by
  have hf : fetch openImage s = some (.base (.JAL rd off)) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.JAL rd off)) =
      some ((s.setReg rd (pcAt (idx + 1))).setPC (pcAt tgt)) := by
    change some ((s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 off)) = _
    rw [hpc, pcAt_add4, htgt]
  exact OpenRuns.step hf hst

theorem step_JALR {s : MachineState} {idx tgt : Nat} {rd rs1 : Reg}
    (hidx : idx < OPEN_CODE_LEN) (hpc : s.pc = pcAt idx)
    (hi : openInstr idx = .base (.JALR rd rs1 (0#12)))
    (hrs1 : s.getReg rs1 = pcAt tgt) :
    OpenRuns s 1 1 ((s.setReg rd (pcAt (idx + 1))).setPC (pcAt tgt)) := by
  have hf : fetch openImage s = some (.base (.JALR rd rs1 (0#12))) := by
    rw [open_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.JALR rd rs1 (0#12))) =
      some ((s.setReg rd (pcAt (idx + 1))).setPC (pcAt tgt)) := by
    change some ((s.setReg rd (s.pc + 4)).setPC ((s.getReg rs1 + signExtend12 (0#12)) &&& ~~~1#64)) = _
    rw [hpc, pcAt_add4, hrs1, pcAt_jalr_return]
  exact OpenRuns.step hf hst

/-! ### 5. Memory Frame, WriterState, and TailState Invariants -/

/-- Writes restricted to the proof output buffer `[11341403200, 19897793624)`. -/
def ProofWritePreserves (s s' : MachineState) : Prop :=
  ∀ a : Word, ¬ (11341403200 ≤ a.toNat ∧ a.toNat < 19897793624) → s'.getMem a = s.getMem a

theorem ProofWritePreserves.refl (s : MachineState) : ProofWritePreserves s s :=
  fun _ _ => rfl

theorem ProofWritePreserves.trans {s1 s2 s3 : MachineState}
    (h1 : ProofWritePreserves s1 s2) (h2 : ProofWritePreserves s2 s3) :
    ProofWritePreserves s1 s3 :=
  fun a ha => (h2 a ha).trans (h1 a ha)

theorem ProofWritePreserves.setMem_proof {s : MachineState} {addr : Nat} {v : Word}
    (hlo : 11341403200 ≤ addr) (hhi : addr < 19897793624) (hal : addr % 8 = 0) :
    ProofWritePreserves s (s.setMem (BitVec.ofNat 64 addr) v) := by
  intro a ha
  have hne : a ≠ BitVec.ofNat 64 addr := by
    intro heq; apply ha; rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact ⟨hlo, hhi⟩
  exact MachineState.getMem_setMem_ne hne

theorem ProofWritePreserves.setWord32_proof {s : MachineState} {addr : Nat} {v : BitVec 32}
    (hlo : 11341403200 ≤ addr) (hhi : addr < 19897793624) (hal : addr % 4 = 0) :
    ProofWritePreserves s (s.setWord32 (BitVec.ofNat 64 addr) v) := by
  intro a ha
  have halA : alignToDword (BitVec.ofNat 64 addr) = BitVec.ofNat 64 (8 * (addr / 8)) := by
    simpa only [show 8 * (addr / 8) + addr % 8 = addr by omega] using
      alignToDword_ofNat_eq (8 * (addr / 8)) (addr % 8) (by omega) (by omega)
  have hne : a ≠ alignToDword (BitVec.ofNat 64 addr) := by
    rw [halA]; intro heq; apply ha
    rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  simp only [MachineState.setWord32]
  exact MachineState.getMem_setMem_ne hne

theorem ProofWritePreserves.setByte_proof {s : MachineState} {addr : Nat} {b : Byte}
    (hlo : 11341403200 ≤ addr) (hhi : addr < 19897793624) :
    ProofWritePreserves s (s.setByte (BitVec.ofNat 64 addr) b) := by
  intro a ha
  have halA : alignToDword (BitVec.ofNat 64 addr) = BitVec.ofNat 64 (8 * (addr / 8)) := by
    simpa only [show 8 * (addr / 8) + addr % 8 = addr by omega] using
      alignToDword_ofNat_eq (8 * (addr / 8)) (addr % 8) (by omega) (by omega)
  have hne : a ≠ alignToDword (BitVec.ofNat 64 addr) := by
    rw [halA]; intro heq; apply ha
    rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  simp only [MachineState.setByte]
  exact MachineState.getMem_setMem_ne hne

/-- Preservation of all read-only input regions (`trapdoor`, `indices`, `openingData`). -/
def ReadOnlyPreserved (s0 s : MachineState) : Prop :=
  ∀ a : Word, (4294971424 ≤ a.toNat ∧ a.toNat < 11341403200) ∨ 68719475936 ≤ a.toNat →
    s.getMem a = s0.getMem a

theorem ReadOnlyPreserved.of_proofWrite {s0 s s' : MachineState}
    (hro : ReadOnlyPreserved s0 s) (hp : ProofWritePreserves s s') :
    ReadOnlyPreserved s0 s' :=
  fun a ha => (hp a (by omega)).trans (hro a ha)

/-- Register preservation outside a small scratch set (typically `{x5, x6, x10, x12}` or `{x5, x6, x12}`). -/
def RegsEqExcept (excl : List Reg) (s s' : MachineState) : Prop :=
  ∀ r : Reg, r ∉ excl → s'.getReg r = s.getReg r

/-- Proof prefix predicate: first `bs.length` bytes at `11341403200` match `bs`. -/
def ProofPrefix (s : MachineState) (bs : List Byte) : Prop :=
  ∀ j (hj : j < bs.length), s.getByte (BitVec.ofNat 64 (11341403200 + j)) = bs[j]

/-- Buffered 64-bit aligned proof-writer state at `x25 = 11341403200 + base`, logical offset
`dstOff` (multiple of 8), residue `r : Fin 8`, optional `r = 4` already-flushed half-dword flag
`flushedR4`, and accumulated logical bytes `written`. Data bytes are conditional on `clean`. -/
structure WriterState (clean : Prop) (s : MachineState) (r : Fin 8) (flushedR4 : Bool)
    (base dstOff : Nat) (written : List Byte) : Prop where
  hbase8 : base % 8 = 0
  hdst8 : dstOff % 8 = 0
  hlen : written.length = base + dstOff + r.val
  hbound : base + dstOff + 8 ≤ 8556390424
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (11341403200 + base)
  hflushed_ok : flushedR4 = true → r.val = 4
  hbytes : clean → ∀ j (hj : j < base + dstOff),
    s.getByte (BitVec.ofNat 64 (11341403200 + j)) = written[j]'(by omega)
  hrem : clean →
    if flushedR4 = true then
      ∀ j (hj : j < r.val),
        s.getByte (BitVec.ofNat 64 (11341403200 + base + dstOff + j)) =
          written[base + dstOff + j]'(by omega)
    else if r.val = 0 then
      True
    else
      (∀ j (hj : j < r.val),
        (s.getReg .x12).extractLsb' (8 * j) 8 = written[base + dstOff + j]'(by omega)) ∧
      (∀ j, r.val ≤ j → j < 8 → (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8)

/-- 64-bit streaming tail-packer state `(x15, x16, x17)` with negative bit counter `x17 = negCnt tCnt`. -/
structure TailState (clean : Prop) (s : MachineState) (tails : List (BitVec 6)) (flushes : Nat) : Prop where
  hbits : 64 * flushes + (6 * tails.length) % 64 = 6 * tails.length
  hbound : 8 * flushes + 16 ≤ 48719475936
  rx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + 8 * flushes)
  rx17 : s.getReg .x17 = negCnt ((6 * tails.length) % 64)
  hdata : clean →
    ∃ tBuf : Nat,
      tBuf < 2 ^ ((6 * tails.length) % 64) ∧
      s.getReg .x16 = BitVec.ofNat 64 tBuf ∧
      bytesToNat ((List.range (8 * flushes)).map fun j =>
          s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
        2 ^ (64 * flushes) * tBuf = bitsOf6 tails

theorem TailState.of_proofWrite {clean : Prop} {s s' : MachineState}
    {tails : List (BitVec 6)} {flushes : Nat}
    (ht : TailState clean s tails flushes) (hp : ProofWritePreserves s s')
    (hx15 : s'.getReg .x15 = s.getReg .x15)
    (hx16 : s'.getReg .x16 = s.getReg .x16)
    (hx17 : s'.getReg .x17 = s.getReg .x17) :
    TailState clean s' tails flushes := by
  refine ⟨ht.hbits, ht.hbound, hx15.trans ht.rx15, hx17.trans ht.rx17, fun hcl => ?_⟩
  obtain ⟨tBuf, hlt, hx16', hsum⟩ := ht.hdata hcl
  refine ⟨tBuf, hlt, hx16.trans hx16', ?_⟩
  have hmap : ((List.range (8 * flushes)).map fun j => s'.getByte (BitVec.ofNat 64 (tailBufBase + j))) =
      ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) := by
    apply List.map_congr_left
    intro j hj
    have hjlt := List.mem_range.mp hj
    simp only [MachineState.getByte]
    congr 1
    apply hp
    have hal := alignToDword_ofNat_eq (8 * ((tailBufBase + j) / 8)) ((tailBufBase + j) % 8) (by omega) (by omega)
    rw [show 8 * ((tailBufBase + j) / 8) + (tailBufBase + j) % 8 = tailBufBase + j by omega] at hal
    rw [hal, BitVec.toNat_ofNat]
    have htbb : tailBufBase = 20000000000 := rfl
    have hbd := ht.hbound
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hmap]; exact hsum

end CommitGolfCandidate.MoonOpen
