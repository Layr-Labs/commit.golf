import CommitGolfCandidate.ChainedContinuationCode
import CommitGolfCandidate.ChainedOpeningCodec

/-! Native variable-width tail append. Byte flushing is left to the caller. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

def tailAppendOps : List Instr := [.SLL .x28 .x24 .x25,.OR .x23 .x23 .x28,.ADD .x25 .x25 .x26]
def tailAppendWords : List (BitVec 32) := [0x019c1e33,0x01cbebb3,0x01ac8cb3]
def tailAppendImage : Image := ⟨tailAppendWords,[]⟩
def tailAppendOp (index : Nat) : Instr := (tailAppendOps[index]?).getD .EBREAK
def tailAppendPrefix (s : MachineState) (count : Nat) : MachineState :=
  (tailAppendOps.take count).foldl execInstrBr s

theorem tail_append_decode : ∀ i : Fin 3,
    (tailAppendWords[i.val]?).bind decodeInstruction = some (.base (tailAppendOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def TailAppendAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 3, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (tailAppendOp i.val))

theorem tail_append_at : TailAppendAt tailAppendImage 4096 := by
  intro i s pc
  apply cap_image_fetch tailAppendImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact tail_append_decode i

theorem tail_append_value (s : MachineState) :
    (tailAppendPrefix s 3).getReg .x23 =
      s.getReg .x23 ||| (s.getReg .x24 <<< ((s.getReg .x25).toNat%64)) := rfl

theorem tail_append_count (s : MachineState) :
    (tailAppendPrefix s 3).getReg .x25 = s.getReg .x25+s.getReg .x26 := rfl

theorem tail_append_memory (s : MachineState) (query : Word) :
    (tailAppendPrefix s 3).getMem query = s.getMem query := rfl

theorem tail_append_frame (s : MachineState) (reg : Reg)
    (value : reg ≠ .x23) (count : reg ≠ .x25) (scratch : reg ≠ .x28) :
    (tailAppendPrefix s 3).getReg reg = s.getReg reg := by
  cases reg <;> first | contradiction | rfl

private theorem prefix_succ (s : MachineState) (count : Nat) (inside : count < 3) :
    tailAppendPrefix s (count+1) = execInstrBr (tailAppendPrefix s count) (tailAppendOp count) := by
  interval_cases count <;> rfl

theorem tail_append_pc (s : MachineState) (count : Nat) (small : count ≤ 3) :
    (tailAppendPrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [tailAppendPrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step : (execInstrBr (tailAppendPrefix s count) (tailAppendOp count)).pc =
        (tailAppendPrefix s count).pc+4 := by
      have inside : count < 3 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4 = _
    rw [←BitVec.ofNat_add]
    congr 1

theorem tail_append_execution (image : Image) (base : Word) (code : TailAppendAt image base)
    (s : MachineState) (pc : s.pc = base) (fuel : Nat) (coins : Bool) :
    execute image (3+fuel) s coins =
      (do let result ← execute image fuel (tailAppendPrefix s 3) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := tailAppendPrefix s)
  intro i inside
  refine ⟨.base (tailAppendOp i),?_,?_,?_⟩
  · apply code ⟨i,inside⟩
    rw [tail_append_pc s i (by omega),pc]
  · rw [prefix_succ s i inside]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem tail_shift_word (value shift : Nat) :
    BitVec.ofNat 64 value <<< shift = BitVec.ofNat 64 (value*2^shift) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq,Nat.mul_mod]

theorem tail_append_word (buffer value shift : Nat) (low : buffer < 2^shift)
    (fit : buffer+value*2^shift < 2^64) :
    BitVec.ofNat 64 buffer ||| (BitVec.ofNat 64 value <<< shift) =
      BitVec.ofNat 64 (buffer+value*2^shift) := by
  have bufferFit : buffer < 2^64 := by omega
  have valueFit : value*2^shift < 2^64 := by omega
  rw [tail_shift_word]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bufferFit,
    Nat.mod_eq_of_lt valueFit,Nat.mod_eq_of_lt fit]
  rw [Nat.add_comm,Nat.mul_comm,Nat.two_pow_add_eq_or_of_lt low,Nat.or_comm]

theorem tail_append_small (buffer value shift width : Nat) (occupied : shift < 8) (size : width ≤ 6)
    (low : buffer < 2^shift) (high : value < 2^width) :
    buffer+value*2^shift < 2^(shift+width) ∧ shift+width ≤ 13 := by
  constructor
  · rw [Nat.pow_add]
    have positive : 0 < 2^shift := by positivity
    nlinarith
  · omega

theorem tail_append_field (s : MachineState) (buffer value shift width : Nat)
    (bufferReg : s.getReg .x23 = BitVec.ofNat 64 buffer)
    (valueReg : s.getReg .x24 = BitVec.ofNat 64 value)
    (shiftReg : s.getReg .x25 = BitVec.ofNat 64 shift)
    (widthReg : s.getReg .x26 = BitVec.ofNat 64 width)
    (occupied : shift < 8) (size : width ≤ 6) (low : buffer < 2^shift) (high : value < 2^width) :
    (tailAppendPrefix s 3).getReg .x23 = BitVec.ofNat 64 (buffer+value*2^shift) ∧
    (tailAppendPrefix s 3).getReg .x25 = BitVec.ofNat 64 (shift+width) ∧
    buffer+value*2^shift < 2^(shift+width) ∧ shift+width ≤ 13 := by
  have bounded := tail_append_small buffer value shift width occupied size low high
  have power : 2^(shift+width) ≤ 2^13 := by gcongr; exact bounded.2
  have fit : buffer+value*2^shift < 2^64 := lt_of_lt_of_le bounded.1 (power.trans (by decide))
  have shiftValue : (s.getReg .x25).toNat%64 = shift := by
    rw [shiftReg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_,?_,bounded⟩
  · rw [tail_append_value,bufferReg,valueReg,shiftValue]
    exact tail_append_word buffer value shift low fit
  · rw [tail_append_count,shiftReg,widthReg,←BitVec.ofNat_add]

theorem record_tail_widths : ∀ field ∈ InteriorCodec.recordSpec, field.2 ≤ 6 := by decide +kernel

theorem footer_tail_widths (nodes : List Nat) : ∀ field ∈ InteriorCodec.footerSpec nodes, field.2 ≤ 6 := by
  intro field member
  obtain ⟨node,_,rfl⟩ := List.mem_map.mp member
  change InteriorCodec.footerWidth node-232 ≤ 6
  unfold InteriorCodec.footerWidth
  split <;> decide

end CommitGolfCandidate.Chained.Native
