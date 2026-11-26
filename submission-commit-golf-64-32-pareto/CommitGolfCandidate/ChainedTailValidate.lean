import CommitGolfCandidate.ChainedTailReadBits
import CommitGolfCandidate.ChainedTailRowBits

/-! Native canonical-tail flag: zero residual bits and exact proof-end pointer. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def tailValidateOps : List Instr :=
  [.XOR .x28 .x20 .x19,.OR .x28 .x28 .x23,.SLTIU .x24 .x28 1]
def tailValidateWords : List (BitVec 32) := [0x013a4e33,0x017e6e33,0x001e3c13]
def tailValidateImage : Image := ⟨tailValidateWords,[]⟩
def tailValidateOp (index : Nat) : Instr := (tailValidateOps[index]?).getD .EBREAK
def tailValidatePrefix (s : MachineState) (count : Nat) : MachineState :=
  (tailValidateOps.take count).foldl execInstrBr s
def tailValidateBad (s : MachineState) : Word := (s.getReg .x20 ^^^ s.getReg .x19) ||| s.getReg .x23

theorem tail_validate_decode : ∀ i : Fin 3,
    (tailValidateWords[i.val]?).bind decodeInstruction = some (.base (tailValidateOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def TailValidateAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 3, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (tailValidateOp i.val))

theorem tail_validate_at : TailValidateAt tailValidateImage 4096 := by
  intro i s pc
  apply cap_image_fetch tailValidateImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact tail_validate_decode i

private theorem prefix_succ (s : MachineState) (count : Nat) (inside : count<3) :
    tailValidatePrefix s (count+1) = execInstrBr (tailValidatePrefix s count) (tailValidateOp count) := by
  interval_cases count <;> rfl

theorem tail_validate_pc (s : MachineState) (count : Nat) (small : count≤3) :
    (tailValidatePrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [tailValidatePrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step : (execInstrBr (tailValidatePrefix s count) (tailValidateOp count)).pc =
        (tailValidatePrefix s count).pc+4 := by
      have inside : count<3 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4 = _
    rw [←BitVec.ofNat_add]
    congr 1

theorem tail_validate_execution (image : Image) (base : Word) (code : TailValidateAt image base)
    (s : MachineState) (pc : s.pc=base) (fuel : Nat) (coins : Bool) :
    execute image (3+fuel) s coins =
      (do let result ← execute image fuel (tailValidatePrefix s 3) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := tailValidatePrefix s)
  intro i inside
  refine ⟨.base (tailValidateOp i),?_,?_,?_⟩
  · apply code ⟨i,inside⟩
    rw [tail_validate_pc s i (by omega),pc]
  · rw [prefix_succ s i inside]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem tail_validate_value (s : MachineState) :
    (tailValidatePrefix s 3).getReg .x24 = if BitVec.ult (tailValidateBad s) (1#64) then 1#64 else 0#64 := rfl

theorem tail_validate_flag (s : MachineState) :
    (tailValidatePrefix s 3).getReg .x24 =
      if s.getReg .x20=s.getReg .x19 ∧ s.getReg .x23=0#64 then 1#64 else 0#64 := by
  have zero : tailValidateBad s=0#64 ↔ s.getReg .x20=s.getReg .x19 ∧ s.getReg .x23=0#64 := by
    rw [tailValidateBad,BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff]
  have natural : (tailValidateBad s).toNat=0 ↔ tailValidateBad s=0#64 := by
    change (tailValidateBad s).toNat=(0#64).toNat ↔ _
    exact BitVec.toNat_inj
  have flag : BitVec.ult (tailValidateBad s) (1#64) = decide (tailValidateBad s=0#64) := by
    change decide ((tailValidateBad s).toNat<1) = _
    simp only [Nat.lt_one_iff,natural]
  rw [tail_validate_value,flag]
  simp [zero]

theorem tail_validate_memory (s : MachineState) (query : Word) :
    (tailValidatePrefix s 3).getMem query = s.getMem query := rfl

theorem tail_validate_frame (s : MachineState) (reg : Reg) (result : reg≠.x24) (scratch : reg≠.x28) :
    (tailValidatePrefix s 3).getReg reg = s.getReg reg := by
  cases reg <;> first | contradiction | rfl

end CommitGolfCandidate.Chained.Native
