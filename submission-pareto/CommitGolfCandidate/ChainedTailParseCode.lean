import CommitGolfCandidate.ChainedTailValidate

/-! Inverse scratch-row traversal followed by canonical-tail validation. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def tailParseOps : List Instr := [.BEQ .x22 .x0 72,.LBU .x26 .x21 1] ++ tailReadOps ++
  [.SB .x21 .x24 0,.ADDI .x21 .x21 2,.ADDI .x22 .x22 4095,.BNE .x22 .x0 8128] ++ tailValidateOps
def tailParseWords : List (BitVec 32) := [0x040b0463,0x001acd03] ++ tailReadWords ++
  [0x018a8023,0x002a8a93,0xfffb0b13,0xfc0b10e3] ++ tailValidateWords
def tailParseImage : Image := ⟨tailParseWords,[]⟩
def tailParseOp (index : Nat) : Instr := (tailParseOps[index]?).getD .EBREAK

theorem tail_parse_decode : ∀ i : Fin 21,
    (tailParseWords[i.val]?).bind decodeInstruction = some (.base (tailParseOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def TailParseAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 21, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (tailParseOp i.val))

theorem tail_parse_at : TailParseAt tailParseImage 4096 := by
  intro i s pc
  apply cap_image_fetch tailParseImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact tail_parse_decode i

theorem TailParseAt.read {image : Image} {base : Word} (code : TailParseAt image base) :
    TailReadAt image (base+8) := by
  intro i s pc
  have op : tailParseOp (2+i.val) = tailReadOp i.val := by fin_cases i <;> rfl
  have location : s.pc = base+BitVec.ofNat 64 (4*(2+i.val)) := by
    rw [pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  simpa only [op] using code ⟨2+i.val,by have := i.isLt; omega⟩ s location

theorem TailParseAt.validate {image : Image} {base : Word} (code : TailParseAt image base) :
    TailValidateAt image (base+72) := by
  intro i s pc
  have op : tailParseOp (18+i.val) = tailValidateOp i.val := by fin_cases i <;> rfl
  have location : s.pc = base+BitVec.ofNat 64 (4*(18+i.val)) := by
    rw [pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  simpa only [op] using code ⟨18+i.val,by have := i.isLt; omega⟩ s location

end CommitGolfCandidate.Chained.Native
