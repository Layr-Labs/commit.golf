import CommitGolfCandidate.ChainedTailRead

/-! A field-row traversal: value/width byte pairs, guarded emission, final padding. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def tailLoadOps : List Instr := [.LBU .x24 .x21 0,.LBU .x26 .x21 1,.ADDI .x21 .x21 2]
def tailLoadOp (index : Nat) : Instr := (tailLoadOps[index]?).getD .EBREAK
def tailLoadPrefix (s : MachineState) (count : Nat) : MachineState :=
  (tailLoadOps.take count).foldl execInstrBr s
def tailTraverseOps : List Instr := [.BEQ .x22 .x0 56] ++ tailLoadOps ++ tailEmitOps ++
  [.ADDI .x22 .x22 4095,.BNE .x22 .x0 8144] ++ tailFinishOps
def tailTraverseWords : List (BitVec 32) :=
  [0x020b0c63,0x000acc03,0x001acd03,0x002a8a93] ++ tailEmitWords ++
  [0xfffb0b13,0xfc0b18e3] ++ tailFinishWords
def tailTraverseImage : Image := ⟨tailTraverseWords,[]⟩
def tailTraverseOp (index : Nat) : Instr := (tailTraverseOps[index]?).getD .EBREAK

theorem tail_traverse_decode : ∀ i : Fin 17,
    (tailTraverseWords[i.val]?).bind decodeInstruction = some (.base (tailTraverseOp i.val)) := by
  intro i
  fin_cases i <;> rfl

def TailTraverseAt (image : Image) (base : Word) : Prop :=
  ∀ i : Fin 17, ∀ s : MachineState, s.pc = base+BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (tailTraverseOp i.val))

theorem tail_traverse_at : TailTraverseAt tailTraverseImage 4096 := by
  intro i s pc
  apply cap_image_fetch tailTraverseImage s i.val _ (by have := i.isLt; omega)
  · change s.pc = BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add] at pc
    exact pc
  · exact tail_traverse_decode i

theorem TailTraverseAt.emit {image : Image} {base : Word} (code : TailTraverseAt image base) :
    TailEmitAt image (base+16) := by
  intro i s pc
  have op : tailTraverseOp (4+i.val) = tailEmitOp i.val := by fin_cases i <;> rfl
  have location : s.pc = base+BitVec.ofNat 64 (4*(4+i.val)) := by
    rw [pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  simpa only [op] using code ⟨4+i.val,by have := i.isLt; omega⟩ s location

theorem TailTraverseAt.finish {image : Image} {base : Word} (code : TailTraverseAt image base) :
    TailFinishAt image (base+56) := by
  intro i s pc
  have op : tailTraverseOp (14+i.val) = tailFinishOp i.val := by fin_cases i <;> rfl
  have location : s.pc = base+BitVec.ofNat 64 (4*(14+i.val)) := by
    rw [pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  simpa only [op] using code ⟨14+i.val,by have := i.isLt; omega⟩ s location

end CommitGolfCandidate.Chained.Native
