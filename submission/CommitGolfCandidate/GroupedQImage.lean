import CommitGolfCandidate.GroupedImageBase
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
def quadPC (slot : Nat) : Word := wordPC (45594+3*slot)
def quadOp (part : Fin 3) : Instr :=
  if part.val=0 then .ECALL else if part.val=1 then .ADDI .x10 .x10 512 else .ADDI .x12 .x12 32
private def QDecode (t : Nat) : Prop := ∀ u : Fin 256, ∀ p : Fin 3,
  Manifest.decodeBase (codeWord (45594+3*(256*t+u.val)+p.val))=some (quadOp p)
private theorem qdec : ∀ t : Fin 32,QDecode t.val := by intro t;unfold QDecode;fin_cases t <;> decide +kernel
private theorem quad_words (slot : Fin 8192) (part : Fin 3) :
    Manifest.decodeBase (codeWord (45594+3*slot.val+part.val))=some (quadOp part) := by
  have h:=qdec ⟨slot.val/256,by have:=slot.isLt;omega⟩ ⟨slot.val%256,by omega⟩ part
  simpa only [Fin.val_mk,Nat.div_add_mod] using h
theorem fetch_quad (state : MachineState) (slot : Fin 8192) (part : Fin 3)
    (pc : state.pc=quadPC slot.val+BitVec.ofNat 64 (4*part.val)) :
    fetch image state=some (.base (quadOp part)) := by
  have atWord : state.pc=wordPC (45594+3*slot.val+part.val) := by
    rw [pc,quadPC,wordPC,wordPC,←BitVec.ofNat_add]
    congr 1 <;> omega
  exact fetch_decoded state _ (by have := slot.isLt;have := part.isLt;omega) atWord _ (quad_words slot part)

def quadSetupOps : List Instr := [.ADDI .x10 .x21 0,.SRLI .x7 .x19 2,.ADD .x12 .x9 .x7]
def upperSetupOps : List Instr := [.ADDI .x10 .x12 4032,.SRLI .x7 .x19 2,.SUB .x12 .x12 .x7,.ADDI .x12 .x12 4064,.ADDI .x11 .x0 64,.ADDI .x13 .x0 0]

private theorem quadSetup_decoded : ∀ i : Fin 3, Manifest.decodeBase (codeWord (45591+i.val)) =
    some ((quadSetupOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_quadSetup (s : MachineState) (i : Fin 3) (pc : s.pc=wordPC (45591+i.val)) :
    fetch image s=some (.base ((quadSetupOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (quadSetup_decoded i)

private theorem upperSetup_decoded : ∀ i : Fin 6, Manifest.decodeBase (codeWord (70172+i.val)) =
    some ((upperSetupOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_upperSetup (s : MachineState) (i : Fin 6) (pc : s.pc=wordPC (70172+i.val)) :
    fetch image s=some (.base ((upperSetupOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (upperSetup_decoded i)

theorem fetch_quad_branch (s : MachineState) (pc : s.pc=wordPC 70170) :
    fetch image s=some (.base (.BEQ .x10 .x24 8)) := fetch_decoded s 70170 (by decide) pc _ (by decide +kernel)

theorem fetch_quad_jump (s : MachineState) (pc : s.pc=wordPC 70171) :
    fetch image s=some (.base (.JAL .x0 1998844)) := fetch_decoded s 70171 (by decide) pc _ (by decide +kernel)

end TwoPermutationPrototype.Grouped
