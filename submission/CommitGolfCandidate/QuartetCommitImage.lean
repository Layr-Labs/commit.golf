import CommitGolf.Artifact
import CommitGolfCandidate.TwoPermutationManifest

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def image : Image := ⟨ArtifactEncoding.decode 32 Artifact.commitCode, ArtifactEncoding.decode 8 Artifact.commitData⟩
theorem exact_image : image = Artifact.submission.image .commit := rfl
def codeWord (index : Nat) : BitVec 32 :=
  if inside : index<261561 then Artifact.commitCode.get 32 ⟨index,inside⟩ else 0
def wordPC (index : Nat) : Word := BitVec.ofNat 64 (4096 + 4*index)

theorem fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 261561) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (codeWord index)=some instruction) :
    fetch image state=some (.base instruction) := by
  have address : state.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have code : image.code=ArtifactEncoding.decode 32 Artifact.commitCode := by
    simp only [image]
  have length : index< image.code.length := by
    rw [code,ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : image.code[index]?=some (Artifact.commitCode.get 32 ⟨index,inCode⟩) := by
    rw [List.getElem?_eq_getElem length,←List.getD_eq_getElem _ _ length,code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,address,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega,atIndex]
  have base : Manifest.decodeBase (Artifact.commitCode.get 32 ⟨index,inCode⟩)=some instruction := by
    simpa only [codeWord,dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (Artifact.commitCode.get 32 ⟨index,inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all


def quadPC (slot : Nat) : Word := wordPC (45227+3*slot)
def quadOp (part : Fin 3) : Instr :=
  if part.val=0 then .ECALL else if part.val=1 then .ADDI .x10 .x10 512 else .ADDI .x12 .x12 32
private theorem quad_words : ∀ slot : Fin 512, ∀ part : Fin 3,
    Manifest.decodeBase (codeWord (45227+3*slot.val+part.val))=some (quadOp part) := by decide +kernel
theorem fetch_quad (state : MachineState) (slot : Fin 512) (part : Fin 3)
    (pc : state.pc=quadPC slot.val+BitVec.ofNat 64 (4*part.val)) :
    fetch image state=some (.base (quadOp part)) := by
  have atWord : state.pc=wordPC (45227+3*slot.val+part.val) := by
    rw [pc,quadPC,wordPC,wordPC,←BitVec.ofNat_add]
    congr 1 <;> omega
  exact fetch_decoded state _ (by have := slot.isLt;have := part.isLt;omega) atWord _ (quad_words slot part)

def setupOps : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 0,.LUI .x19 131072,
   .ADD .x21 .x9 .x19,.SLLI .x22 .x19 2,.ADD .x22 .x21 .x22,.ADDI .x24 .x22 0,
   .LUI .x23 1,.LUI .x7 1,.ADDI .x7 .x7 2048,.ADD .x20 .x21 .x7,
   .ADDI .x5 .x0 2,.ADDI .x10 .x22 (-176),.ADDI .x11 .x0 24,.ECALL,
   .ADD .x22 .x22 .x7,.ADD .x25 .x24 .x7,.ADDI .x5 .x0 0,.ADDI .x11 .x0 200,
   .ADDI .x13 .x0 1,.JAL .x0 713356]
def quadSetupOps : List Instr := [.ADDI .x10 .x21 0,.SRLI .x7 .x19 2,.ADD .x12 .x9 .x7]
def upperSetupOps : List Instr := [.ADDI .x10 .x12 4032,.SRLI .x7 .x19 2,.SUB .x12 .x12 .x7,.ADDI .x12 .x12 4064,.ADDI .x11 .x0 64,.ADDI .x13 .x0 0]

private theorem setup_decoded : ∀ i : Fin 22, Manifest.decodeBase (codeWord (0+i.val)) =
    some ((setupOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_setup (s : MachineState) (i : Fin 22) (pc : s.pc=wordPC (0+i.val)) :
    fetch image s=some (.base ((setupOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (setup_decoded i)

private theorem quadSetup_decoded : ∀ i : Fin 3, Manifest.decodeBase (codeWord (45224+i.val)) =
    some ((quadSetupOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_quadSetup (s : MachineState) (i : Fin 3) (pc : s.pc=wordPC (45224+i.val)) :
    fetch image s=some (.base ((quadSetupOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (quadSetup_decoded i)

private theorem upperSetup_decoded : ∀ i : Fin 6, Manifest.decodeBase (codeWord (46765+i.val)) =
    some ((upperSetupOps[i.val]?).getD .EBREAK) := by decide +kernel
theorem fetch_upperSetup (s : MachineState) (i : Fin 6) (pc : s.pc=wordPC (46765+i.val)) :
    fetch image s=some (.base ((upperSetupOps[i.val]?).getD .EBREAK)) :=
  fetch_decoded s _ (by have := i.isLt;omega) pc _ (upperSetup_decoded i)

theorem fetch_leaf_branch (s : MachineState) (pc : s.pc=wordPC 45222) :
    fetch image s=some (.base (.BEQ .x20 .x25 8)) := fetch_decoded s 45222 (by decide) pc _ (by decide +kernel)

theorem fetch_leaf_jump (s : MachineState) (pc : s.pc=wordPC 45223) :
    fetch image s=some (.base (.JAL .x0 1916348)) := fetch_decoded s 45223 (by decide) pc _ (by decide +kernel)

theorem fetch_quad_branch (s : MachineState) (pc : s.pc=wordPC 46763) :
    fetch image s=some (.base (.BEQ .x10 .x24 8)) := fetch_decoded s 46763 (by decide) pc _ (by decide +kernel)

theorem fetch_quad_jump (s : MachineState) (pc : s.pc=wordPC 46764) :
    fetch image s=some (.base (.JAL .x0 2091004)) := fetch_decoded s 46764 (by decide) pc _ (by decide +kernel)

end TwoPermutationPrototype.QuartetCommit
