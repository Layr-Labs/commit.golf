import CommitGolfCandidate.TwoPermutationWideParentImage

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def wideLeafIndex (slot : Nat) : Nat := 19+14*slot+slot/128+slot/256
def wideLeafPC (slot offset : Nat) : Word := BitVec.ofNat 64 (4096+4*(wideLeafIndex slot+offset))

def wideNonceOffset (slot byte : Nat) : BitVec 12 := BitVec.ofNat 12 (16*slot + byte + 2049)

def wideFirstOps (slot : Nat) : List Instr :=
  [.SD .x10 .x10 0,.SD .x10 .x0 8,.SD .x10 .x0 16,
   .LD .x31 .x22 (wideNonceOffset slot 0),.SD .x10 .x31 24,
   .LD .x31 .x22 (wideNonceOffset slot 8),.SD .x10 .x31 32,
   .ADDI .x12 .x10 0]

def wideHeapOffset (slot : Nat) : BitVec 12 := BitVec.ofNat 12 (32*(slot%128)+2049)

def wideSecondOps (slot : Nat) : List Instr :=
  [.ADDI .x10 .x10 96,.SD .x10 .x10 0,
   .ADDI .x12 .x20 (wideHeapOffset slot)]

def wideLeafOp (slot offset : Nat) : Instr :=
  (((wideFirstOps slot) ++ [.ECALL] ++ wideSecondOps slot ++ [.ECALL,.ADDI .x10 .x10 160])[offset]?).getD .EBREAK

private def wideCodeWord (index : Nat) : BitVec 32 :=
  if inCode : index < 261739 then Artifact.commitCode.get 32 ⟨index,inCode⟩ else 0

private def LeafTileDecodes (tile : Nat) : Prop :=
  ∀ slot : Fin 64, ∀ offset : Fin 14,
    Manifest.decodeBase (wideCodeWord (wideLeafIndex (64*tile+slot.val)+offset.val)) =
    some (wideLeafOp (64*tile+slot.val) offset.val)

private theorem tile0 : LeafTileDecodes 0 := by unfold LeafTileDecodes; decide +kernel
private theorem tile1 : LeafTileDecodes 1 := by unfold LeafTileDecodes; decide +kernel
private theorem tile2 : LeafTileDecodes 2 := by unfold LeafTileDecodes; decide +kernel
private theorem tile3 : LeafTileDecodes 3 := by unfold LeafTileDecodes; decide +kernel

theorem wide_leaf_decode (slot : Fin 256) (offset : Fin 14) :
    Manifest.decodeBase (wideCodeWord (wideLeafIndex slot.val+offset.val)) =
      some (wideLeafOp slot.val offset.val) := by
  have bound : slot.val/64 < 4 := by have := slot.isLt; omega
  have group : LeafTileDecodes (slot.val/64) := by
    generalize slot.val/64=tile at bound ⊢
    interval_cases tile
    · exact tile0
    · exact tile1
    · exact tile2
    · exact tile3
  have pos : 64*(slot.val/64)+slot.val%64=slot.val := by omega
  simpa only [Fin.val_mk,pos] using group ⟨slot.val%64,by omega⟩ offset

private theorem wide_fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 261739) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (wideCodeWord index)=some instruction) :
    fetch wideCommitImage state=some (.base instruction) := by
  have address : state.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have code : wideCommitImage.code=ArtifactEncoding.decode 32 Artifact.commitCode := by
    simp only [wideCommitImage]
  have length : index<wideCommitImage.code.length := by
    rw [code,ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : wideCommitImage.code[index]?=some (Artifact.commitCode.get 32 ⟨index,inCode⟩) := by
    rw [List.getElem?_eq_getElem length,←List.getD_eq_getElem _ _ length,code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,address,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega,atIndex]
  have base : Manifest.decodeBase (Artifact.commitCode.get 32 ⟨index,inCode⟩)=some instruction := by
    simpa only [wideCodeWord,dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (Artifact.commitCode.get 32 ⟨index,inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all

theorem wide_fetch_leaf (slot : Fin 256) (offset : Fin 14) (state : MachineState)
    (pc : state.pc=wideLeafPC slot.val offset.val) :
    fetch wideCommitImage state=some (.base (wideLeafOp slot.val offset.val)) := by
  have fits : wideLeafIndex slot.val+offset.val<261739 := by
    have := slot.isLt
    have := offset.isLt
    simp only [wideLeafIndex]
    omega
  exact wide_fetch_decoded state _ fits pc _ (wide_leaf_decode slot offset)

def heapRebaseIndex (tile : Nat) := wideLeafIndex (128*tile+127)+14
def nonceRebaseIndex (segment : Nat) := wideLeafIndex (256*segment+255)+15

private theorem heap_rebase_decoded : ∀ tile : Fin 2,
    Manifest.decodeBase (wideCodeWord (heapRebaseIndex tile.val))=
      some (.ADD .x20 .x20 .x7) := by decide +kernel

private theorem nonce_rebase_decoded : ∀ segment : Fin 1,
    Manifest.decodeBase (wideCodeWord (nonceRebaseIndex segment.val))=
      some (.ADD .x22 .x22 .x7) := by decide +kernel

theorem wide_fetch_heap_rebase (tile : Fin 2) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*heapRebaseIndex tile.val)) :
    fetch wideCommitImage state=some (.base (.ADD .x20 .x20 .x7)) := by
  have fits : heapRebaseIndex tile.val < 261739 := by unfold heapRebaseIndex wideLeafIndex; have := tile.isLt; omega
  exact wide_fetch_decoded state _ fits pc _ (heap_rebase_decoded tile)

theorem wide_fetch_nonce_rebase (segment : Fin 1) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*nonceRebaseIndex segment.val)) :
    fetch wideCommitImage state=some (.base (.ADD .x22 .x22 .x7)) := by
  have fits : nonceRebaseIndex segment.val < 261739 := by unfold nonceRebaseIndex wideLeafIndex; have := segment.isLt; omega
  exact wide_fetch_decoded state _ fits pc _ (nonce_rebase_decoded segment)

theorem wide_fetch_leaf_branch (state : MachineState) (pc : state.pc=18520) :
    fetch wideCommitImage state=some (.base (.BGEU .x20 .x21 16)) :=
  wide_fetch_decoded state 3606 (by decide) pc _ rfl

theorem wide_fetch_leaf_loop (state : MachineState) (pc : state.pc=18524) :
    fetch wideCommitImage state=some (.base (.JAL .x0 2082800)) :=
  wide_fetch_decoded state 3607 (by decide) pc _ rfl

def wideInitialOps : List Instr :=
  initialInstructions ++ [.ECALL] ++ readyInstructions ++ [.LUI .x7 1,.ADDI .x22 .x22 2047,.ADDI .x20 .x20 2047]

private theorem wide_prelude_decoded : ∀ i : Fin 19,
    Manifest.decodeBase (wideCodeWord i.val)=
      some ((wideInitialOps[i.val]?).getD .EBREAK) := by decide +kernel

theorem wide_fetch_initial (i : Fin 19) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*i.val)) :
    fetch wideCommitImage state=some (.base ((wideInitialOps[i.val]?).getD .EBREAK)) := by
  have fits : i.val<261739 := by have := i.isLt; omega
  exact wide_fetch_decoded state _ fits pc _ (wide_prelude_decoded i)

private theorem wide_parent_setup_decoded : ∀ i : Fin 5,
    Manifest.decodeBase (wideCodeWord (3610+i.val))=
      some ((parentSetupOps[i.val]?).getD .EBREAK) := by decide +kernel

theorem wide_fetch_parent_setup (i : Fin 5) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*(3610+i.val))) :
    fetch wideCommitImage state=some (.base ((parentSetupOps[i.val]?).getD .EBREAK)) := by
  have fits : 3610+i.val<261739 := by have := i.isLt; omega
  exact wide_fetch_decoded state _ fits pc _ (wide_parent_setup_decoded i)

end TwoPermutationPrototype.RV64
