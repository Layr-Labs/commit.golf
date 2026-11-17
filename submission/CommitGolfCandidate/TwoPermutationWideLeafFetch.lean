import CommitGolfCandidate.TwoPermutationWideParentImage

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def wideLeafIndex (slot : Nat) : Nat := 18+14*slot+slot/64+slot/128
def wideLeafPC (slot offset : Nat) : Word := BitVec.ofNat 64 (4096+4*(wideLeafIndex slot+offset))

def wideFirstOps (slot : Nat) : List Instr :=
  [.SD .x10 .x10 0,.SD .x10 .x0 8,.SD .x10 .x0 16,
   .LD .x31 .x22 (BitVec.ofNat 12 (16*(slot%128))),.SD .x10 .x31 24,
   .LD .x31 .x22 (BitVec.ofNat 12 (16*(slot%128)+8)),.SD .x10 .x31 32,
   .ADDI .x12 .x10 0]

def wideSecondOps (slot : Nat) : List Instr :=
  [.ADDI .x10 .x10 96,.SD .x10 .x10 0,
   .ADDI .x12 .x20 (BitVec.ofNat 12 (32*(slot%64)))]

def wideLeafOp (slot offset : Nat) : Instr :=
  (((wideFirstOps slot) ++ [.ECALL] ++ wideSecondOps slot ++ [.ECALL,.ADDI .x10 .x10 160])[offset]?).getD .EBREAK

private def wideCodeWord (index : Nat) : BitVec 32 :=
  if inCode : index < 201007 then Artifact.commitCode.get 32 ⟨index,inCode⟩ else 0

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
    (inCode : index < 201007) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
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
  have fits : wideLeafIndex slot.val+offset.val<201007 := by
    have := slot.isLt
    have := offset.isLt
    simp only [wideLeafIndex]
    omega
  exact wide_fetch_decoded state _ fits pc _ (wide_leaf_decode slot offset)

def heapRebaseIndex (tile : Nat) := wideLeafIndex (64*tile+63)+14
def nonceRebaseIndex (segment : Nat) := wideLeafIndex (128*segment+127)+15

private theorem heap_rebase_decoded : ∀ tile : Fin 4,
    Manifest.decodeBase (wideCodeWord (heapRebaseIndex tile.val))=
      some (.ADDI .x20 .x12 32) := by decide +kernel

private theorem nonce_rebase_decoded : ∀ segment : Fin 2,
    Manifest.decodeBase (wideCodeWord (nonceRebaseIndex segment.val))=
      some (.ADD .x22 .x22 .x7) := by decide +kernel

theorem wide_fetch_heap_rebase (tile : Fin 4) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*heapRebaseIndex tile.val)) :
    fetch wideCommitImage state=some (.base (.ADDI .x20 .x12 32)) := by
  have fits : heapRebaseIndex tile.val < 201007 := by unfold heapRebaseIndex wideLeafIndex; have := tile.isLt; omega
  exact wide_fetch_decoded state _ fits pc _ (heap_rebase_decoded tile)

theorem wide_fetch_nonce_rebase (segment : Fin 2) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*nonceRebaseIndex segment.val)) :
    fetch wideCommitImage state=some (.base (.ADD .x22 .x22 .x7)) := by
  have fits : nonceRebaseIndex segment.val < 201007 := by unfold nonceRebaseIndex wideLeafIndex; have := segment.isLt; omega
  exact wide_fetch_decoded state _ fits pc _ (nonce_rebase_decoded segment)

theorem wide_fetch_leaf_branch (state : MachineState) (pc : state.pc=18528) :
    fetch wideCommitImage state=some (.base (.BEQ .x20 .x21 8)) :=
  wide_fetch_decoded state 3608 (by decide) pc _ rfl

theorem wide_fetch_leaf_loop (state : MachineState) (pc : state.pc=18532) :
    fetch wideCommitImage state=some (.base (.JAL .x0 2082788)) :=
  wide_fetch_decoded state 3609 (by decide) pc _ rfl

def wideInitialOps : List Instr :=
  initialInstructions ++ [.ECALL] ++ readyInstructions ++ [.LUI .x7 1,.ADDI .x7 .x7 2048]

private theorem wide_prelude_decoded : ∀ i : Fin 18,
    Manifest.decodeBase (wideCodeWord i.val)=
      some ((wideInitialOps[i.val]?).getD .EBREAK) := by decide +kernel

theorem wide_fetch_initial (i : Fin 18) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*i.val)) :
    fetch wideCommitImage state=some (.base ((wideInitialOps[i.val]?).getD .EBREAK)) := by
  have fits : i.val<201007 := by have := i.isLt; omega
  exact wide_fetch_decoded state _ fits pc _ (wide_prelude_decoded i)

private theorem wide_parent_setup_decoded : ∀ i : Fin 5,
    Manifest.decodeBase (wideCodeWord (3610+i.val))=
      some ((parentSetupOps[i.val]?).getD .EBREAK) := by decide +kernel

theorem wide_fetch_parent_setup (i : Fin 5) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*(3610+i.val))) :
    fetch wideCommitImage state=some (.base ((parentSetupOps[i.val]?).getD .EBREAK)) := by
  have fits : 3610+i.val<201007 := by have := i.isLt; omega
  exact wide_fetch_decoded state _ fits pc _ (wide_parent_setup_decoded i)

end TwoPermutationPrototype.RV64
