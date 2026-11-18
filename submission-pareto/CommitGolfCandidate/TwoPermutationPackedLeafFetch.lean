import CommitGolfCandidate.MixedWidthParentImage
import CommitGolfCandidate.TwoPermutationPackedLeafTemplates

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def packed_wideLeafIndex (slot : Nat) : Nat := 22+11*slot+slot/64+slot/256
def packed_wideLeafPC (slot offset : Nat) : Word := BitVec.ofNat 64 (4096+4*(packed_wideLeafIndex slot+offset))

def packed_wideCodeWord (index : Nat) : BitVec 32 :=
  if inCode : index < 233357 then Artifact.commitCode.get 32 ⟨index,inCode⟩ else 0

private def LeafTileWordsMatch (tile : Nat) : Prop :=
  ∀ slot : Fin 64, ∀ offset : Fin 11,
    packed_wideCodeWord (packed_wideLeafIndex (64*tile+slot.val)+offset.val)=
      packed_leafTemplateWord (64*tile+slot.val) offset.val

private theorem words0 : LeafTileWordsMatch 0 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words1 : LeafTileWordsMatch 1 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words2 : LeafTileWordsMatch 2 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words3 : LeafTileWordsMatch 3 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words4 : LeafTileWordsMatch 4 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words5 : LeafTileWordsMatch 5 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words6 : LeafTileWordsMatch 6 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words7 : LeafTileWordsMatch 7 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words8 : LeafTileWordsMatch 8 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words9 : LeafTileWordsMatch 9 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words10 : LeafTileWordsMatch 10 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words11 : LeafTileWordsMatch 11 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words12 : LeafTileWordsMatch 12 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words13 : LeafTileWordsMatch 13 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words14 : LeafTileWordsMatch 14 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words15 : LeafTileWordsMatch 15 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words16 : LeafTileWordsMatch 16 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words17 : LeafTileWordsMatch 17 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words18 : LeafTileWordsMatch 18 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words19 : LeafTileWordsMatch 19 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words20 : LeafTileWordsMatch 20 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words21 : LeafTileWordsMatch 21 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words22 : LeafTileWordsMatch 22 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words23 : LeafTileWordsMatch 23 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words24 : LeafTileWordsMatch 24 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words25 : LeafTileWordsMatch 25 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words26 : LeafTileWordsMatch 26 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words27 : LeafTileWordsMatch 27 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words28 : LeafTileWordsMatch 28 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words29 : LeafTileWordsMatch 29 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words30 : LeafTileWordsMatch 30 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words31 : LeafTileWordsMatch 31 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words32 : LeafTileWordsMatch 32 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words33 : LeafTileWordsMatch 33 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words34 : LeafTileWordsMatch 34 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words35 : LeafTileWordsMatch 35 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words36 : LeafTileWordsMatch 36 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words37 : LeafTileWordsMatch 37 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words38 : LeafTileWordsMatch 38 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words39 : LeafTileWordsMatch 39 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words40 : LeafTileWordsMatch 40 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words41 : LeafTileWordsMatch 41 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words42 : LeafTileWordsMatch 42 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words43 : LeafTileWordsMatch 43 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words44 : LeafTileWordsMatch 44 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words45 : LeafTileWordsMatch 45 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words46 : LeafTileWordsMatch 46 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words47 : LeafTileWordsMatch 47 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words48 : LeafTileWordsMatch 48 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words49 : LeafTileWordsMatch 49 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words50 : LeafTileWordsMatch 50 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words51 : LeafTileWordsMatch 51 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words52 : LeafTileWordsMatch 52 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words53 : LeafTileWordsMatch 53 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words54 : LeafTileWordsMatch 54 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words55 : LeafTileWordsMatch 55 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words56 : LeafTileWordsMatch 56 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words57 : LeafTileWordsMatch 57 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words58 : LeafTileWordsMatch 58 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words59 : LeafTileWordsMatch 59 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words60 : LeafTileWordsMatch 60 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words61 : LeafTileWordsMatch 61 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words62 : LeafTileWordsMatch 62 := by unfold LeafTileWordsMatch; decide +kernel
private theorem words63 : LeafTileWordsMatch 63 := by unfold LeafTileWordsMatch; decide +kernel

/-- Every delivered leaf word is still checked, but no decoder is run in these
64 tables. The two reusable templates supply the decode theorem afterward. -/
private theorem packed_wide_leaf_word_matches (slot : Fin 4096) (offset : Fin 11) :
    packed_wideCodeWord (packed_wideLeafIndex slot.val+offset.val)=
      packed_leafTemplateWord slot.val offset.val := by
  have bound : slot.val/64<64 := by have := slot.isLt; omega
  have group : LeafTileWordsMatch (slot.val/64) := by
    generalize slot.val/64=tile at bound ⊢
    interval_cases tile
    · exact words0
    · exact words1
    · exact words2
    · exact words3
    · exact words4
    · exact words5
    · exact words6
    · exact words7
    · exact words8
    · exact words9
    · exact words10
    · exact words11
    · exact words12
    · exact words13
    · exact words14
    · exact words15
    · exact words16
    · exact words17
    · exact words18
    · exact words19
    · exact words20
    · exact words21
    · exact words22
    · exact words23
    · exact words24
    · exact words25
    · exact words26
    · exact words27
    · exact words28
    · exact words29
    · exact words30
    · exact words31
    · exact words32
    · exact words33
    · exact words34
    · exact words35
    · exact words36
    · exact words37
    · exact words38
    · exact words39
    · exact words40
    · exact words41
    · exact words42
    · exact words43
    · exact words44
    · exact words45
    · exact words46
    · exact words47
    · exact words48
    · exact words49
    · exact words50
    · exact words51
    · exact words52
    · exact words53
    · exact words54
    · exact words55
    · exact words56
    · exact words57
    · exact words58
    · exact words59
    · exact words60
    · exact words61
    · exact words62
    · exact words63
  have pos : 64*(slot.val/64)+slot.val%64=slot.val := by omega
  simpa only [Fin.val_mk,pos] using group ⟨slot.val%64,by omega⟩ offset

theorem packed_wide_leaf_decode (slot : Fin 4096) (offset : Fin 11) :
    Manifest.decodeBase (packed_wideCodeWord (packed_wideLeafIndex slot.val+offset.val))=
      some (packed_wideLeafOp slot.val offset.val) := by
  rw [packed_wide_leaf_word_matches slot offset]
  have template := packed_leaf_template_decode ⟨slot.val%256,Nat.mod_lt _ (by decide)⟩ offset
  simpa only [Fin.val_mk,packed_leafTemplateWord_periodic,packed_wideLeafOp_periodic] using template

theorem packed_wide_fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 233357) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (packed_wideCodeWord index)=some instruction) :
    fetch packedWideCommitImage state=some (.base instruction) := by
  have address : state.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have code : packedWideCommitImage.code=ArtifactEncoding.decode 32 Artifact.commitCode := by
    simp only [packedWideCommitImage]
  have length : index<packedWideCommitImage.code.length := by
    rw [code,ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : packedWideCommitImage.code[index]?=some (Artifact.commitCode.get 32 ⟨index,inCode⟩) := by
    rw [List.getElem?_eq_getElem length,←List.getD_eq_getElem _ _ length,code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,address,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega,atIndex]
  have base : Manifest.decodeBase (Artifact.commitCode.get 32 ⟨index,inCode⟩)=some instruction := by
    simpa only [packed_wideCodeWord,dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (Artifact.commitCode.get 32 ⟨index,inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all

theorem packed_wide_fetch_leaf (slot : Fin 4096) (offset : Fin 11) (state : MachineState)
    (pc : state.pc=packed_wideLeafPC slot.val offset.val) :
    fetch packedWideCommitImage state=some (.base (packed_wideLeafOp slot.val offset.val)) := by
  have fits : packed_wideLeafIndex slot.val+offset.val<233357 := by
    have := slot.isLt
    have := offset.isLt
    simp only [packed_wideLeafIndex]
    omega
  exact packed_wide_fetch_decoded state _ fits pc _ (packed_wide_leaf_decode slot offset)

def packed_heapRebaseIndex (tile : Nat) := packed_wideLeafIndex (64*tile+63)+11
def packed_nonceRebaseIndex (segment : Nat) := packed_wideLeafIndex (256*segment+255)+12

private theorem heap_rebase_decoded : ∀ tile : Fin 64,
    Manifest.decodeBase (packed_wideCodeWord (packed_heapRebaseIndex tile.val))=
      some (.ADDI .x20 .x12 32) := by decide +kernel

private theorem nonce_rebase_decoded : ∀ segment : Fin 16,
    Manifest.decodeBase (packed_wideCodeWord (packed_nonceRebaseIndex segment.val))=
      some (.ADD .x22 .x22 .x7) := by decide +kernel

theorem packed_wide_fetch_heap_rebase (tile : Fin 64) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*packed_heapRebaseIndex tile.val)) :
    fetch packedWideCommitImage state=some (.base (.ADDI .x20 .x12 32)) := by
  have fits : packed_heapRebaseIndex tile.val < 233357 := by unfold packed_heapRebaseIndex packed_wideLeafIndex; have := tile.isLt; omega
  exact packed_wide_fetch_decoded state _ fits pc _ (heap_rebase_decoded tile)

theorem packed_wide_fetch_nonce_rebase (segment : Fin 16) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*packed_nonceRebaseIndex segment.val)) :
    fetch packedWideCommitImage state=some (.base (.ADD .x22 .x22 .x7)) := by
  have fits : packed_nonceRebaseIndex segment.val < 233357 := by unfold packed_nonceRebaseIndex packed_wideLeafIndex; have := segment.isLt; omega
  exact packed_wide_fetch_decoded state _ fits pc _ (nonce_rebase_decoded segment)

theorem packed_wide_fetch_leaf_branch (state : MachineState) (pc : state.pc=184728) :
    fetch packedWideCommitImage state=some (.base (.BEQ .x20 .x21 8)) :=
  packed_wide_fetch_decoded state 45158 (by decide) pc _ rfl

theorem packed_wide_fetch_leaf_loop (state : MachineState) (pc : state.pc=184732) :
    fetch packedWideCommitImage state=some (.base (.JAL .x0 1916604)) :=
  packed_wide_fetch_decoded state 45159 (by decide) pc _ rfl

def packed_wideInitialOps : List Instr :=
  (initialInstructions.take 9 ++ [.ADDI .x10 .x22 (-176),.ADDI .x11 .x0 24]) ++ [.ECALL] ++ (readyInstructions.take 3 ++ [.JAL .x0 932572]) ++ [.SLLI .x7 .x13 11,.ADD .x22 .x22 .x7,.SLLI .x7 .x7 1,.ADDI .x0 .x0 0,.ADDI .x0 .x0 0,.ADDI .x10 .x10 40]

private theorem packed_wide_prelude_decoded : ∀ i : Fin 22,
    Manifest.decodeBase (packed_wideCodeWord i.val)=
      some ((packed_wideInitialOps[i.val]?).getD .EBREAK) := by decide +kernel

theorem packed_wide_fetch_initial (i : Fin 22) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*i.val)) :
    fetch packedWideCommitImage state=some (.base ((packed_wideInitialOps[i.val]?).getD .EBREAK)) := by
  have fits : i.val<233357 := by have := i.isLt; omega
  exact packed_wide_fetch_decoded state _ fits pc _ (packed_wide_prelude_decoded i)

private theorem packed_wide_parent_setup_decoded : ∀ i : Fin 5,
    Manifest.decodeBase (packed_wideCodeWord (45160+i.val))=
      some ((parentSetupOps[i.val]?).getD .EBREAK) := by decide +kernel

theorem packed_wide_fetch_parent_setup (i : Fin 5) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*(45160+i.val))) :
    fetch packedWideCommitImage state=some (.base ((parentSetupOps[i.val]?).getD .EBREAK)) := by
  have fits : 45160+i.val<233357 := by have := i.isLt; omega
  exact packed_wide_fetch_decoded state _ fits pc _ (packed_wide_parent_setup_decoded i)

end TwoPermutationPrototype.RV64
