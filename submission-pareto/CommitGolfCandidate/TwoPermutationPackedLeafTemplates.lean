import CommitGolfCandidate.TwoPermutationManifest
import Mathlib.Tactic

/-! Artifact-independent decode templates for the raw 4096-leaf kernel.
Nonce offsets repeat every 128 leaves and heap offsets every 64. The two
64-leaf tiles in one 128-leaf period supply all instruction decodes; the
artifact-dependent module separately checks every delivered leaf word. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

def packed_wideFirstOps (_slot : Nat) : List Instr :=
  [.ADDI .x12 .x10 4064]

def packed_wideSecondOps (slot : Nat) : List Instr :=
  [.ADDI .x10 .x10 56, .SD .x10 .x10 0,
   .LD .x31 .x22 (BitVec.ofNat 12 (2048+16*(slot%256))), .SD .x10 .x31 8,
   .LD .x31 .x22 (BitVec.ofNat 12 (2048+16*(slot%256)+8)), .SD .x10 .x31 16,
   .ADDI .x12 .x20 (BitVec.ofNat 12 (32*(slot%64)))]

def packed_wideLeafOp (slot offset : Nat) : Instr :=
  (((packed_wideFirstOps slot) ++ [.ECALL] ++ packed_wideSecondOps slot ++ [.ECALL,.ADDI .x10 .x10 200])[offset]?).getD .EBREAK

/-- Exact ordinary RV64 words for one raw leaf. This formula has no artifact
dependency; all delivered words are checked against it in the fetch module. -/
def packed_leafTemplateWord (slot offset : Nat) : BitVec 32 :=
  match offset with
  | 0 => 0xfe050613
  | 1 => 0x00000073
  | 2 => 0x03850513
  | 3 => 0x00a53023
  | 4 => BitVec.ofNat 32 (0x000b3f83 + 2^20 * ((2048+16*(slot%256))%4096))
  | 5 => 0x01f53423
  | 6 => BitVec.ofNat 32 (0x000b3f83 + 2^20 * ((2048+16*(slot%256)+8)%4096))
  | 7 => 0x01f53823
  | 8 => BitVec.ofNat 32 (0x000a0613 + 2^20 * (32*(slot%64)))
  | 9 => 0x00000073
  | 10 => 0x0c850513
  | _ => 0x00100073

theorem packed_leafTemplateWord_periodic (slot offset : Nat) :
    packed_leafTemplateWord (slot%256) offset=packed_leafTemplateWord slot offset := by
  simp only [packed_leafTemplateWord,Nat.mod_mod,
    Nat.mod_mod_of_dvd slot (show 64∣256 by decide)]

theorem packed_wideLeafOp_periodic (slot offset : Nat) :
    packed_wideLeafOp (slot%256) offset=packed_wideLeafOp slot offset := by
  simp only [packed_wideLeafOp,packed_wideFirstOps,packed_wideSecondOps,Nat.mod_mod,
    Nat.mod_mod_of_dvd slot (show 64∣256 by decide)]

private def TemplateTileDecodes (tile : Nat) : Prop :=
  ∀ slot : Fin 64, ∀ offset : Fin 11,
    Manifest.decodeBase (packed_leafTemplateWord (64*tile+slot.val) offset.val)=
      some (packed_wideLeafOp (64*tile+slot.val) offset.val)

private theorem template0 : TemplateTileDecodes 0 := by unfold TemplateTileDecodes; decide +kernel
private theorem template1 : TemplateTileDecodes 1 := by unfold TemplateTileDecodes; decide +kernel
private theorem template2 : TemplateTileDecodes 2 := by unfold TemplateTileDecodes; decide +kernel
private theorem template3 : TemplateTileDecodes 3 := by unfold TemplateTileDecodes; decide +kernel

theorem packed_leaf_template_decode (slot : Fin 256) (offset : Fin 11) :
    Manifest.decodeBase (packed_leafTemplateWord slot.val offset.val)=
      some (packed_wideLeafOp slot.val offset.val) := by
  have bound : slot.val/64<4 := by have := slot.isLt; omega
  have group : TemplateTileDecodes (slot.val/64) := by
    generalize slot.val/64=tile at bound ⊢
    interval_cases tile
    · exact template0
    · exact template1
    · exact template2
    · exact template3
  have pos : 64*(slot.val/64)+slot.val%64=slot.val := by omega
  simpa only [Fin.val_mk,pos] using group ⟨slot.val%64,by omega⟩ offset

end TwoPermutationPrototype.RV64
