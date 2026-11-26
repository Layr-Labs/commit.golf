import CommitGolfCandidate.TwoPermutationPackedOpeningImage
import CommitGolfCandidate.OpeningWordCopyFinish

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open CommitGolfCandidate.OpeningWordCopy
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def CopySite.fast : CopySite → Bool
  | .nonce | .firstSibling => true
  | .sibling level => decide (level.val=0 ∨ level.val%2=1)
  | .cap => false

def CopySite.cycles (site : CopySite) : Nat :=
  if site.fast then site.halfwords+2 else 2*site.halfwords

def WordPairDecodes (site : CopySite) (offset : Nat) : Prop :=
  (openingImage.code[site.start+2*offset]?).bind Opening.decodeBase =
      some (.LWU .x31 .x7 (BitVec.ofNat 12 (4*offset))) ∧
    (openingImage.code[site.start+2*offset+1]?).bind Opening.decodeBase =
      some (.SW .x21 .x31 (BitVec.ofNat 12 (4*offset)))

private instance (site : CopySite) (offset : Nat) : Decidable (WordPairDecodes site offset) := by
  unfold WordPairDecodes
  infer_instance

theorem fast_pairs_decoded (site : CopySite) (fast : site.fast=true)
    (offset : Fin (site.halfwords/2)) : WordPairDecodes site offset.val := by
  cases site with
  | nonce => exact (show ∀ i : Fin 4, WordPairDecodes .nonce i.val by decide) offset
  | firstSibling => exact (show ∀ i : Fin 8, WordPairDecodes .firstSibling i.val by decide) offset
  | sibling level =>
    exact (show ∀ j : Fin 15, (CopySite.sibling j).fast=true →
      ∀ i : Fin ((CopySite.sibling j).halfwords/2), WordPairDecodes (.sibling j) i.val by decide) level fast offset
  | cap => simp [CopySite.fast] at fast

def fastWordCode (site : CopySite) (fast : site.fast=true) : WordCode where
  image := openingImage
  start := site.start
  words := site.halfwords/2
  offsetBound := by cases site <;> simp [CopySite.halfwords] <;> (try split_ifs) <;> decide
  load := fun j inside state pc => by
    apply packed_fetch_base state (site.start+2*j) _ _ pc (fast_pairs_decoded site fast ⟨j,inside⟩).1
    have halfwords : 0 < site.halfwords := by
      cases site <;> simp [CopySite.halfwords] <;> (try split_ifs) <;> decide
    have bound := copy_site_inside site ⟨j,by omega⟩
    change site.start+2*j+1<667 at bound
    omega
  store := fun j inside state pc => by
    apply packed_fetch_base state (site.start+2*j+1) _ _ pc (fast_pairs_decoded site fast ⟨j,inside⟩).2
    have halfwords : 0 < site.halfwords := by
      cases site <;> simp [CopySite.halfwords] <;> (try split_ifs) <;> decide
    exact copy_site_inside site ⟨j,by omega⟩

def SuffixDecodes (site : CopySite) (offset : Nat) : Prop :=
  (openingImage.code[site.start+2*(site.halfwords/2)+offset]?).bind Opening.decodeBase =
    some ((finishInstructions site.halfwords)[offset]?.getD .EBREAK)

private instance (site : CopySite) (offset : Nat) : Decidable (SuffixDecodes site offset) := by
  unfold SuffixDecodes
  infer_instance

theorem fast_suffix_decoded (site : CopySite) (fast : site.fast=true)
    (offset : Fin (finishInstructions site.halfwords).length) : SuffixDecodes site offset.val := by
  cases site with
  | nonce => exact (show ∀ i : Fin 2, SuffixDecodes .nonce i.val by decide) offset
  | firstSibling => exact (show ∀ i : Fin 2, SuffixDecodes .firstSibling i.val by decide) offset
  | sibling level =>
    exact (show ∀ j : Fin 15, (CopySite.sibling j).fast=true →
      ∀ i : Fin (finishInstructions (CopySite.sibling j).halfwords).length,
        SuffixDecodes (.sibling j) i.val by decide) level fast offset
  | cap => simp [CopySite.fast] at fast

theorem fast_width (site : CopySite) : FieldWidth site.halfwords := by
  cases site <;> simp [FieldWidth,CopySite.halfwords] <;> (try split_ifs) <;> tauto

theorem fast_suffix_fetch (site : CopySite) (fast : site.fast=true)
    (offset : Fin (finishInstructions site.halfwords).length) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*(site.start+2*(site.halfwords/2)+offset.val))) :
    fetch openingImage state = some (.base ((finishInstructions site.halfwords)[offset.val]?.getD .EBREAK)) := by
  apply packed_fetch_base _ _ _ _ pc (fast_suffix_decoded site fast offset)
  let j : Nat := offset.val
  have inside : j < (finishInstructions site.halfwords).length := offset.isLt
  change site.start+2*(site.halfwords/2)+j<667
  have width := fast_width site
  have boundary := copy_site_inside site ⟨site.halfwords-1, by rcases width with h | h | h <;> omega⟩
  change site.start+2*(site.halfwords-1)+1<667 at boundary
  rcases width with width | width | width <;> rw [width] at inside boundary ⊢ <;>
    norm_num [finishInstructions] at inside boundary ⊢ <;> omega

def ActualPairDecodes (site : CopySite) (offset : Nat) : Prop :=
    (openingImage.code[site.start+2*offset]?).bind Opening.decodeBase = some (copyLoad offset) ∧
    (openingImage.code[site.start+2*offset+1]?).bind Opening.decodeBase = some (copyStore offset)

private instance (site : CopySite) (offset : Nat) : Decidable (ActualPairDecodes site offset) := by
  unfold ActualPairDecodes
  infer_instance

theorem slow_pairs_decoded (site : CopySite) (slow : site.fast=false)
    (offset : Fin site.halfwords) : ActualPairDecodes site offset.val := by
  cases site with
  | nonce => simp [CopySite.fast] at slow
  | firstSibling => simp [CopySite.fast] at slow
  | sibling level =>
    exact (show ∀ j : Fin 15, (CopySite.sibling j).fast=false →
      ∀ i : Fin (CopySite.sibling j).halfwords, ActualPairDecodes (.sibling j) i.val by decide) level slow offset
  | cap => exact (show ∀ i : Fin 15, ActualPairDecodes .cap i.val by decide) offset

end TwoPermutationPrototype.PackedOpening
