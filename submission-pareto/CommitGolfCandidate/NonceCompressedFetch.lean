import CommitGolfCandidate.NonceCompressedPrograms
import CommitGolfCandidate.NonceCopyReady
import CommitGolfCandidate.NonceBackwardReady
import CommitGolfCandidate.CapMarkImage

/-! Exact instruction fetches for the two concrete nonce codec loops. The
ordinary-copy resource lemmas are instantiated only with these actual images. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def nonceCompactImage : Image := nonceCompressedProgram.image .opening
def nonceExpandedImage : Image := nonceCompressedProgram.image .check

theorem nonce_compact_copy_fetched : NonceCopyReady.Fetched nonceCompactImage 4620 := by
  intro state index bounded pc
  apply cap_image_fetch _ state (131+index) _ (by omega)
  · rw [pc]
    change BitVec.ofNat 64 4620+BitVec.ofNat 64 (4*index)=_
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · interval_cases index <;> rfl

theorem nonce_expanded_copy_fetched : NonceBackwardReady.Fetched nonceExpandedImage 5096 := by
  intro state index bounded pc
  apply cap_image_fetch _ state (250+index) _ (by omega)
  · rw [pc]
    change BitVec.ofNat 64 5096+BitVec.ofNat 64 (4*index)=_
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · interval_cases index <;> rfl

theorem nonce_compact_image_length : nonceCompactImage.code.length=259 := by decide
theorem nonce_expanded_image_length : nonceExpandedImage.code.length=547 := by decide

theorem nonce_compact_old_prefix :
    nonceCompactImage.code.take 110=(assemble (capOpeningCode LOG_LENGTH)).take 110 := by
  decide

/-- The packed checker keeps cap words 1..199 (retained core and the
never-executed filler) and the checker words 257..444 (leaf routine and truncation stubs). -/
theorem nonce_expanded_old_core :
    (nonceExpandedImage.code.drop 1).take 199=((assemble (capCheckCode LOG_LENGTH)).drop 1).take 199 := by
  decide

theorem nonce_expanded_old_leaf :
    (nonceExpandedImage.code.drop 257).take 188=(assemble (capCheckCode LOG_LENGTH)).drop 257 := by
  decide

theorem nonce_compact_prefix_word (index : Nat) (inside : index<110) :
    nonceCompactImage.code[index]?=(assemble (capOpeningCode LOG_LENGTH))[index]? := by
  have equal := congrArg (fun words : List (BitVec 32) => words[index]?) nonce_compact_old_prefix
  simpa only [List.getElem?_take, if_pos inside] using equal

theorem nonce_expanded_core_word (index : Nat) (positive : 1 ≤ index) (inside : index<200) :
    nonceExpandedImage.code[index]?=(assemble (capCheckCode LOG_LENGTH))[index]? := by
  have bounded : index-1<199 := by omega
  have equal := congrArg (fun words : List (BitVec 32) => words[index-1]?) nonce_expanded_old_core
  simp only [List.getElem?_take, if_pos bounded, List.getElem?_drop] at equal
  have offset : 1+(index-1)=index := by omega
  simpa only [offset] using equal

theorem nonce_expanded_leaf_word (index : Nat) (above : 257 ≤ index) (inside : index<445) :
    nonceExpandedImage.code[index]?=(assemble (capCheckCode LOG_LENGTH))[index]? := by
  have equal := congrArg (fun words : List (BitVec 32) => words[index-257]?) nonce_expanded_old_leaf
  have bounded : index-257<188 := by omega
  simp only [List.getElem?_take, if_pos bounded, List.getElem?_drop] at equal
  have offset : 257+(index-257)=index := by omega
  simpa only [offset] using equal

theorem nonce_fetch_at_index_congr (left right : Image) (state : MachineState)
    (index : Nat) (bounded : index<512)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (equal : left.code[index]?=right.code[index]?) :
    fetch left state=fetch right state := by
  have numeric : state.pc.toNat=4096+4*index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have aligned : 4096+4*index≥4096 ∧ (4096+4*index)%4=0 := by omega
  have offset : (4096+4*index-4096)/4=index := by omega
  simp only [fetch, numeric, if_pos aligned, offset, equal]

theorem nonce_compact_prefix_fetch (state : MachineState) (index : Nat)
    (inside : index<110) (pc : state.pc=BitVec.ofNat 64 (4096+4*index)) :
    fetch nonceCompactImage state=fetch ((capExperimental LOG_LENGTH).image .opening) state :=
  nonce_fetch_at_index_congr _ _ state index (by omega) pc (nonce_compact_prefix_word index inside)

theorem nonce_expanded_core_fetch (state : MachineState) (index : Nat)
    (positive : 1 ≤ index) (inside : index<200)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*index)) :
    fetch nonceExpandedImage state=fetch ((capExperimental LOG_LENGTH).image .check) state :=
  nonce_fetch_at_index_congr _ _ state index (by omega) pc (nonce_expanded_core_word index positive inside)

theorem nonce_expanded_leaf_fetch (state : MachineState) (index : Nat)
    (above : 257 ≤ index) (inside : index<445)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*index)) :
    fetch nonceExpandedImage state=fetch ((capExperimental LOG_LENGTH).image .check) state :=
  nonce_fetch_at_index_congr _ _ state index (by omega) pc (nonce_expanded_leaf_word index above inside)

end CommitGolfCandidate
