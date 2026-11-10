import CommitGolfCandidate.CapCheckCodecAlgebra
import CommitGolfCandidate.CapCheckSubtreeKnownLeaves

/-! Occupied internal nodes compose the two physical child traversals in
decoder order. The right subtree preserves the completed left root by its
write footprint; the parent then hashes those exact two roots. A failed child
prevents all later work. No initial internal-root equation is assumed. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckDfsNext capCheckDfsValue capCheckSubtreeValue

def CapCheckCodecCorrect (oracle : Oracle) (limit : Nat) (marked : Nat → Bool)
    {height : Nat} (view : CapView height) (node : Nat) : Prop :=
  ∀ state cursor words tailBytes,
    CapCheckDfsReady limit marked (.visit node) state →
    CapCheckWordSuffix state cursor words tailBytes →
    CapCheckKnownLeaves state node view →
    CapCheckCodecResult limit marked node tailBytes
      (capCheckSubtreeValue oracle marked height node state)
      (capDecode oracle.compression view words)

private theorem above_cursor (state : MachineState) (cursor : Nat)
    (words : List Digest) (tailBytes : Nat)
    (suffix : CapCheckWordSuffix state cursor words tailBytes) :
    22528≤(state.getReg .x25).toNat := by
  have small := cap_check_word_suffix_small state cursor words tailBytes suffix
  rw [suffix.pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.1]
  exact suffix.high

theorem cap_check_codec_internal (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) {height : Nat} (left right : CapView height)
    (node : Nat) (positive : 0<node) (internal : node<128)
    (leftLower : 128≤(2*node)*2^height)
    (leftUpper : (2*node+1)*2^height≤256)
    (rightLower : 128≤(2*node+1)*2^height)
    (rightUpper : (2*node+2)*2^height≤256)
    (marks : CapViewMarks marked node (.node left right))
    (occupied : capOccupied (.node left right)=true)
    (leftCorrect : CapCheckCodecCorrect oracle limit marked left (2*node))
    (rightCorrect : CapCheckCodecCorrect oracle limit marked right (2*node+1)) :
    CapCheckCodecCorrect oracle limit marked (.node left right) node := by
  intro state cursor words tailBytes ready suffix known
  obtain ⟨nodeMarks,leftMarks,rightMarks⟩ := marks
  obtain ⟨leftKnown,rightKnown⟩ := known
  have present : marked node=true := nodeMarks.trans occupied
  let entered := capCheckDfsNext oracle marked (.visit node) state
  have enteredFacts := cap_check_codec_enter oracle limit marked node state
    cursor words tailBytes ready suffix internal present
  have enteredLeft := cap_check_codec_known_frame oracle limit marked (.visit node)
    state cursor words tailBytes ready suffix
    (by simp only [capCheckDfsShort,present,↓reduceIte])
    left (2*node) leftLower leftUpper leftMarks leftKnown
  have enteredRight := cap_check_codec_known_frame oracle limit marked (.visit node)
    state cursor words tailBytes ready suffix
    (by simp only [capCheckDfsShort,present,↓reduceIte])
    right (2*node+1) rightLower rightUpper rightMarks rightKnown
  let leftResult := capCheckSubtreeValue oracle marked height (2*node) entered
  have leftMatch := leftCorrect entered cursor words tailBytes
    enteredFacts.2 enteredFacts.1 enteredLeft
  have entryOne := cap_check_one_value oracle marked (.visit node) state
    (by simp only [capCheckDfsShort,present,↓reduceIte])
  have run :
      capCheckSubtreeValue oracle marked (height+1) node state=
        capCheckValueThen leftResult (fun leftState =>
          capCheckValueThen
            (capCheckDfsValue oracle marked 1 (.advance (2*node)) leftState)
            (fun siblingState =>
              capCheckValueThen
                (capCheckSubtreeValue oracle marked height (2*node+1) siblingState)
                (capCheckDfsValue oracle marked 1 (.advance (2*node+1))))) := by
    rw [capCheckSubtreeValue,if_pos present,entryOne]
    rfl
  rw [cap_decode_node_known oracle.compression left right words occupied]
  cases leftDecode : capDecode oracle.compression left words with
  | none =>
    rw [leftDecode] at leftMatch
    change leftResult.2=false at leftMatch
    simp only [Option.bind_none,CapCheckCodecResult]
    rw [run,cap_check_then_rejected _ _ leftMatch]
    exact leftMatch
  | some leftPair =>
    rcases leftPair with ⟨leftRoot,leftRest⟩
    rw [leftDecode] at leftMatch
    change CapCheckCodecResult limit marked node tailBytes
      (capCheckSubtreeValue oracle marked (height+1) node state)
      (do let (rightRoot,rest) ← capDecode oracle.compression right leftRest
          return (combine oracle.compression leftRoot rightRoot,rest))
    change leftResult.2=true ∧ capReadRoot leftResult.1 (2*node)=leftRoot ∧
      ∃ nextCursor, CapCheckWordSuffix leftResult.1 nextCursor leftRest tailBytes ∧
        CapCheckDfsReady limit marked (.advance (2*node)) leftResult.1 at leftMatch
    obtain ⟨leftPassed,leftValue,leftCursor,leftSuffix,leftReady⟩ := leftMatch
    have rightAtLeft := cap_check_subtree_known_leaves oracle limit marked
      height (2*node) entered leftLower leftUpper enteredFacts.2
      (above_cursor entered cursor words tailBytes enteredFacts.1)
      right (2*node+1) rightLower rightUpper rightMarks enteredRight leftPassed
    let sibling := capCheckDfsNext oracle marked (.advance (2*node)) leftResult.1
    have siblingFacts := cap_check_codec_sibling oracle limit marked node leftResult.1
      leftCursor leftRest tailBytes leftReady leftSuffix positive internal
    have siblingKnown := cap_check_codec_known_frame oracle limit marked
      (.advance (2*node)) leftResult.1 leftCursor leftRest tailBytes leftReady
      leftSuffix rfl right (2*node+1) rightLower rightUpper rightMarks rightAtLeft
    have siblingOne := cap_check_one_value oracle marked (.advance (2*node))
      leftResult.1 rfl
    let rightResult := capCheckSubtreeValue oracle marked height (2*node+1) sibling
    have rightMatch := rightCorrect sibling leftCursor leftRest tailBytes
      siblingFacts.2.1 siblingFacts.1 siblingKnown
    cases rightDecode : capDecode oracle.compression right leftRest with
    | none =>
      rw [rightDecode] at rightMatch
      change rightResult.2=false at rightMatch
      simp only [Option.bind_some,Option.bind_none,CapCheckCodecResult]
      rw [run,cap_check_then_passed _ _ leftPassed,siblingOne]
      change (capCheckValueThen rightResult _).2=false
      rw [cap_check_then_rejected _ _ rightMatch]
      exact rightMatch
    | some rightPair =>
      rcases rightPair with ⟨rightRoot,rightRest⟩
      rw [rightDecode] at rightMatch
      change rightResult.2=true ∧ capReadRoot rightResult.1 (2*node+1)=rightRoot ∧
        ∃ nextCursor, CapCheckWordSuffix rightResult.1 nextCursor rightRest tailBytes ∧
          CapCheckDfsReady limit marked (.advance (2*node+1)) rightResult.1 at rightMatch
      obtain ⟨rightPassed,rightValue,rightCursor,rightSuffix,rightReady⟩ := rightMatch
      have leftFrame := cap_check_subtree_root_below oracle limit marked
        height (2*node+1) sibling rightLower rightUpper siblingFacts.2.1
        (above_cursor sibling leftCursor leftRest tailBytes siblingFacts.1)
        (2*node) (by omega) (by omega) rightPassed
      have leftFinal : capReadRoot rightResult.1 (2*node)=leftRoot :=
        leftFrame.trans (siblingFacts.2.2.trans leftValue)
      have parentRoot := cap_check_codec_parent oracle limit marked node rightResult.1
        rightCursor rightRest tailBytes rightReady rightSuffix positive internal
      rw [leftFinal,rightValue] at parentRoot
      have parentFacts := cap_check_codec_navigation oracle limit marked
        (.advance (2*node+1)) rightResult.1 rightCursor rightRest tailBytes
        rightReady rightSuffix rfl rfl
      have nonroot : 2*node+1≠1 := by omega
      have odd : (2*node+1)%2≠0 := by omega
      have half : (2*node+1)/2=node := by omega
      have parentControl : capControlStep marked (.advance (2*node+1))=.advance node := by
        simp only [capControlStep,nonroot,odd,↓reduceIte,half]
      rw [parentControl] at parentFacts
      have parentOne := cap_check_one_value oracle marked (.advance (2*node+1))
        rightResult.1 rfl
      simp only [Option.bind_some,CapCheckCodecResult]
      rw [run,cap_check_then_passed _ _ leftPassed,siblingOne]
      change CapCheckCodecResult limit marked node tailBytes
        (capCheckValueThen rightResult _) (some (_,rightRest))
      rw [cap_check_then_passed _ _ rightPassed,parentOne]
      exact ⟨rfl,parentRoot,rightCursor,parentFacts.1,parentFacts.2⟩

end CommitGolfCandidate
