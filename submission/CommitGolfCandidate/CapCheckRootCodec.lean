import CommitGolfCandidate.CapCheckSubtreeCodec
import CommitGolfCandidate.CapCheckRootValue

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckDfsNext capCheckDfsValue capCheckSubtreeValue

def CapCheckRootCodecResult (limit : Nat) (marked : Nat → Bool) (tailBytes : Nat)
    (result : MachineState × Bool) : Option (Digest × List Digest) → Prop
  | none => result.2=false
  | some (root,rest) =>
      result.2=true ∧ capReadRoot result.1 1=root ∧
        ∃ cursor, CapCheckWordSuffix result.1 cursor rest tailBytes ∧
          CapCheckDfsReady limit marked .done result.1

theorem cap_check_root_codec (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (view : CapView 8)
    (state : MachineState) (cursor : Nat) (words : List Digest) (tailBytes : Nat)
    (ready : CapCheckDfsReady limit marked (.visit 1) state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (marks : CapViewMarks marked 1 view)
    (known : CapCheckKnownLeaves state 1 view) :
    CapCheckRootCodecResult limit marked tailBytes
      (capCheckDfsValue oracle marked 1022 (.visit 1) state)
      (capDecode oracle.compression view words) := by
  have matchResult := cap_check_subtree_codec oracle limit marked view 1
    (by decide) (by decide) marks state cursor words tailBytes ready suffix known
  cases decoded : capDecode oracle.compression view words with
  | none =>
    rw [decoded] at matchResult
    change (capCheckSubtreeValue oracle marked 8 1 state).2=false at matchResult
    change (capCheckDfsValue oracle marked 1022 (.visit 1) state).2=false
    rw [cap_check_root_value,cap_check_then_rejected _ _ matchResult]
    exact matchResult
  | some pair =>
    rcases pair with ⟨root,rest⟩
    rw [decoded] at matchResult
    change (capCheckSubtreeValue oracle marked 8 1 state).2=true ∧
      capReadRoot (capCheckSubtreeValue oracle marked 8 1 state).1 1=root ∧
      ∃ finalCursor, CapCheckWordSuffix
        (capCheckSubtreeValue oracle marked 8 1 state).1 finalCursor rest tailBytes ∧
        CapCheckDfsReady limit marked (.advance 1)
          (capCheckSubtreeValue oracle marked 8 1 state).1 at matchResult
    obtain ⟨passed,payload,finalCursor,finalSuffix,finalReady⟩ := matchResult
    let last := (capCheckSubtreeValue oracle marked 8 1 state).1
    have nextFacts := cap_check_codec_navigation oracle limit marked (.advance 1)
      last finalCursor rest tailBytes finalReady finalSuffix rfl rfl
    have small := cap_check_word_suffix_small last finalCursor rest tailBytes finalSuffix
    have above : 32768≤(last.getReg .x25).toNat := by
      rw [finalSuffix.pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.1]
      exact finalSuffix.high
    have rootFrame := cap_check_dfs_next_roots oracle limit marked (.advance 1)
      last finalReady above 1 (by decide)
    simp only [capCheckRootStep,if_pos (Or.inl (rfl : (1:Nat)=1))] at rootFrame
    rw [cap_check_root_value,cap_check_then_passed _ _ passed]
    change (true=true) ∧ capReadRoot (capCheckDfsNext oracle marked (.advance 1) last) 1=root ∧
      ∃ finalCursor, CapCheckWordSuffix
        (capCheckDfsNext oracle marked (.advance 1) last) finalCursor rest tailBytes ∧
        CapCheckDfsReady limit marked .done
          (capCheckDfsNext oracle marked (.advance 1) last)
    exact ⟨rfl,rootFrame.trans payload,finalCursor,nextFacts.1,nextFacts.2⟩

end CommitGolfCandidate
