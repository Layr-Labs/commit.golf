import CommitGolfCandidate.CapCheckRootCodec
import CommitGolfCandidate.CapCheckCodecFinal
import CommitGolfCandidate.CapCheckFinishValue

/-! Actual terminating cap acceptance is canonical decoding to the original
claimed digest with no remaining complete words or partial bytes. Input
admission, phase readiness and the unchanged claimed bytes remain explicit.
This theorem concerns the cap phase, not the earlier lower-record parser. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] readBuffer capCheckDfsNext capCheckDfsValue

theorem cap_check_cap_acceptance (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (view : CapView 8) (state : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes commitment : Nat)
    (ready : CapCheckDfsReady limit marked (.visit 1) state)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (marks : CapViewMarks marked 1 view)
    (known : CapCheckKnownLeaves state 1 view)
    (claimed : state.getReg .x26=BitVec.ofNat 64 commitment)
    (commitmentAligned : commitment%8=0)
    (commitmentHigh : 32768≤commitment)
    (commitmentBound : commitment+32≤2^64) :
    (checkEvaluation oracle
      (capCheckDfsFinish marked 1022 (.visit 1) state)).1.exit=.success ↔
      capDecode oracle.compression view words=
        some (readBuffer state commitment 32,[]) ∧ tailBytes=0 := by
  have matchResult := cap_check_root_codec oracle limit marked view state cursor
    words tailBytes ready suffix marks known
  cases decoded : capDecode oracle.compression view words with
  | none =>
    rw [decoded] at matchResult
    change (capCheckDfsValue oracle marked 1022 (.visit 1) state).2=false at matchResult
    rw [cap_check_finish_exit_value]
    simp only [matchResult,Bool.false_eq_true,↓reduceIte,reduceCtorEq,false_and]
  | some pair =>
    rcases pair with ⟨root,rest⟩
    rw [decoded] at matchResult
    change (capCheckDfsValue oracle marked 1022 (.visit 1) state).2=true ∧
      capReadRoot (capCheckDfsValue oracle marked 1022 (.visit 1) state).1 1=root ∧
      ∃ finalCursor, CapCheckWordSuffix
        (capCheckDfsValue oracle marked 1022 (.visit 1) state).1 finalCursor rest tailBytes ∧
        CapCheckDfsReady limit marked .done
          (capCheckDfsValue oracle marked 1022 (.visit 1) state).1 at matchResult
    obtain ⟨passed,payload,finalCursor,finalSuffix,finalReady⟩ := matchResult
    have frame := cap_check_dfs_value_high oracle limit marked 1022 (.visit 1)
      state state ready (cap_high_bytes_refl state) passed
    have roots : (capCheckDfsValue oracle marked 1022 (.visit 1) state).1.getReg .x18=
        BitVec.ofNat 64 12288 := by
      simpa only [capBoundaryRootRegister,↓reduceIte] using finalReady.stable.roots
    have finalClaim := frame.2.trans claimed
    have final := cap_check_codec_final
      (capCheckDfsValue oracle marked 1022 (.visit 1) state).1
      finalCursor rest tailBytes commitment finalSuffix roots finalClaim commitmentAligned
    rw [payload,cap_high_bytes_read _ state commitment 32 commitmentHigh
      commitmentBound frame.1] at final
    rw [cap_check_finish_exit_value]
    simp only [passed,↓reduceIte,Option.some.injEq,Prod.mk.injEq]
    rw [final]
    tauto

end CommitGolfCandidate
