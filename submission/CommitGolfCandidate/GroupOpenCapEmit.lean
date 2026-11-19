import CommitGolfCandidate.GroupOpenCapEmitPlain
import CommitGolfCandidate.GroupOpenCapEmitFold
import CommitGolfCandidate.GroupOpenCapSubtree

/-! T238 cap emit block (opener rows 668..700 with WK 855 and WS 859): the plain node (GroupOpenCapEmitPlain) and
the 8th node of a group (GroupOpenCapEmitFold) give the frozen `EmitCap238`; the root cap cursor on top of it. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64


theorem emit_cap238 : EmitCap238 := by
  intro groups state node dest count bounded position counter small pc separate aligned fits
  by_cases zero : count = 0
  · have sep : Opening.proofBase+210 ≤ dest := by rw [if_pos zero] at separate; exact separate
    obtain ⟨after, r, p, pos, x30, bytes, fold, frame⟩ :=
      emit_cap238_fold groups state node dest bounded position (by rw [counter, zero]) pc sep aligned fits
    refine ⟨after, ?_, p, ?_, ?_, ?_, fun _ => fold, fun a h t => frame a h (zero ▸ t)⟩
    · rw [if_pos zero]; exact r
    · rw [if_pos zero]; exact pos
    · rw [if_pos zero]; exact x30
    · rw [if_pos zero]; exact bytes
  · have sep : Opening.proofBase ≤ dest := by rw [if_neg zero] at separate; omega
    obtain ⟨after, r, p, pos, x30, bytes, frame⟩ :=
      emit_cap238_plain groups state node dest count bounded position counter (by omega) small pc sep aligned fits
    refine ⟨after, ?_, p, ?_, ?_, ?_, fun h => absurd h zero, frame⟩
    · rw [if_neg zero]; exact r
    · rw [if_neg zero]; exact pos
    · rw [if_neg zero]; exact x30
    · rw [if_neg zero]; exact bytes

theorem cap_subtree (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (span : Opening.CapSpan node height) (position : CapPosition groups state node dest)
    (pc : state.pc=0x1a54) (separate : Opening.proofBase ≤ dest) (aligned : dest%2=0)
    (fits : dest+capOffset (Sampling.capFrontierNodes groups node height).length+2 ≤ MEMORY_BYTES)
    (counter : state.getReg .x30=7#64) :
    ∃ after, RunsOpeningBlock state after (capWalkCycles groups node height dest 0) ∧
      after.pc=0x1af4 ∧
      CapPosition groups after node (dest+capOffset (Sampling.capFrontierNodes groups node height).length) ∧
      (∀ address<2^64, address<dest ∨ dest+capOffset (Sampling.capFrontierNodes groups node height).length ≤ address →
        after.getByte (BitVec.ofNat 64 address)=state.getByte (BitVec.ofNat 64 address)) ∧
      bytesAt after dest (capOffset (Sampling.capFrontierNodes groups node height).length)=
        foldNodes ((Sampling.capFrontierNodes groups node height).map (fun n => readBuffer state (Opening.capDigestAddress n) 32)) :=
  cap_subtree_of_emit emit_cap238 groups state node height dest span position pc separate aligned fits counter

end TwoPermutationPrototype.GroupedOpening
