import CommitGolfCandidate.StudyCap
import CommitGolfCandidate.GroupOpenMark
import CommitGolfCandidate.GroupOpenCapMoves

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Opening (markBase trapdoorBase machineMarks markWord)

def capPreparation := CapStudy.capPreparation

theorem execute_cap_preparation (state : MachineState) (pc : state.pc = 0x1a24)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase) (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (771 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (capPreparation state) allowCoins
          return result.charge 771 0) :=
  CapStudy.execute_cap_preparation state pc base fuel allowCoins

theorem cap_preparation_context (state : MachineState) (groups : List Nat) (dest : Nat)
    (markBaseReg : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (heap : state.getReg .x25 = BitVec.ofNat 64 Opening.trapdoorBase)
    (leaves : state.getReg .x27 = 256#64)
    (proofStart : state.getReg .x20 = BitVec.ofNat 64 quartetProofBase)
    (pointer : state.getReg .x21 = BitVec.ofNat 64 dest)
    (marks : ∀ node, 255 < node → node < 512 → machineMarks state node = markWord groups node) :
    let after := capPreparation state
    after.pc = 0x1a54 ∧ CapPosition groups after 1 dest ∧ after.getReg .x30 = 7#64 := by
  obtain ⟨pc, root, countdown, live, values⟩ := CapStudy.cap_preparation_context state
    (markWord groups) marks
    (fun k pos upper => Opening.mark_word_parent groups ⟨k,upper⟩ pos)
  exact ⟨pc, ⟨⟨(live .x25 (by decide)).trans heap, (live .x26 (by decide)).trans markBaseReg,
      (live .x27 (by decide)).trans leaves, (live .x20 (by decide)).trans proofStart, values⟩,
      root, (live .x21 (by decide)).trans pointer⟩, countdown⟩


end TwoPermutationPrototype.GroupedOpening
