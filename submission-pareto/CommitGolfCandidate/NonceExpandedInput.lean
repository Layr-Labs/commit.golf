import CommitGolfCandidate.S6Codec
import CommitGolfCandidate.CapExperimentalABI

/-! The retained checker's input for a delivered proof: the same commitment, positions and values,
with the proof expanded by `s6ExpandRecords` (record `r` belongs to the `r`-th position in
increasing order). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def nonceExpandedInput (input : CheckInput) : CheckInput :=
  { input with proof := s6ExpandRecords (input.positions.sort (· ≤ ·)) input.proof }

/-- The delivered proofs the checker expands: whole records and whole 32-byte footer fields,
expanding to at most the proof capacity. -/
def NonceCheckValid (input : CheckInput) : Prop :=
  560 * input.positions.card ≤ input.proof.length ∧
    (input.proof.length - 560 * input.positions.card) % 32 = 0 ∧
    (nonceExpandedInput input).proof.length ≤ capProgram.sizes.proof

/-- The retained checker after its first word (`mv x26, x11`). -/
def nonceOldCheckTailState (input : CheckInput) : MachineState :=
  execInstrBr (capProgram.initialState .check input) (.ADDI .x26 .x11 0)

end CommitGolfCandidate
