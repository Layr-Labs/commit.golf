import CommitGolfCandidate.ReconstructedOpeningNodes
import CommitGolfCandidate.ReconstructedOpeningRead
import CommitGolfCandidate.ReconstructedHonestSizeRows

namespace CommitGolfCandidate.Reconstruction.CapEntry
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open CommitBlocks (addr)
abbrev W := BitVec.ofNat 64

def flags (ps : Positions) (i : Nat) : Bool := (Frontier.flags (ps.sort (·≤·)))[i]?.getD false

/-- The caller of the cap retains the two stack registers, the saved return PC and
two mask spills, the lookup tables, and the committed heap cells in depths 1–9. -/
structure Source (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) : Prop where
  stack : s.getReg .x2 = 68719474016
  frame : s.getReg .x8 = 68719476336
  saved : s.getMem 68719476328 = 4176
  shiftMask : s.getMem 68719474112 = 4294967295
  headerMask : s.getMem 68719474104 = 2147483647
  lows : ∀ d : Fin 10, s.getMem (W (2097152+8*d.val)) = W (Encoding.lows d.val)
  widths : ∀ d : Fin 10, s.getMem (W (2097352+8*d.val)) = W (Binding.width d.val)
  tree : ∀ (d j k : Nat), 0<d → d≤9 → CommitParents.Cell d j → k<4 →
    s.getMem (W (CommitParents.addr d j+8*k)) =
      (HonestInputs.first trap ps).getMem (W (CommitParents.addr d j+8*k))

structure Ready (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (records : List Wire.Field) : Prop extends Source s trap ps where
  location : s.pc = addr 1429
  cursor : s.getReg .x7 = W (Wire.bits records)
  output : OpeningPut.Serialized (memoryView s) (Wire.pack records)
  occupancy : HonestFlagState.Initial (flags ps) s

end CommitGolfCandidate.Reconstruction.CapEntry
