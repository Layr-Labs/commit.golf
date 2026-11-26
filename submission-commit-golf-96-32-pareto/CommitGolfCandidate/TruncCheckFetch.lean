import CommitGolfCandidate.TruncWireImage
import CommitGolfCandidate.LateNormalImage
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 12000
abbrev checkOld := Late.Check.Normal.checkerImage
def untouched (i : Nat) := i<433 ∧ i≠6 ∧ i≠15 ∧ i≠252 ∧ i≠256 ∧ i≠334 ∧ i≠364
instance (i : Nat) : Decidable (untouched i) := inferInstanceAs (Decidable (_ ∧ _))
private theorem equalWords : ∀ i : Fin 433, untouched i.val → (wireImage true).code[i.val]?=checkOld.code[i.val]? := by decide
theorem sharedFetch (s : MachineState) (i : Nat) (op : Instr) (hi : untouched i)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i)) (d : (checkOld.code[i]?).bind decodeInstruction=some (.base op)) :
    fetch (wireImage true) s=some (.base op) :=
  fetchAt _ s i op (by have :=hi.1;omega) pc (by rw [equalWords ⟨i,hi.1⟩ hi];exact d)
end CommitGolfCandidate.Trunc
