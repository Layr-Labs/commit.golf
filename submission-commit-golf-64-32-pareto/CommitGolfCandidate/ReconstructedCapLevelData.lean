import CommitGolfCandidate.ReconstructedCapEvidence
import CommitGolfCandidate.ReconstructedCapHeaderFlush

namespace CommitGolfCandidate.Reconstruction.CapLevelData
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OpeningPut OpeningCursor
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
open HonestCapTables (addrSlot w)
set_option maxRecDepth 18000

structure Packed (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) (f : Nat→Bool) (d : Nat)
    (xs : List Nat) (fs : List Wire.Field) : Prop where
  common : CapGlobal.Common s trap ps
  rows : HonestSizeRows.Rows f d (HonestCapPlan.pairs d) s
  slots : CapSlots.Contains (memoryView s) xs
  buffer : CapEvidence.Buffer s fs
  depth : s.getReg .x10=W d
  one : s.getReg .x11=1

def kept : List Reg := [.x5,.x9,.x13,.x17,.x18,.x19,.x28,.x31,.x2,.x8,.x10,.x11]

theorem change (s t : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) (f : Nat→Bool) (d : Nat)
    (xs : List Nat) (fs gs : List Wire.Field) (old : Packed s trap ps f d xs fs)
    (depthBound : HonestCapPlan.pairs d≤256) (size : xs.length≤512) (out : CapEvidence.Buffer t gs)
    (regs : ∀ r∈kept, t.getReg r=s.getReg r)
    (mem : ∀ q, q<2^33 → CapEmitNode.outside q → memoryView t q=memoryView s q) : Packed t trap ps f d xs gs := by
  have named : HonestCapStages.holds t CapGlobal.fixed := by
    intro r v known
    have within : r∈kept := by
      simp only [CapGlobal.fixed,List.mem_cons,List.not_mem_nil,or_false] at known
      rcases known with h|h|h|h|h|h|h|h <;> cases h <;> decide
    exact (regs _ within).trans (old.common.regs _ _ known)
  refine ⟨⟨CapFrame.transfer s t trap ps old.common.source (regs _ (by decide)) (regs _ (by decide)) (fun q h _ z => mem q h z),
    named⟩,CapEvidence.rows_of_outside _ _ _ _ _ depthBound old.rows mem,CapEvidence.slots_of_outside _ _ _ size old.slots mem,
    out,(regs _ (by decide)).trans old.depth,(regs _ (by decide)).trans old.one⟩

theorem jump (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) (f : Nat→Bool) (d : Nat)
    (xs : List Nat) (fs : List Wire.Field) (old : Packed s trap ps f d xs fs) (p : Word)
    (small : HonestCapPlan.pairs d≤256) (size : xs.length≤512) : Packed (s.setPC p) trap ps f d xs fs :=
  change s _ trap ps f d xs fs fs old small size ⟨old.buffer.cursor,old.buffer.output⟩ (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem emit_guard (o : Oracle) (s : MachineState) (pc : s.pc=addr 1511) (k n : Nat) (kl : k≤256) (nl : n≤256)
    (left : s.getReg .x24=addrSlot k) (right : s.getReg .x25=addrSlot n) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (if k=n then addr 1581 else addr 1512)) := by
  apply CommitExact.plain o _ _ _ (.base (.BEQ .x24 .x25 280)) (OpeningStraight.fetched 1511 _ (by decide) rfl s pc)
  change some (if s.getReg .x24==s.getReg .x25 then s.setPC (s.pc+signExtend13 280) else s.setPC (s.pc+4))=_
  rw [pc,left,right]
  have eq := HonestCapState.slots (n:=n) (j:=k) nl kl
  by_cases same : k=n
  · rw [ite_eq_left same,beq_iff_eq.mpr (eq.mpr same)];rfl
  · rw [ite_eq_right same,beq_eq_false_iff_ne.mpr (fun h => same (eq.mp h))];rfl

end CommitGolfCandidate.Reconstruction.CapLevelData
