import CommitGolfCandidate.PhaseTail
import CommitGolfCandidate.GroupOpenRecords
namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate GroupedOpening
open Opening (sortedIndex RecordMarks)
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] execute

theorem Rel.follow {a b c : MachineState} (x : Rel a b) (y : Rel b c) : Rel a c :=
  ⟨x.mem.trans y.mem,fun r h => (x.reg r h).trans (y.reg r h)⟩

theorem Rel.rightPC {a b : MachineState} (x : Rel a b) (v : Word) : Rel a (b.setPC v) :=
  ⟨x.mem,fun r h => x.reg r h⟩

def phaseOf (o : Nat) : Fin 4 := ⟨o%4,Nat.mod_lt _ (by decide)⟩
def recordRow (size o : Nat) := if o=size then 649 else phasePC (phaseOf o)
def rowAddress (n : Nat) := addr (4096+4*n)

theorem next_row (size o : Nat) : nextRow (phaseOf o) (decide (o+1=size))=recordRow size (o+1) := by
  have eq : nextPhase (phaseOf o)=phaseOf (o+1) := by
    apply Fin.ext;change (o%4+1)%4=(o+1)%4;omega
  simp [recordRow,nextRow,eq]

theorem remaining_zero (pos : Positions) (o : Nat) (present : o<pos.card) :
    BitVec.ofNat 64 (pos.card-(o+1))=0#64 ↔ o+1=pos.card := by
  have total : pos.card≤LENGTH := by simpa [Index] using Finset.card_le_univ pos
  have bound : LENGTH<2^64 := by decide
  constructor
  · intro z
    have eq:=Opening.nat_address_injective (by omega : pos.card-(o+1)<2^64) (by decide : 0<2^64) z
    omega
  · intro z;rw [z,Nat.sub_self]

theorem single_run (pi : Image) (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (pos : Positions) (old actual : MachineState) (o : Nat) (present : o<pos.card)
    (boundary : RecordBoundary s td pos old o) (rel : Rel old actual)
    (pc : actual.pc=rowAddress (recordRow pos.card o)) :
    ∃ after : MachineState,
      PricedRun (stitched pi) actual after (phaseCost (phaseOf o)) 3 ∧
      Rel (runRecord old (decide (o+1=pos.card))) after ∧
      after.pc=rowAddress (recordRow pos.card (o+1)) := by
  let p:=phaseOf o
  let i:=sortedIndex pos o present
  let fin:=decide (o+1=pos.card)
  have start:=prefix_ready s layout td pos old o present (boundary.start present)
  have total : pos.card≤LENGTH := by simpa [Index] using Finset.card_le_univ pos
  have entry : actual.pc=rowAddress (phasePC p) := by simpa only [recordRow,if_neg (Nat.ne_of_lt present)] using pc
  let raw:=physicalFields p i o actual 18
  obtain ⟨run,similar,lastAt⟩:=fields_run pi p i o old actual (by omega) rfl start entry rel 18 (by decide)
  have r : Rel (afterCopy old 17) raw := similar
  have atTail : raw.pc=addr (4096+4*lastPC p) := lastAt
  obtain ⟨lo,hi⟩:=tail_rows_range p
  have hsafe:=safe_mark s layout td pos old o present boundary
  have ready:=ready_last (afterCopy old 17) (by rw [original_data];exact hsafe)
  obtain ⟨ending,post,lpc⟩:=lifted_run pi p lastOps (lastPC p) (last_decoded p) (by omega) hi
    (afterCopy old 17) raw atTail r ready last_member
  have same: Rel (runRecord old fin) (straight raw lastOps) := (tail_reference old fin).follow post
  have oldNext:=(execute_record s layout td pos old o present boundary).next
  have flag : ((straight raw lastOps).getReg .x18=0#64) ↔ fin=true := by
    rw [←same.reg .x18 (by decide),oldNext.left,remaining_zero pos o present]
    exact (decide_eq_true_iff).symm
  have tail:=latch_run pi p fin (straight raw lastOps) lpc flag
  refine ⟨finishRecord p fin (straight raw lastOps),?_,same.rightPC _,?_⟩
  · rw [←complete_cost p];exact (run.next ending).next tail.priced
  · change rowAddress (nextRow p fin)=_
    rw [next_row]

theorem cost_monotone : Monotone PhaseOpening.recordCost := by
  apply monotone_nat_of_le_succ
  intro n
  rw [recordCost_step n (phaseOf n) rfl]
  omega

theorem records_run (pi : Image) (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (pos : Positions) (o count : Nat) (old actual : MachineState) (bound : o+count≤pos.card)
    (boundary : RecordBoundary s td pos old o) (rel : Rel old actual)
    (pc : actual.pc=rowAddress (recordRow pos.card o)) :
    ∃ after : MachineState,
      PricedRun (stitched pi) actual after (PhaseOpening.recordCost (o+count)-PhaseOpening.recordCost o) (3*count) ∧
      Rel (runRecords pos.card o count old) after ∧
      after.pc=rowAddress (recordRow pos.card (o+count)) := by
  induction count generalizing o old actual with
  | zero =>
    refine ⟨actual,?_,rel,pc⟩
    intro fuel coins;simp [Execution.charge]
  | succ k ih =>
    have present : o<pos.card := by omega
    let oldNext:=runRecord old (decide (o+1=pos.card))
    have nextContext:=(execute_record s layout td pos old o present boundary).next
    obtain ⟨next,first,close,newPC⟩:=single_run pi s layout td pos old actual o present boundary rel pc
    obtain ⟨last,rest,same,lastPC⟩:=ih (o+1) oldNext next (by omega) nextContext close newPC
    have add : o+(k+1)=(o+1)+k := by omega
    have step:=recordCost_step o (phaseOf o) rfl
    have mono:=cost_monotone (show o+1≤(o+1)+k by omega)
    refine ⟨last,?_,same,?_⟩
    · rw [add,show PhaseOpening.recordCost (o+1+k)-PhaseOpening.recordCost o =
        phaseCost (phaseOf o)+(PhaseOpening.recordCost (o+1+k)-PhaseOpening.recordCost (o+1)) by omega]
      simpa only [Nat.mul_succ,Nat.add_comm 3] using first.next rest
    · rwa [add]

#print axioms single_run
#print axioms records_run
end TwoPermutationPrototype.PhaseOpening
