import CommitGolfCandidate.PhaseRecords

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate GroupedOpening
open Opening (RecordMarks)
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
attribute [local irreducible] execute runRecords

theorem transfer_final {s : Submission} {td : BitVec (8*s.sizes.trapdoor)} {pos : Positions} {old actual : MachineState}
    (rel : Rel old actual) (pc : actual.pc=0x1a24)
    (context : RecordBoundary s td pos old pos.card) :
    RecordBoundary s td pos actual pos.card := by
  have reg (k : Reg) (safe : k≠.x31 := by decide) := (rel.reg k safe).symm
  refine ⟨by simpa only [ite_true] using pc,(reg .x9).trans context.heap,(reg .x8).trans context.index,
    (reg .x22).trans context.nonce,(reg .x21).trans context.dest,(reg .x19).trans context.leaves,
    (reg .x24).trans context.slots,?_,(reg .x18).trans context.left,(reg .x26).trans context.marks,
    (reg .x23).trans context.one,(reg .x25).trans context.capHeap,(reg .x27).trans context.capLeaves,
    (reg .x20).trans context.proofBegin,(reg .x4).trans context.mult⟩
  simpa only [SameOpeningInput,MachineState.getMem,←rel.mem] using context.input

theorem complete_records (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor))
    (pos : Positions) (start : MachineState) (positive : 0<pos.card) (pc : start.pc=rowAddress 762)
    (boundary : RecordBoundary s td pos (start.setPC 0x103c) 0) (marks : RecordMarks pos start 0)
    (imageEq : openingImage=stitched openingImage) :
    ∃ lower : MachineState, RunsOpeningSlack start lower (PhaseOpening.recordCost pos.card+3*pos.card) (3*pos.card) ∧
      RecordBoundary s td pos lower pos.card ∧ RecordMarks pos lower pos.card ∧
      CompletedRecords s td pos lower pos.card := by
  let old:=start.setPC 0x103c
  have markOld:RecordMarks pos old 0:=marks
  have r:Rel old start:=⟨rfl,fun _ _=>rfl⟩
  have startPC : start.pc=rowAddress (recordRow pos.card 0) := by
    rw [recordRow,if_neg (Nat.ne_of_lt positive)]
    exact pc
  obtain ⟨lower,ran,close,cap⟩:=records_run openingImage s layout td pos 0 pos.card old start (by omega) boundary r startPC
  have complete:=execute_records_from_step execute_record s layout td pos old 0 pos.card
    (by omega) boundary markOld (fun j _ inside => (by omega : False).elim)
  have endPC : lower.pc=0x1a24 := by simpa [recordRow,rowAddress,addr] using cap
  have ctx : RecordBoundary s td pos (runRecords pos.card 0 pos.card old) pos.card := by simpa using complete.boundary
  have lowerMarks : RecordMarks pos (runRecords pos.card 0 pos.card old) pos.card := by simpa using complete.marks
  have written : CompletedRecords s td pos (runRecords pos.card 0 pos.card old) pos.card := by simpa using complete.bytes
  refine ⟨lower,?_,transfer_final close endPC ctx,?_,?_⟩
  · intro fuel coins
    simpa only [←imageEq,Nat.zero_add,show PhaseOpening.recordCost 0=0 by decide,Nat.sub_zero,Nat.add_assoc] using ran (3*pos.card+fuel) coins
  · simpa only [RecordMarks,Opening.machineMarks,MachineState.getMem,←close.mem] using lowerMarks
  · simpa only [CompletedRecords,MachineState.getByte,MachineState.getMem,←close.mem] using written

def fastCycles (pos : Positions) : Nat := if pos.card=0 then 7 else
  15+(PhaseOpening.recordCost pos.card+3*pos.card)+2551+(PackedOpening.capSubtreeCycles (Opening.groupsBefore pos pos.card) 1 8+3)+4

theorem budget (pos : Positions) (nz : 0<pos.card) :
    fastCycles pos+(634*pos.card-1) = QuartetOpening.scheduledCycles pos+PhaseOpening.recordCost pos.card+3*pos.card := by
  simp only [fastCycles,QuartetOpening.scheduledCycles,if_neg (Nat.ne_of_gt nz)];omega

theorem cost_cap (n : Nat) : PhaseOpening.recordCost n≤634*n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [recordCost_step n (phaseOf n) rfl]
    have lim := (show ∀ p : Fin 4, phaseCost p≤634 by decide) (phaseOf n)
    omega

theorem fast_scored (p : Positions) (h : p.card=BATCH) :
    fastCycles p≤74426 ∧ QuartetOpening.proofLength p≤72192 := by
  have k : p.card=128 := h
  have gold:=QuartetOpening.scored_limits p h
  have eq:=budget p (by omega)
  rw [k,recordCost_128] at eq
  exact ⟨by omega,gold.2⟩

#print axioms complete_records
#print axioms fast_scored
end TwoPermutationPrototype.PhaseOpening
