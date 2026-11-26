import CommitGolfCandidate.ReconstructedHonestSizeAdvance
import CommitGolfCandidate.ReconstructedHonestSizeExit

namespace CommitGolfCandidate.Reconstruction.HonestSizeCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestFinishes HonestCapPlan HonestCapState HonestCapInvariant
open HonestSizeSchedule HonestSizeRows HonestProtected HonestRanges HonestCapStages
open HonestRecordMemory (context)
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

structure Invariant (f : Nat→Bool) (v : Node) (s : MachineState) : Prop where
  infra : Extra v s
  operands : HonestSizeCursor.detail v.depth v.phase s
  rows : At f v s
  counts : rightCount f v.depth v.phase
  exactBits : (s.getReg .x7).toNat+future f v=3633*128+total f 9

theorem entire (f : Nat→Bool) (v : Node) (ok : legal v) (s : MachineState)
    (known : Matches v s) (inv : Invariant f v s) (few : population f 9≤128) :
    SuccessPost image true HonestSizeExit.Good s := by
  suffices h : ∀ n (v : Node), potential v=n → legal v → ∀ s, Matches v s → Invariant f v s →
      SuccessPost image true HonestSizeExit.Good s from h _ v rfl ok s known inv
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v size valid s known inv
    by_cases done_ : v.phase=.returned
    · exact HonestSizeExit.finish known inv.infra done_ inv.exactBits few
    · refine HonestCapPrices.segment_success (good:=HonestSizeExit.Good) _ _ (registered _ done_) s true known.atPc ?_
      intro t path
      obtain ⟨w',edge,matched⟩ := HonestCapExecution.advance v done_ _ _ _ valid known path
      obtain ⟨ok',_,lt⟩ := decreases _ _ valid edge
      obtain ⟨rows,counts⟩ := HonestSizeAdvance.maintained valid done_ known inv.infra inv.operands inv.rows inv.counts path edge matched
      refine ih (potential w') (by omega) w' rfl ok' t matched ?_
      refine ⟨maintained _ _ _ _ valid done_ known inv.infra path edge matched,
        HonestSizeCursor.maintained valid known inv.infra inv.operands done_ path edge matched,rows,counts,?_⟩
      have moved := HonestSizeCursor.paid known inv.infra inv.operands done_ path
      have price := advance f v w' valid inv.counts edge
      have start := inv.exactBits
      omega

private theorem constant_eq {v : Word} {n : Nat} (value : Contains (HonestRecordMemory.constant n) v) :
    v=BitVec.ofNat 64 n := BitVec.eq_of_toNat_eq (Nat.le_antisymm value.2 value.1)

theorem run (s : MachineState) (pc0 : s.pc=addr 1429) (ready : Holds context (HonestRecordShapes.capStart 128) s)
    (f : Nat→Bool) (marks : HonestFlagState.Initial f s) (few : population f 9≤128) :
    SuccessPost image true HonestSizeExit.Good s := by
  let start : Node := ⟨9,.enter⟩
  have ok : legal start := by simp [start,legal,allowed]
  have reg := ready.1
  have size := constant_eq (reg .x7 (HonestRecordMemory.constant (3633*128)) (by decide))
  have stack := constant_eq (reg .x2 _ List.mem_cons_self)
  have fp := constant_eq (reg .x8 _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have know : Matches start s := ⟨pc0,fp,holds_nil _⟩
  have ext : Extra start s := ⟨stack,ready.2.2,(by rw [size]; exact HonestCapGrowth.opening_max),
    (by intro h; exact False.elim (h rfl)),trivial⟩
  exact entire f start ok s know ⟨ext,trivial,HonestSizeRows.init marks,trivial,(by rw [size]; rfl)⟩ few

end CommitGolfCandidate.Reconstruction.HonestSizeCap
