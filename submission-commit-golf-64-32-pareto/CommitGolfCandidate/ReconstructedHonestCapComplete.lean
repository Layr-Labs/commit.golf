import CommitGolfCandidate.ReconstructedHonestCapInvariant
import CommitGolfCandidate.ReconstructedHonestRecordShapes

namespace CommitGolfCandidate.Reconstruction.HonestCapComplete
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestCapInvariant
open HonestCapPrices (Budget)
open HonestRanges HonestProtected
open HonestRecordMemory (context)
open CommitBlocks (addr)

private theorem exact_const {v : Word} {n : Nat} (value : Contains (HonestRecordMemory.constant n) v) :
    v=BitVec.ofNat 64 n := BitVec.eq_of_toNat_eq (Nat.le_antisymm value.2 value.1)

/-- All saved registers and the return PC are read from the very stack used by
the record loop. The nine-level cap and its complete epilogue cost at most 54,870 cycles. -/
theorem run (s : MachineState) (pc0 : s.pc=addr 1429)
    (ready : Holds context (HonestRecordShapes.capStart 128) s) : Budget s true 54870 := by
  let start : Node := ⟨9,.enter⟩
  have ok : legal start := by simp [start,legal,allowed]
  have reg := ready.1
  have size := exact_const (reg .x7 (HonestRecordMemory.constant (3633*128)) (by decide))
  have stack := exact_const (reg .x2 _ List.mem_cons_self)
  have frame := exact_const (reg .x8 _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have know : Matches start s := ⟨pc0,frame,HonestCapStages.holds_nil _⟩
  have extra : Extra start s := ⟨stack,ready.2.2,(by rw [size]; exact HonestCapGrowth.opening_max),
     (by intro h; exact False.elim (h rfl)),trivial⟩
  have bound := HonestCapExecution.budget_with Extra start ok s know extra true 23
    (fun v w s t legalV live known ext path edge matched => maintained v w s t legalV live known ext path edge matched)
    (fun v t _ ext pcEnd => by
      have saved := ext.frozen 68719476328 (by decide +kernel)
      change Contains (HonestRecordMemory.constant 4176) (t.getMem 68719476328) at saved
      exact HonestBudget.epilogue t pcEnd ext.stack (exact_const saved) ((Nat.le_add_right _ _).trans ext.cursor))
  exact bound

end CommitGolfCandidate.Reconstruction.HonestCapComplete
