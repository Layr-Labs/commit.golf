import CommitGolfCandidate.ReconstructedHonestWideMemory
import CommitGolfCandidate.ReconstructedHonestCapComplete

namespace CommitGolfCandidate.Reconstruction.HonestWideCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapState HonestCapPlan HonestCapInvariant HonestCapPrices
open HonestRanges HonestProtected
open HonestRecordMemory (idx data sp constant)
open HonestWideMemory (capacity)
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

private theorem freeze {s : MachineState} (wide : HonestWideMemory.Frozen s) : HonestCapRam.Frozen s := by
  intro q has
  have included : protects HonestWideMemory.context q=true := by
    simp only [protects,HonestRecordMemory.context,HonestWideMemory.context,List.any_cons,List.any_nil,
      Bool.or_false,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at has ⊢
    rcases has with a|b|c|d
    · exact Or.inl a
    · exact Or.inr (Or.inl b)
    · exact Or.inr (Or.inr (Or.inl c))
    · exact Or.inr (Or.inr (Or.inr ⟨d.1,by dsimp [idx,capacity] at *; omega⟩))
  have actual := wide q included
  unfold HonestWideMemory.fixed at actual
  split at actual
  · rename_i valid
    change Contains (HonestRecordMemory.fixed q) (s.getMem q)
    simp only [HonestRecordMemory.fixed,valid.1,ne_eq,not_true_eq_false,ite_false]
    have lo := valid.2.1
    simp only [ite_eq_right (show q.toNat≠sp-8 by dsimp [sp,idx,capacity] at *; omega),
      ite_eq_right (show ¬(sp-2312≤q.toNat ∧ q.toNat≤sp-2224) by dsimp [sp,idx,capacity] at *; omega),
      ite_eq_right (show ¬(data≤q.toNat ∧ q.toNat<data+400) by dsimp [data,idx] at *; omega)]
    split <;> first | exact actual | exact arbitrary _
  · exact actual

private theorem scalar {v : Word} {n : Nat} (h : Contains (constant n) v) :
    v=BitVec.ofNat 64 n := BitVec.eq_of_toNat_eq (Nat.le_antisymm h.2 h.1)

theorem root_ready (s : MachineState) (entry : s.pc=addr 1429)
    (ready : Holds HonestWideMemory.context HonestWideMemory.finish s) :
    legal ⟨9,.enter⟩ ∧ Matches ⟨9,.enter⟩ s ∧ ExtraAt 70000000000 ⟨9,.enter⟩ s := by
  let root : Node := ⟨9,.enter⟩
  have stack := scalar (ready.1 .x2 (constant (sp-2320)) (by decide))
  have fp := scalar (ready.1 .x8 (constant sp) (by decide))
  have size : (s.getReg .x7).toNat≤3633*capacity := (ready.1 .x7 (⟨0,3633*capacity⟩ : Range) (by decide)).2
  have base : Matches root s := ⟨entry,fp,HonestCapStages.holds_nil _⟩
  have ok : legal root := by simp [root,legal,allowed]
  have good : ExtraAt 70000000000 root s := ⟨stack,freeze ready.2.2,(by
      have m : 3633*capacity+HonestCapGrowth.remaining root≤70000000000 := by decide
      omega),(by intro h; exact (h rfl).elim),trivial⟩
  exact ⟨ok,base,good⟩

theorem run (s : MachineState) (entry : s.pc=addr 1429) (ready : Holds HonestWideMemory.context HonestWideMemory.finish s) :
    Budget s true 54870 := by
  obtain ⟨ok,base,good⟩ := root_ready s entry ready
  apply HonestCapExecution.budget_with (ExtraAt 70000000000) ⟨9,.enter⟩ ok s base good true 23
    (fun v w s t valid live known ext path edge matched =>
      maintainedWide (Nat.le_refl _) v w s t valid live known ext path edge matched)
  intro v t ended ext loc fuel r hr
  have saved := ext.frozen 68719476328 (by decide +kernel)
  change Contains (constant 4176) (t.getMem 68719476328) at saved
  obtain ⟨out,extended,lower⟩ := HonestBudget.extend _ _ _ fuel 23 r hr
  obtain ⟨endState,exec,len⟩ := Return.execute_return_wide t loc ext.stack (scalar saved)
    ((Nat.le_add_right _ _).trans ext.cursor) fuel
  rw [Nat.add_comm fuel 23,exec,support_pure,Set.mem_singleton_iff] at extended
  subst out; exact lower

theorem calls (s : MachineState) (entry : s.pc=addr 1429) (ready : Holds HonestWideMemory.context HonestWideMemory.finish s) :
    HonestCallFlow.Calls image s true 0 := by
  have every (m : Nat) : ∀ v : Node, potential v=m → legal v → ∀ t : MachineState,
      Matches v t → ExtraAt 70000000000 v t → HonestCallFlow.Calls image t true 0 := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro v size ok t known ext
      by_cases ended : v.phase=.returned
      · have pcEnd : t.pc=addr 1641 := by simpa only [ended,pc] using known.atPc
        have saved := ext.frozen 68719476328 (by decide +kernel)
        change Contains (constant 4176) (t.getMem 68719476328) at saved
        intro fuel r hr
        obtain ⟨out,extended,lower⟩ := HonestCallFlow.extend _ _ _ fuel 23 r hr
        obtain ⟨endState,exec,_⟩ := Return.execute_return_wide t pcEnd ext.stack (scalar saved)
          ((Nat.le_add_right _ _).trans ext.cursor) fuel
        rw [Nat.add_comm fuel 23,exec,support_pure,Set.mem_singleton_iff] at extended
        subst out; exact lower
      · apply segment_calls (pc v.phase) (fee v.phase) (registered _ ended) t true known.atPc 0
        intro u path
        obtain ⟨w,edge,matched⟩ := HonestCapExecution.advance v ended _ _ _ ok known path
        obtain ⟨valid,_,less⟩ := decreases v w ok edge
        exact ih (potential w) (size ▸ less) w rfl valid u matched
          (maintainedWide (Nat.le_refl _) v w t u ok ended known ext path edge matched)
  obtain ⟨ok,base,ext⟩ := root_ready s entry ready
  exact every _ _ rfl ok s base ext

end CommitGolfCandidate.Reconstruction.HonestWideCap
