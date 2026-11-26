import CommitGolfCandidate.ReconstructedHonestObserve
import CommitGolfCandidate.ReconstructedHonestWideCap

namespace CommitGolfCandidate.Reconstruction.HonestCapObserve
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestCapInvariant
open CommitBlocks (addr)
open HonestObserve (At)

attribute [local irreducible] ArtifactEncoding.decode execute
set_option maxRecDepth 16384

private theorem never_enter (v w : Node) (edge : w∈next v.depth v.phase) : w.phase≠.enter := by
  obtain ⟨d,p⟩ := v
  cases p <;> simp only [next,List.mem_cons,List.not_mem_nil,or_false] at edge
  all_goals try split at edge
  all_goals first | contradiction | (rcases edge with rfl|rfl <;> intro h <;> cases h) | (subst w;intro h;cases h)

private theorem notEntry (p : Phase) (notFirst : p≠.enter) : addr (pc p)≠addr 1429 := by
  cases p <;> first | contradiction | (simp only [pc];decide +kernel)

/-- The very first cap state is the only state at its entry PC. This covers
all supported prefixes, including stops partway through the return. -/
theorem only (s : MachineState) (entry : s.pc=addr 1429)
    (ready : HonestProtected.Holds HonestWideMemory.context HonestWideMemory.finish s) :
    At image s (addr 1429) (·=s) := by
  have all (m : Nat) : ∀ v : Node, potential v=m → legal v → ∀ u : MachineState,
      Matches v u → ExtraAt 70000000000 v u → (v.phase=.enter→u=s) → At image u (addr 1429) (·=s) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro v size valid u known ext first
      by_cases ended : v.phase=.returned
      · have pcEnd : u.pc=addr 1641 := by simpa only [ended,pc] using known.atPc
        have saved := ext.frozen 68719476328 (by decide +kernel)
        change HonestRanges.Contains (HonestRecordMemory.constant 4176) (u.getMem 68719476328) at saved
        have ret : u.getMem 68719476328=4176 := BitVec.eq_of_toNat_eq (Nat.le_antisymm saved.2 saved.1)
        intro f r run live hit
        exact False.elim (Return.no_cap_prefix u pcEnd ext.stack ret ((Nat.le_add_right _ _).trans ext.cursor) f r run live hit)
      · apply HonestObserve.cuts image u HonestCapStages.stops (addr 1429) (·=s) (by decide)
        · intro atEntry
          apply first; by_contra no
          exact notEntry v.phase no (known.atPc.symm.trans atEntry)
        · intro t path
          obtain ⟨w,edge,matched⟩ := HonestCapExecution.advance v ended _ _ _ valid known path
          obtain ⟨ok,_,less⟩ := decreases v w valid edge
          exact ih (potential w) (size ▸ less) w rfl ok t matched
            (maintainedWide (Nat.le_refl _) v w u t valid ended known ext path edge matched)
            (fun reenter => (never_enter v w edge reenter).elim)
  obtain ⟨legal,known,ext⟩ := HonestWideCap.root_ready s entry ready
  exact all _ _ rfl legal s known ext (fun _ => rfl)

end CommitGolfCandidate.Reconstruction.HonestCapObserve
