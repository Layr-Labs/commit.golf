import CommitGolfCandidate.ReconstructedHonestCapEmit
import CommitGolfCandidate.ReconstructedHonestCapGroups

namespace CommitGolfCandidate.Reconstruction.HonestCapExecution
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestCapPrices
open CommitBlocks (addr)

theorem advance (v : Node) (live : v.phase ≠ .returned) : HonestCapScan.Step v.depth v.phase := by
  obtain ⟨d,p⟩ := v
  cases p with
  | enter => exact HonestCapScan.enter _
  | level => exact HonestCapScan.level_start _
  | scan j n => exact HonestCapScan.scan d j n
  | scanGuard j n => exact HonestCapScan.scan_guard d j n
  | collected n => exact HonestCapEmit.collected d n
  | emit n j => exact HonestCapEmit.emit d n j
  | emitGuard n j => exact HonestCapEmit.emit_guard d n j
  | lowDone n => exact HonestCapEmit.low_done d n
  | group n j => exact HonestCapGroups.group d n j
  | inner n j r => exact HonestCapGroups.inner d n j r
  | digitGuard n j r => exact HonestCapGroups.digit_guard d n j r
  | flush n j => exact HonestCapGroups.flush d n j
  | groupGuard n j => exact HonestCapGroups.group_guard d n j
  | finish => exact HonestCapGroups.finish d
  | returned => exact False.elim (live rfl)

private theorem successor (v : Node) (live : v.phase ≠ .returned) : ∃ w, w ∈ next v.depth v.phase := by
  obtain ⟨d,p⟩ := v
  cases p <;> first | contradiction | exact ⟨_,List.mem_cons_self⟩

/-- For every fuel and every execution supported by the reference interpreter,
the cap consumes its phase potential before the epilogue. No restrictions on
the cap flags, digest memory, or oracle are required. -/
theorem budget_with (extra : Node → MachineState → Prop) (v : Node) (ok : legal v) (s : MachineState) (known : Matches v s)
    (start : extra v s) (coins : Bool) (tail : Nat)
    (preserve : ∀ (v w : Node) (s t : MachineState), legal v → v.phase≠.returned →
      Matches v s → extra v s → Path coins s t → w ∈ next v.depth v.phase → Matches w t → extra w t)
    (exitBound : ∀ (v : Node) (t : MachineState), v.phase=.returned → extra v t → t.pc=addr 1641 → Budget t coins tail) :
    Budget s coins (potential v + tail) := by
  suffices all : ∀ m (v : Node), potential v = m → legal v →
      ∀ s : MachineState, Matches v s → extra v s → Budget s coins (m+tail) from all _ v rfl ok s known start
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro v size ok s known ext
    by_cases ended : v.phase=.returned
    · have price : potential v=0 := by simp [potential,ended]
      have pcEnd : s.pc=addr 1641 := by simpa only [ended,pc] using known.atPc
      rw [← size,price,Nat.zero_add]
      exact exitBound v s ended ext pcEnd
    · obtain ⟨w,edge⟩ := successor v ended
      have feeLe : fee v.phase ≤ m := by have := (decreases _ _ ok edge).2.1; omega
      have bound := segment (pc v.phase) (fee v.phase) (registered _ ended) s coins known.atPc
          (m-fee v.phase+tail) (by
        intro t path
        obtain ⟨w',edge',matched⟩ := advance v ended _ _ _ ok known path
        obtain ⟨ok',cost,less⟩ := decreases v w' ok edge'
        exact mono (by omega) (ih (potential w') (by omega) w' rfl ok' t matched (preserve v w' s t ok ended known ext path edge' matched)))
      exact mono (by omega) bound

theorem budget (v : Node) (ok : legal v) (s : MachineState) (known : Matches v s)
    (coins : Bool) (tail : Nat) (exitBound : ∀ t : MachineState, t.pc=addr 1641 → Budget t coins tail) :
    Budget s coins (potential v + tail) := by
  exact budget_with (fun _ _ => True) v ok s known trivial coins tail (by intros; trivial)
    (fun _ t _ _ pcEnd => exitBound t pcEnd)

/-- At the actual cap entry only the compiler's frame pointer is required.
The complete unsigned pair, sibling, and mixed-radix loops cost at most 54,847 cycles. -/
theorem opening_cap (s : MachineState) (coins : Bool) (pc0 : s.pc=addr 1429)
    (stack : s.getReg .x8 = HonestCapTables.sp) (tail : Nat)
    (exitBound : ∀ t : MachineState, t.pc=addr 1641 → Budget t coins tail) :
    Budget s coins (54847+tail) := by
  have ok : legal ⟨9,.enter⟩ := by simp [legal,allowed]
  have result := budget ⟨9,.enter⟩ ok s ⟨pc0,stack,HonestCapStages.holds_nil _⟩ coins tail exitBound
  rwa [entry_cost] at result

end CommitGolfCandidate.Reconstruction.HonestCapExecution
