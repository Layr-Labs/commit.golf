import CommitGolfCandidate.ReconstructedHonestBlocks

namespace CommitGolfCandidate.Reconstruction.HonestCuts
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFlow HonestRegisters

/-- A path of genuine one-step interpreter executions, stopped at its first
encounter with a designated cutpoint. Only an unfinished single step continues. -/
inductive Reaches (im : Image) (coins : Bool) (cut : Word → Bool) : MachineState → MachineState → Prop
  | hit {s : MachineState} {r : Execution} (run : r ∈ support (execute im 1 s coins))
      (cont : r.exit = .unfinished) (done : cut r.state.pc = true) : Reaches im coins cut s r.state
  | more {s t : MachineState} {r : Execution} (run : r ∈ support (execute im 1 s coins))
      (cont : r.exit = .unfinished) (inside : cut r.state.pc = false)
      (tail : Reaches im coins cut r.state t) : Reaches im coins cut s t

/-- An observed cutpoint path always ends inside the selected set. -/
theorem endpoint {im : Image} {coins : Bool} {cut : Word → Bool} {s t : MachineState}
    (walk : Reaches im coins cut s t) : cut t.pc = true := by
  induction walk with
  | hit _ _ h => exact h
  | more _ _ _ _ ih => exact ih

/-- The bound at a boundary is required only for the actual machine states
reachable from the input state. Independent register and memory facts about
the same reachable end state can therefore be used together. -/
theorem bounded {im : Image} {active cut zero : Word → Bool} {rank : Word → Nat}
    (cert : Ranking im active cut zero rank) (s : MachineState) (coins : Bool) (tail : Nat)
    (entry : active s.pc = true) (safe : zero s.pc = true → s.getReg .x5 = 0)
    (boundary : ∀ t, Reaches im coins cut s t → ∀ f r, r ∈ support (execute im f t coins) → r.cycles ≤ tail)
    (fuel : Nat) (r : Execution) (run : r ∈ support (execute im fuel s coins)) : r.cycles ≤ rank s.pc + tail := by
  induction fuel generalizing s r with
  | zero => simp only [execute,support_pure,Set.mem_singleton_iff] at run; subst r; exact Nat.zero_le _
  | succ f ih =>
    obtain ⟨op,rd,dir,mode,fee,edges⟩ := cert.step s entry
    rw [show f+1=1+f by omega,execute_add,mem_support_bind_iff] at run
    obtain ⟨mid,first,rest⟩ := run
    obtain ⟨paid,progress⟩ := charged_successors im s op coins rd dir (safe ∘ mode) mid first
    by_cases cont : mid.exit = .unfinished
    · simp only [resume,cont,ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at rest
      obtain ⟨out,remain,rfl⟩ := rest
      obtain ⟨target,clear⟩ := progress cont
      cases stop : cut mid.state.pc with
      | true =>
        have b := boundary _ (.hit first cont stop) f out remain
        change mid.cycles+out.cycles ≤ _
        omega
      | false =>
        have edge := edges _ target
        simp only [stop,Bool.false_eq_true,false_or] at edge
        have b := ih mid.state edge.1 (clear ∘ edge.2.2)
          (fun t w => boundary t (.more first cont stop w)) out remain
        change mid.cycles+out.cycles ≤ _
        omega
    · simp only [resume,cont,ite_false,support_pure,Set.mem_singleton_iff] at rest
      subst r; omega

private theorem split_walk {im : Image} {coins : Bool} {cut : Word → Bool} {s t : MachineState}
    (walk : Reaches im coins cut s t) : ∃ out, out ∈ support (execute im 1 s coins) ∧
      out.exit = .unfinished ∧ ((cut out.state.pc = true ∧ t = out.state) ∨
      (cut out.state.pc = false ∧ Reaches im coins cut out.state t)) := by
  cases walk with
  | hit first cont done => exact ⟨_,first,cont,Or.inl ⟨done,rfl⟩⟩
  | more first cont inside tail => exact ⟨_,first,cont,Or.inr ⟨inside,tail⟩⟩

/-- The Boolean block checker certifies register facts on each genuine
reachable end state. It can be run on several independent register projections
and all their conclusions apply to that same state. -/
theorem postcondition {n : Nat} (packed : ArtifactEncoding.Packed n) (im : Image)
    (code : im.code = ArtifactEncoding.decode 32 packed) (small : 4096+4*n < 2^64)
    (cut : Word → Bool) (post : Word → Known → Bool) (keep : Word → Reg → Bool)
    (clock : Nat) (pc : Word) (m : Known) (budget : Nat)
    (cert : HonestBlocks.check packed cut post keep clock pc m budget = true)
    (coins : Bool) (s t : MachineState) (atPC : s.pc = pc) (agree : Agrees s m)
    (walk : Reaches im coins cut s t) : ∃ facts, post t.pc facts = true ∧ Agrees t facts := by
  induction clock generalizing pc m budget s with
  | zero => cases cert
  | succ h ih =>
    cases read : HonestBlocks.readOp packed pc with
    | none => simp [HonestBlocks.check,read] at cert
    | some op =>
      simp only [HonestBlocks.check,read,Bool.and_eq_true,decide_eq_true_eq] at cert
      obtain ⟨⟨⟨plain,dir⟩,_⟩,edges⟩ := cert
      have noCall : op ≠ .base .ECALL := by rintro rfl; cases plain
      obtain ⟨mid,first,cont,advance⟩ := split_walk walk
      have fetch := HonestBlocks.fetch_op packed im code small s op (atPC ▸ read)
      have ⟨target,held⟩ := (HonestAbstract.one im s op m coins fetch noCall dir agree mid first).2 cont
      rw [atPC] at target
      have edge := List.all_eq_true.mp edges mid.state.pc target
      let facts := HonestBlocks.prune (keep mid.state.pc) (update m op)
      have consistent : Agrees mid.state facts := HonestBlocks.pruned _ _ held _
      rcases advance with ⟨done,rfl⟩ | ⟨inside,tail⟩
      · exact ⟨facts,by simpa only [done,ite_true] using edge,consistent⟩
      · have more : HonestBlocks.check packed cut post keep h mid.state.pc facts (budget-price op) = true := by
          simpa only [inside,Bool.false_eq_true,ite_false] using edge
        exact ih _ _ _ more mid.state rfl consistent tail

end CommitGolfCandidate.Reconstruction.HonestCuts
