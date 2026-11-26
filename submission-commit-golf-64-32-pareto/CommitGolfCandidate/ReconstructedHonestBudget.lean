import CommitGolfCandidate.ReconstructedHonestCapPrices
import CommitGolfCandidate.ReconstructedReturn

namespace CommitGolfCandidate.Reconstruction.HonestBudget
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- A supported partial run always extends to a supported longer run of at
least its current charge, for arbitrary public replies and private coins. -/
theorem extend (im : Image) (s : MachineState) (coins : Bool) (f extra : Nat) (r : Execution)
    (run : r ∈ support (execute im f s coins)) :
    ∃ out ∈ support (execute im (f+extra) s coins), r.cycles≤out.cycles := by
  rw [execute_add]
  by_cases progress : r.exit=.unfinished
  · obtain ⟨tail,rest⟩ := support_nonempty (execute im extra r.state coins)
    refine ⟨tail.charge r.cycles r.oracleCalls,?_,?_⟩
    · rw [mem_support_bind_iff]
      refine ⟨r,run,?_⟩
      simp only [resume,progress,ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff]
      exact ⟨tail,rest,rfl⟩
    · change r.cycles≤r.cycles+tail.cycles; omega
  · refine ⟨r,?_,le_rfl⟩
    rw [mem_support_bind_iff]
    refine ⟨r,run,?_⟩
    simp only [resume,ite_eq_right progress,support_pure,Set.mem_singleton_iff]

theorem epilogue (s : MachineState) (pc : s.pc=10660) (stack : s.getReg .x2=68719474016)
    (returnPC : s.getMem 68719476328=4176) (cursor : (s.getReg .x7).toNat≤600000) :
    HonestCapPrices.Budget s true 23 := by
  intro f r run
  obtain ⟨out,finish,le⟩ := extend _ _ _ f 23 r run
  obtain ⟨t,exact,_⟩ := Return.execute_return s pc stack returnPC cursor f
  rw [Nat.add_comm f 23,exact,support_pure,Set.mem_singleton_iff] at finish
  subst out
  exact le

end CommitGolfCandidate.Reconstruction.HonestBudget
