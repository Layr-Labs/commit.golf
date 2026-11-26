import CommitGolfCandidate.ChainedContinuationHeader

/-! Compose word-store frames without expanding nested machine-state records. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem word_store_frame (s : MachineState) (src value : Reg) (offset : BitVec 12) (query : Word)
    (outside : query ≠ s.getReg src+signExtend12 offset) :
    (execInstrBr s (.SD src value offset)).getMem query = s.getMem query := by
  change (if query == s.getReg src+signExtend12 offset then _ else _) = _
  simp only [beq_iff_eq,ite_eq_right outside]
  rfl

private theorem header_step_frame (s : MachineState) (i : Fin 8) (query : Word)
    (outside : ∀ j : Fin 4, query ≠ s.getReg .x10+BitVec.ofNat 64 (32+8*j.val)) :
    (execInstrBr s (continuationOp (1+i.val))).getMem query = s.getMem query := by
  fin_cases i <;> dsimp only [continuationOp,continuationOps]
  all_goals first | rfl | apply word_store_frame
  all_goals first | exact outside ⟨0,by decide⟩ | exact outside ⟨1,by decide⟩ |
    exact outside ⟨2,by decide⟩ | exact outside ⟨3,by decide⟩

theorem header_prefix_source (s : MachineState) (count : Nat) (bound : count ≤ 8) :
    (ordinaryPrefix s 1 count).getReg .x10 = s.getReg .x10 := by
  interval_cases count <;> rfl

private theorem header_prefix_succ (s : MachineState) (count : Nat) (bound : count < 8) :
    ordinaryPrefix s 1 (count+1) =
      execInstrBr (ordinaryPrefix s 1 count) (continuationOp (1+count)) := by
  interval_cases count <;> rfl

theorem header_prefix_memory_outside (s : MachineState) (query : Word)
    (outside : ∀ j : Fin 4, query ≠ s.getReg .x10+BitVec.ofNat 64 (32+8*j.val))
    (count : Nat) (bound : count ≤ 8) :
    (ordinaryPrefix s 1 count).getMem query = s.getMem query := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [header_prefix_succ s count (by omega)]
    rw [header_step_frame _ ⟨count,by omega⟩ query]
    · exact ih (by omega)
    · intro j
      rw [header_prefix_source s count (by omega)]
      exact outside j

private theorem offsets_distinct : ∀ i : Fin 4, ∀ j : Fin 4,
    BitVec.ofNat 64 (8*i.val) ≠ BitVec.ofNat 64 (32+8*j.val) := by
  decide +kernel

theorem header_low_word (s : MachineState) (i : Fin 4) :
    (ordinaryPrefix s 1 8).getMem (s.getReg .x10+BitVec.ofNat 64 (8*i.val)) =
      s.getMem (s.getReg .x10+BitVec.ofNat 64 (8*i.val)) := by
  apply header_prefix_memory_outside s _ _ 8 (by decide)
  intro j same
  exact offsets_distinct i j ((BitVec.add_right_inj _).mp same)

end CommitGolfCandidate.Chained.Native
