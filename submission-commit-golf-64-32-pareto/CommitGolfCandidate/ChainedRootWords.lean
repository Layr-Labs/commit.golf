import CommitGolfCandidate.ChainedHeapModel

/-! Projected word stores and frames for the four delivered root-copy pairs. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384

def rootWord (s : MachineState) (index : Nat) : MachineState :=
  execInstrBr (execInstrBr s (.LD .x31 .x9 (BitVec.ofNat 12 (32+8*index))))
    (.SD .x8 .x31 (BitVec.ofNat 12 (8*index)))

theorem root_word_memory (s : MachineState) (index : Nat) (small : index < 4) (query : Word) :
    (rootWord s index).getMem query =
      if query == s.getReg .x8+BitVec.ofNat 64 (8*index)
      then s.getMem (s.getReg .x9+BitVec.ofNat 64 (32+8*index)) else s.getMem query := by
  interval_cases index <;> rfl

theorem root_pair_memory (s : MachineState) (count : Nat) (small : count < 4) (query : Word) :
    (chainedRootPrefix s (2*(count+1))).getMem query =
      (rootWord (chainedRootPrefix s (2*count)) count).getMem query := by
  interval_cases count <;> rfl

theorem root_bases (s : MachineState) (pairs : Nat) (small : pairs ≤ 4) :
    (chainedRootPrefix s (2*pairs)).getReg .x8 = s.getReg .x8 ∧
      (chainedRootPrefix s (2*pairs)).getReg .x9 = s.getReg .x9 := by
  interval_cases pairs <;> exact ⟨rfl,rfl⟩

theorem root_tail_memory (s : MachineState) (query : Word) :
    (chainedRootPrefix s 10).getMem query = (chainedRootPrefix s 8).getMem query := by rfl

theorem root_memory_outside (s : MachineState) (query : Word)
    (avoid : ∀ j : Fin 4, query ≠ s.getReg .x8+BitVec.ofNat 64 (8*j.val))
    (pairs : Nat) (small : pairs ≤ 4) :
    (chainedRootPrefix s (2*pairs)).getMem query = s.getMem query := by
  induction pairs with
  | zero => rfl
  | succ pairs ih =>
    rw [root_pair_memory s pairs (by omega),root_word_memory _ pairs (by omega),
      (root_bases s pairs (by omega)).1,(root_bases s pairs (by omega)).2]
    rw [show (query == s.getReg .x8+BitVec.ofNat 64 (8*pairs)) = false from
      beq_eq_false_iff_ne.mpr (avoid ⟨pairs,by omega⟩)]
    exact ih (by omega)

theorem root_offset_eq (a b : Fin 4) :
    BitVec.ofNat 64 (8*a.val) = BitVec.ofNat 64 (8*b.val) ↔ a.val = b.val := by
  constructor
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    have ha := a.isLt
    have hb := b.isLt
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 8*a.val < 2^64 by omega),
      Nat.mod_eq_of_lt (show 8*b.val < 2^64 by omega)] at numeric
    omega
  · intro equal
    rw [equal]

theorem root_target_word (s : MachineState) (i : Fin 4) (pairs : Nat) (small : pairs ≤ 4)
    (separate : ∀ a b : Fin 4, s.getReg .x9+BitVec.ofNat 64 (32+8*a.val) ≠
      s.getReg .x8+BitVec.ofNat 64 (8*b.val)) :
    (chainedRootPrefix s (2*pairs)).getMem (s.getReg .x8+BitVec.ofNat 64 (8*i.val)) =
      if i.val < pairs then s.getMem (s.getReg .x9+BitVec.ofNat 64 (32+8*i.val))
      else s.getMem (s.getReg .x8+BitVec.ofNat 64 (8*i.val)) := by
  induction pairs with
  | zero => simp [chainedRootPrefix]
  | succ pairs ih =>
    have before : pairs < 4 := by omega
    rw [root_pair_memory s pairs before,root_word_memory _ pairs before,
      (root_bases s pairs (by omega)).1,(root_bases s pairs (by omega)).2]
    simp only [beq_iff_eq]
    by_cases same : i.val = pairs
    · have hit : s.getReg .x8+BitVec.ofNat 64 (8*i.val) = s.getReg .x8+BitVec.ofNat 64 (8*pairs) := by rw [same]
      rw [ite_eq_left hit,root_memory_outside s _ (separate ⟨pairs,before⟩) pairs (by omega)]
      simp only [same,ite_eq_left (Nat.lt_succ_self pairs)]
    · have miss : s.getReg .x8+BitVec.ofNat 64 (8*i.val) ≠ s.getReg .x8+BitVec.ofNat 64 (8*pairs) := by
        intro equal
        exact same ((root_offset_eq i ⟨pairs,before⟩).mp ((BitVec.add_right_inj _).mp equal))
      rw [ite_eq_right miss,ih (by omega)]
      by_cases earlier : i.val < pairs
      · rw [ite_eq_left earlier,ite_eq_left (show i.val < pairs+1 by omega)]
      · rw [ite_eq_right earlier,ite_eq_right (show ¬i.val < pairs+1 by omega)]

end CommitGolfCandidate.Chained.Native
