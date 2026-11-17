import CommitGolfCandidate.CapCheckRootLoop

/-! The completed comparison accepts exactly when all requested original words
agree. Every earlier comparison preserves the operands used by later ones.
This statement is independent of the values in the reconstructed/stored roots. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem word_memory (left right : MachineState) (same : left.mem = right.mem)
    (address : Word) : left.getMem address = right.getMem address :=
  congrFun same address

theorem cap_check_root_equal_frame (state : MachineState) (word other : Nat) :
    CapCheckRootEqual (capCheckRootPrefix state word 3) other ↔
      CapCheckRootEqual state other := by
  unfold CapCheckRootEqual
  rw [cap_check_root_register state word .x18 (by decide) (by decide),
    cap_check_root_register state word .x26 (by decide) (by decide),
    word_memory _ _ (cap_check_root_memory state word),
    word_memory _ _ (cap_check_root_memory state word)]

theorem cap_check_root_loop_register (state : MachineState) (word count : Nat)
    (reg : Reg) (outside6 : reg ≠ .x6) (outside7 : reg ≠ .x7) :
    (capCheckRootLoop state word count).1.getReg reg = state.getReg reg := by
  induction count generalizing state word with
  | zero => rfl
  | succ count ih =>
    unfold capCheckRootLoop
    split
    · exact (ih _ _).trans (cap_check_root_register state word reg outside6 outside7)
    · exact cap_check_root_register state word reg outside6 outside7

theorem cap_check_root_loop_passed (state : MachineState) (word count : Nat) :
    (capCheckRootLoop state word count).2 = true ↔
      ∀ i < count, CapCheckRootEqual state (word+i) := by
  induction count generalizing state word with
  | zero => simp [capCheckRootLoop]
  | succ count ih =>
    by_cases equal : CapCheckRootEqual state word
    · rw [capCheckRootLoop, if_pos equal, ih]
      constructor
      · intro tail i inside
        cases i with
        | zero => simpa using equal
        | succ i =>
          have value := (cap_check_root_equal_frame state word (word+1+i)).mp
            (tail i (by omega))
          simpa only [Nat.add_assoc, Nat.add_comm 1 i] using value
      · intro all i inside
        apply (cap_check_root_equal_frame state word (word+1+i)).mpr
        have value := all (i+1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using value
    · rw [capCheckRootLoop, if_neg equal]
      constructor
      · intro impossible
        contradiction
      · intro all
        exact (equal (by simpa using all 0 (by omega))).elim

end CommitGolfCandidate
