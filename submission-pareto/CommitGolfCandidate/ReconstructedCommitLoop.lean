import CommitGolfCandidate.ReconstructedCommitBlocks

namespace CommitGolfCandidate.Reconstruction.CommitLoop
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitControl CommitBlocks

/-- The taken last-iteration exit accounts for the one omitted back jump. -/
def work (perVisit : Nat) : Nat → Nat
  | 0 => 0
  | 1 => perVisit + 2
  | n+2 => perVisit + 3 + work perVisit (n+1)

theorem work_eq (price n : Nat) :
    work price (n+1) + 1 = (n+1)*(price+3) := by
  induction n with
  | zero => simp [work]
  | succ n ih => rw [work,Nat.succ_mul]; omega

private theorem pure_instr (im : Image) (i : Instruction) (pc : Word)
    {P Q : MachineState → Prop} (fetchOp : ∀ s, P s → s.pc = pc)
    (word : ∀ s : MachineState, s.pc = pc → fetch im s = some i)
    (next : ∀ s, P s → ∃ t, ordinaryStep s i = some t ∧ Q t) :
    Fragment im 1 (instructionCycles i) 0 P Q := by
  intro s hp r hr
  obtain ⟨t, ht, post⟩ := next s hp
  rw [execute_ordinary_step im i s t 0 true (word s (fetchOp s hp)) ht] at hr
  simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at hr
  subst r
  exact ⟨by simp [Execution.charge],by rfl,fun _ => post⟩

theorem decrement (im : Image) (pc : Word) (n : Nat)
    (word : ∀ s : MachineState, s.pc = pc →
      fetch im s = some (.base (.ADDI .x20 .x20 4095))) :
    Fragment im 1 1 0 (At pc (BitVec.ofNat 64 (n+1))) (At (pc+4) (BitVec.ofNat 64 n)) := by
  apply pure_instr im (.base (.ADDI .x20 .x20 4095)) pc (fun _ h => h.1) word
  intro s hs
  refine ⟨_, rfl, congrArg (· + 4) hs.1, ?_, ?_⟩
  · exact hs.2.1
  · change s.getReg .x20 + 0xffffffffffffffff#64 = BitVec.ofNat 64 n
    rw [hs.2.2,BitVec.ofNat_add]
    rw [BitVec.add_assoc, show BitVec.ofNat 64 1 + 0xffffffffffffffff#64 = 0 from rfl]
    exact BitVec.add_zero _

theorem branch_zero (im : Image) (pc counter : Word)
    (word : ∀ s : MachineState, s.pc = pc → fetch im s = some (.base (.BEQ .x20 .x0 8))) :
    Fragment im 1 1 0 (At pc counter) (At (if counter = 0 then pc+8 else pc+4) counter) := by
  apply pure_instr im (.base (.BEQ .x20 .x0 8)) pc (fun _ h => h.1) word
  intro s hs
  refine ⟨_,rfl,?_⟩
  have zero : s.getReg .x0 = 0 := rfl
  change At _ _ (if s.getReg .x20 == s.getReg .x0 then s.setPC (s.pc + signExtend13 8)
                  else s.setPC (s.pc+4))
  rw [hs.2.2,zero]
  by_cases z : counter = 0
  · subst counter
    simp only [beq_self_eq_true,ite_true]
    exact ⟨congrArg (·+8) hs.1,hs.2.1,hs.2.2⟩
  · have ne : (counter == 0) = false := beq_eq_false_iff_ne.mpr z
    rw [ne,ite_eq_right (by decide : false ≠ true),ite_eq_right z]
    exact ⟨congrArg (·+4) hs.1,hs.2.1,hs.2.2⟩

theorem jump_back (im : Image) (pc first counter : Word) (offset : BitVec 21)
    (word : ∀ s : MachineState, s.pc = pc → fetch im s = some (.base (.JAL .x0 offset)))
    (target : pc + signExtend21 offset = first) :
    Fragment im 1 1 0 (At pc counter) (At first counter) := by
  apply pure_instr im (.base (.JAL .x0 offset)) pc (fun _ h => h.1) word
  intro s hs
  refine ⟨_,rfl,?_,hs.2.1,hs.2.2⟩
  exact (congrArg (· + signExtend21 offset) hs.1).trans target

/-- Iteration through the charged body, decrement, branch and optional back edge. -/
theorem counted (im : Image) (first last : Word) (len price calls : Nat)
    (body : ∀ r, Fragment im len price calls (At first r) (At last r))
    (dec : ∀ n, Fragment im 1 1 0 (At last (BitVec.ofNat 64 (n+1))) (At (last+4) (BitVec.ofNat 64 n)))
    (br : ∀ r, Fragment im 1 1 0 (At (last+4) r)
      (At (if r=0 then last+12 else last+8) r))
    (back : ∀ r, Fragment im 1 1 0 (At (last+8) r) (At first r))
    (n : Nat) (small : n+1 < 2^64) :
    Fragment im (work len (n+1)) (work price (n+1)) ((n+1)*calls)
      (At first (BitVec.ofNat 64 (n+1))) (At (last+12) 0) := by
  induction n with
  | zero =>
    have exit := br 0
    simp only [ite_true] at exit
    have finish := compose (compose (body 1) (dec 0)) exit
    simpa [work,Nat.add_assoc] using finish
  | succ n ih =>
    have nz : BitVec.ofNat 64 (n+1) ≠ 0 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      change (n+1) % 2^64 = 0 at h
      rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
    have more := br (BitVec.ofNat 64 (n+1))
    simp only [nz,ite_false] at more
    have taken := compose (compose (compose (body _) (dec (n+1))) more) (back _)
    have finish := compose taken (ih (by omega))
    simpa [work,Nat.succ_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finish

end CommitGolfCandidate.Reconstruction.CommitLoop
