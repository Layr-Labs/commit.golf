import CommitGolfCandidate.Execution

namespace CommitGolfCandidate.Reconstruction.CommitControl
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxHeartbeats 2000000

/-- A costed machine fragment. A fault may end the fragment early. A state that
uses all its fuel and continues must establish the stated postcondition. -/
def Fragment (image : Image) (n cycles calls : Nat) (P Q : MachineState → Prop) : Prop :=
  ∀ s, P s → ∀ r ∈ support (execute image n s true),
    r.cycles ≤ cycles ∧ r.oracleCalls ≤ calls ∧ (r.exit = .unfinished → Q r.state)

theorem empty (im : Image) (P : MachineState → Prop) : Fragment im 0 0 0 P P := by
  intro s hs r hr
  simp only [execute, support_pure, Set.mem_singleton_iff] at hr
  subst r; simp [hs]

theorem compose {im : Image} {n m a b u v : Nat} {P Q R : MachineState → Prop}
    (first : Fragment im n a u P Q) (second : Fragment im m b v Q R) :
    Fragment im (n+m) (a+b) (u+v) P R := by
  intro s hs result hr
  rw [execute_add, mem_support_bind_iff] at hr
  obtain ⟨mid, hm, hk⟩ := hr
  obtain ⟨c, q, next⟩ := first s hs mid hm
  by_cases cont : mid.exit = .unfinished
  · simp only [resume,cont,ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hk
    obtain ⟨r, h, rfl⟩ := hk
    obtain ⟨c', q', post⟩ := second _ (next cont) r h
    exact ⟨Nat.add_le_add c c', Nat.add_le_add q q', post⟩
  · simp only [resume,cont,ite_false,support_pure,Set.mem_singleton_iff] at hk
    subst result
    exact ⟨by omega, by omega, fun e => (cont e).elim⟩

def Preserves (s t : MachineState) : Prop :=
  t.pc = s.pc+4 ∧ t.getReg .x5 = s.getReg .x5 ∧ t.getReg .x20 = s.getReg .x20

def ordinary (i : Instr) : Bool :=
  match i with
  | .LUI rd _ | .ADDI rd _ _ | .ADDIW rd _ _ | .SLLI rd _ _
  | .ADD rd _ _ | .OR rd _ _ | .REMU rd _ _ | .LD rd _ _ | .LHU rd _ _ =>
    rd != .x5 && rd != .x20
  | .SB .. | .SH .. | .SW .. | .SD .. => true
  | _ => false

theorem ordinary_preserves (s t : MachineState) (i : Instr) (allowed : ordinary i = true)
    (step : ordinaryStep s (.base i) = some t) : Preserves s t := by
  have reg (rd : Reg) (value : Word) (h₁ : rd ≠ .x5) (h₂ : rd ≠ .x20) :
      Preserves s ((s.setReg rd value).setPC (s.pc+4)) := by
    cases rd <;> simp_all [Preserves, MachineState.setReg, MachineState.getReg, MachineState.setPC]
  cases i <;> simp only [ordinary, Bool.and_eq_true, bne_iff_ne, Bool.false_eq_true] at allowed
  all_goals simp only [ordinaryStep] at step
  all_goals split at step <;> simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst t
  all_goals first | exact reg _ _ allowed.1 allowed.2 | exact ⟨rfl,rfl,rfl⟩

theorem oracle_preserves (s : MachineState) (address : Word) (query : PublicSpec.Domain)
    (answer : PublicSpec.Range query) :
    Preserves s (writeOracleAnswer s address query answer) := by
  rcases query with x | (y | z) <;>
    exact ⟨rfl, writeBits_register .., writeBits_register ..⟩


def At (pc : Word) (counter : Word) (s : MachineState) : Prop :=
  s.pc = pc ∧ s.getReg .x5 = 0 ∧ s.getReg .x20 = counter

private theorem advance {s t : MachineState} {pc r : Word} (h : At pc r s)
    (m : Preserves s t) : At (pc+4) r t :=
  ⟨m.1.trans (congrArg (·+4) h.1), m.2.1.trans h.2.1, m.2.2.trans h.2.2⟩

theorem plain_step (im : Image) (pc counter : Word) (op : Instr)
    (word : ∀ s : MachineState, s.pc = pc → fetch im s = some (.base op))
    (ok : ordinary op = true) :
    Fragment im 1 (instructionCycles (.base op)) 0 (At pc counter) (At (pc+4) counter) := by
  intro s hs r hr
  have fetchOp := word s hs.1
  have notCall : op ≠ .ECALL := by intro h; subst op; cases ok
  have price : 1 ≤ instructionCycles (.base op) := by cases op <;> simp [instructionCycles]
  cases hop : ordinaryStep s (.base op) with
  | none =>
    have stop : execute im 1 s true = pure ⟨.failure,s,1,0⟩ := by
      cases op <;> simp_all [execute]
    rw [stop] at hr
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨price,Nat.zero_le _,fun e => by cases e⟩
  | some next =>
    have moved := advance hs (ordinary_preserves s next op ok hop)
    rw [execute_ordinary_step im (.base op) s next 0 true fetchOp hop] at hr
    simp only [execute, pure_bind,support_pure,Set.mem_singleton_iff] at hr
    subst r; simp [Execution.charge]; exact moved

/-- A public call of unknown kind costs at most the permutation price, 30 cycles. -/
theorem public_step (im : Image) (pc counter : Word)
    (word : ∀ s : MachineState, s.pc = pc → fetch im s = some (.base .ECALL)) :
    Fragment im 1 30 1 (At pc counter) (At (pc+4) counter) := by
  intro s hs r hr
  rw [execute,word _ hs.1] at hr
  simp only [hs.2.1, ite_true] at hr
  cases e : oracleInput s with
  | none =>
    simp only [e,support_pure,Set.mem_singleton_iff] at hr
    subst r; exact ⟨by change 1 ≤ 30; decide, Nat.zero_le _,fun e => by cases e⟩
  | some q =>
    simp only [e,mem_support_bind_iff] at hr
    obtain ⟨ans, _, hr⟩ := hr
    simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at hr
    obtain ⟨_,rfl,rfl⟩ := hr
    have fee : oracleCycles q ≤ 30 := by
      rcases q with a | (b | c) <;> simp [oracleCycles, COMPRESSION_CYCLES, PERMUTATION_CYCLES]
    exact ⟨by simp only [Execution.charge]; omega,by change 1+0 ≤ 1; decide,fun _ => advance hs (oracle_preserves ..)⟩

theorem weaken {im : Image} {n a u : Nat} {P Q R : MachineState → Prop}
    (f : Fragment im n a u P Q) (h : ∀ s, Q s → R s) : Fragment im n a u P R := by
  intro s hs r hr
  obtain ⟨c, q, post⟩ := f s hs r hr
  exact ⟨c, q, fun e => h _ (post e)⟩

/-! ### The compression part of the commitment

From word 53018 on, the oracle kind register a3 (x13) is zero, so every public call is a
compression call and costs eight cycles. `AtC` adds that register to `At`. -/

def AtC (pc counter : Word) (s : MachineState) : Prop := At pc counter s ∧ s.getReg .x13 = 0

/-- The instructions of `ordinary` that also leave a3 unchanged. -/
def ordinaryC (i : Instr) : Bool :=
  match i with
  | .LUI rd _ | .ADDI rd _ _ | .ADDIW rd _ _ | .SLLI rd _ _
  | .ADD rd _ _ | .OR rd _ _ | .REMU rd _ _ | .LD rd _ _ | .LHU rd _ _ =>
    rd != .x5 && rd != .x20 && rd != .x13
  | .SB .. | .SH .. | .SW .. | .SD .. => true
  | _ => false

theorem ordinaryC_ordinary (i : Instr) (h : ordinaryC i = true) : ordinary i = true := by
  cases i <;> simp_all [ordinaryC, ordinary]

theorem ordinaryC_keeps (s t : MachineState) (i : Instr) (allowed : ordinaryC i = true)
    (step : ordinaryStep s (.base i) = some t) : t.getReg .x13 = s.getReg .x13 := by
  have reg (rd : Reg) (value : Word) (h : rd ≠ .x13) :
      ((s.setReg rd value).setPC (s.pc+4)).getReg .x13 = s.getReg .x13 := by
    cases rd <;> simp_all [MachineState.setReg, MachineState.getReg, MachineState.setPC]
  cases i <;> simp only [ordinaryC, Bool.and_eq_true, bne_iff_ne, Bool.false_eq_true] at allowed
  all_goals simp only [ordinaryStep] at step
  all_goals split at step <;> simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst t
  all_goals first | exact reg _ _ allowed.2 | rfl

theorem oracle_keeps (s : MachineState) (address : Word) (query : PublicSpec.Domain)
    (answer : PublicSpec.Range query) :
    (writeOracleAnswer s address query answer).getReg .x13 = s.getReg .x13 := by
  rcases query with x | (y | z) <;> exact writeBits_register ..

/-- With a3 = 0 an accepted public call is a compression call. -/
theorem kind_zero_fee {s : MachineState} {q : PublicSpec.Domain} (zero : s.getReg .x13 = 0)
    (input : oracleInput s = some q) : oracleCycles q = 8 := by
  have k : (s.getReg .x13).toNat = 0 := by rw [zero]; rfl
  cases q with
  | inl x => rfl
  | inr y =>
    exfalso
    simp [oracleInput, k] at input

theorem plain_stepC (im : Image) (pc counter : Word) (op : Instr)
    (word : ∀ s : MachineState, s.pc = pc → fetch im s = some (.base op))
    (ok : ordinaryC op = true) :
    Fragment im 1 (instructionCycles (.base op)) 0 (AtC pc counter) (AtC (pc+4) counter) := by
  intro s hs r hr
  have fetchOp := word s hs.1.1
  have notCall : op ≠ .ECALL := by intro h; subst op; cases ok
  have price : 1 ≤ instructionCycles (.base op) := by cases op <;> simp [instructionCycles]
  cases hop : ordinaryStep s (.base op) with
  | none =>
    have stop : execute im 1 s true = pure ⟨.failure,s,1,0⟩ := by
      cases op <;> simp_all [execute]
    rw [stop] at hr
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨price,Nat.zero_le _,fun e => by cases e⟩
  | some next =>
    have moved := advance hs.1 (ordinary_preserves s next op (ordinaryC_ordinary op ok) hop)
    have kept := ordinaryC_keeps s next op ok hop
    rw [execute_ordinary_step im (.base op) s next 0 true fetchOp hop] at hr
    simp only [execute, pure_bind,support_pure,Set.mem_singleton_iff] at hr
    subst r; simp [Execution.charge]; exact ⟨moved, kept.trans hs.2⟩

theorem public_stepC (im : Image) (pc counter : Word)
    (word : ∀ s : MachineState, s.pc = pc → fetch im s = some (.base .ECALL)) :
    Fragment im 1 8 1 (AtC pc counter) (AtC (pc+4) counter) := by
  intro s hs r hr
  rw [execute,word _ hs.1.1] at hr
  simp only [hs.1.2.1, ite_true] at hr
  cases e : oracleInput s with
  | none =>
    simp only [e,support_pure,Set.mem_singleton_iff] at hr
    subst r; exact ⟨by change 1 ≤ 8; decide, Nat.zero_le _,fun e => by cases e⟩
  | some q =>
    simp only [e,mem_support_bind_iff] at hr
    obtain ⟨ans, _, hr⟩ := hr
    simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at hr
    obtain ⟨_,rfl,rfl⟩ := hr
    have fee : oracleCycles q = 8 := kind_zero_fee hs.2 e
    exact ⟨by simp [Execution.charge,fee],by change 1+0 ≤ 1; decide,
      fun _ => ⟨advance hs.1 (oracle_preserves ..),(oracle_keeps ..).trans hs.2⟩⟩

/-- Word 53017, `addi a3,zero,0`, enters the compression part. -/
theorem kind_reset (im : Image) (pc counter : Word)
    (word : ∀ s : MachineState, s.pc = pc → fetch im s = some (.base (.ADDI .x13 .x0 0))) :
    Fragment im 1 1 0 (At pc counter) (AtC (pc+4) counter) := by
  intro s hs r hr
  rw [execute_ordinary_step im _ s (execInstrBr s (.ADDI .x13 .x0 0)) 0 true (word s hs.1) rfl] at hr
  simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at hr
  subst r
  exact ⟨by simp [Execution.charge,instructionCycles],by simp [Execution.charge],
    fun _ => ⟨⟨congrArg (·+4) hs.1,hs.2.1,hs.2.2⟩,rfl⟩⟩

end CommitGolfCandidate.Reconstruction.CommitControl
