import CommitGolfCandidate.ReconstructedHonestRegisters

namespace CommitGolfCandidate.Reconstruction.HonestRanges
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestRegisters

/-- An inclusive interval for an unsigned machine word. The unbounded case stays
compact, since most digest values are deliberately unconstrained. -/
structure Range where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

abbrev limit : Nat := 2^64
def any : Range := ⟨0,limit-1⟩
def point (v : Word) : Range := ⟨v.toNat,v.toNat⟩
def Contains (r : Range) (v : Word) := r.lo ≤ v.toNat ∧ v.toNat ≤ r.hi

def singleton (r : Range) : Option Word := if r.lo = r.hi then some (BitVec.ofNat 64 r.lo) else none

theorem arbitrary (v : Word) : Contains any v := ⟨Nat.zero_le _,by have := v.isLt; change _ ≤ 2^64-1; omega⟩
theorem precise (v : Word) : Contains (point v) v := ⟨le_rfl,le_rfl⟩
theorem singleton_ok {r : Range} {v u : Word} (within : Contains r v) (exact : singleton r = some u) :
    v = u := by
  simp only [singleton] at exact
  split at exact
  · rename_i eq
    obtain rfl := Option.some.inj exact
    obtain ⟨lo,hi⟩ := within
    have val : r.lo = v.toNat := by omega
    simp [val]
  · contradiction

def narrow (r q : Range) : Bool := q.lo≤r.lo && r.hi≤q.hi
theorem weaken {r q : Range} {v : Word} (ok : narrow r q = true) (within : Contains r v) : Contains q v := by
  simp only [narrow,Bool.and_eq_true,decide_eq_true_eq] at ok
  exact ⟨ok.1.trans within.1,within.2.trans ok.2⟩

def wrap (a b : Nat) : Range :=
  if b<limit then ⟨a,b⟩ else if limit≤a ∧ b<2*limit then ⟨a-limit,b-limit⟩ else any

theorem wrap_ok (a b n : Nat) (lower : a≤n) (upper : n≤b) (v : Word) (value : v.toNat=n%limit) :
    Contains (wrap a b) v := by
  unfold wrap
  split
  · rename_i small
    change _ ≤ _ ∧ _ ≤ _
    rw [value,Nat.mod_eq_of_lt (by omega)]
    exact ⟨lower,upper⟩
  · split
    · rename_i cut
      change _ ≤ _ ∧ _ ≤ _
      rw [value]
      dsimp [limit] at *
      omega
    · exact arbitrary _

def plus (a b : Range) := wrap (a.lo+b.lo) (a.hi+b.hi)
def minus (a b : Range) := if b.hi≤limit then wrap (limit+a.lo-b.hi) (limit+a.hi-b.lo) else any

theorem plus_ok {a b : Range} {u v : Word} (hu : Contains a u) (hv : Contains b v) :
    Contains (plus a b) (u+v) := by
  apply wrap_ok _ _ (u.toNat+v.toNat) (Nat.add_le_add hu.1 hv.1) (Nat.add_le_add hu.2 hv.2)
  exact BitVec.toNat_add _ _

theorem minus_ok {a b : Range} {u v : Word} (hu : Contains a u) (hv : Contains b v) :
    Contains (minus a b) (u-v) := by
  obtain ⟨l,h⟩ := hu; obtain ⟨l',h'⟩ := hv
  unfold minus; split
  · apply wrap_ok _ _ (limit+u.toNat-v.toNat) (by omega) (by omega)
    simp only [BitVec.toNat_sub,limit]; have := v.isLt; congr 1; omega
  · exact arbitrary _

def right (r : Range) (shift : Nat) : Range := ⟨r.lo / 2^shift,r.hi / 2^shift⟩
def left (r : Range) (shift : Nat) : Range := wrap (r.lo*2^shift) (r.hi*2^shift)
def band (a b : Range) : Range := ⟨0,min a.hi b.hi⟩

theorem right_ok {r : Range} {v : Word} (within : Contains r v) (k : Nat) : Contains (right r k) (v>>>k) := by
  simp only [right,Contains,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  exact ⟨Nat.div_le_div_right within.1,Nat.div_le_div_right within.2⟩

theorem left_ok {r : Range} {v : Word} (within : Contains r v) (k : Nat) : Contains (left r k) (v<<<k) := by
  apply wrap_ok _ _ (v.toNat*2^k) (Nat.mul_le_mul_right _ within.1) (Nat.mul_le_mul_right _ within.2)
  simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,limit]

theorem band_ok {a b : Range} {u v : Word} (hu : Contains a u) (hv : Contains b v) :
    Contains (band a b) (u&&&v) := by
  simp only [band,Contains,BitVec.toNat_and,Nat.zero_le,true_and,le_min_iff]
  exact ⟨Nat.and_le_left.trans hu.2,Nat.and_le_right.trans hv.2⟩

abbrev Registers := Reg → Range
def Meaning (s : MachineState) (m : Registers) := ∀ r, Contains (m r) (s.getReg r)

def exactFile (m : Registers) : Known := fun r => singleton (m r)

theorem exactFile_ok {s : MachineState} {m : Registers} (ok : Meaning s m) : Agrees s (exactFile m) :=
  fun r _ h => singleton_ok (ok r) h

/-- Nonconstant pointer operations. Unsupported data operations simply lose
precision, while precise ALU inputs use the existing exact word semantics. -/
def approximate (op : Instruction) (m : Registers) (r : Reg) : Range :=
  match op with
  | .base (.ADD d a b) => if d=r then plus (m a) (m b) else any
  | .base (.SUB d a b) => if d=r then minus (m a) (m b) else any
  | .base (.AND d a b) => if d=r then band (m a) (m b) else any
  | .base (.ADDI d a n) => if d=r then plus (m a) (point (signExtend12 n)) else any
  | .base (.ANDI d a n) => if d=r then band (m a) (point (signExtend12 n)) else any
  | .base (.SRLI d a n) => if d=r then right (m a) n.toNat else any
  | .base (.SLLI d a n) => if d=r then left (m a) n.toNat else any
  | _ => any

private theorem approx_ok (s t : MachineState) (m : Registers) (op : Instruction) (r : Reg)
    (ok : Meaning s m) (step : ordinaryStep s op = some t) (nz : r≠.x0) :
    Contains (approximate op m r) (t.getReg r) := by
  cases op with
  | word _ _ _ _ | sraiw _ _ _ => exact arbitrary _
  | base op =>
    cases op <;> first | exact arbitrary _ | skip
    all_goals simp only [approximate]
    all_goals split
    all_goals try exact arbitrary _
    all_goals rename_i eq; subst r
    all_goals simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
    all_goals subst t
    all_goals simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nz]
    all_goals first | exact plus_ok (ok _) (ok _) | exact plus_ok (ok _) (precise _)
                    | exact minus_ok (ok _) (ok _) | exact band_ok (ok _) (ok _) | exact band_ok (ok _) (precise _)
                    | exact right_ok (ok _) _ | exact left_ok (ok _) _

def update (m : Registers) (op : Instruction) (r : Reg) : Range :=
  if r = .x0 then point 0 else if writesReg op r then
    match HonestRegisters.update (exactFile m) op r with
    | some w => point w
    | none => approximate op m r
  else m r

theorem update_ok {s t : MachineState} (m : Registers) (op : Instruction) (ok : Meaning s m)
    (step : ordinaryStep s op = some t) : Meaning t (update m op) := by
  intro r
  unfold update
  split
  · rename_i eq; subst r; exact precise _
  · rename_i nz
    split
    · split
      · rename_i w eq
        rw [HonestRegisters.update_valid s t op _ (exactFile_ok ok) step r w eq]
        exact precise _
      · exact approx_ok s t m op r ok step nz
    · rename_i unwritten
      simp only [Bool.not_eq_true] at unwritten
      rw [ordinary_step_keeps _ _ _ _ step unwritten]
      exact ok r

end CommitGolfCandidate.Reconstruction.HonestRanges
