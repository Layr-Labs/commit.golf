import CommitGolfCandidate.ReconstructedHonestCapInvariant
import CommitGolfCandidate.ReconstructedHonestFlagState

namespace CommitGolfCandidate.Reconstruction.HonestSizeRows
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestSizeSchedule HonestCapPlan HonestFlagState
open HonestCapRam (activeBase)
open HonestCapTables (w)

set_option maxRecDepth 32768

/-- During a level scan, child flags are fixed, the parent prefix has been
computed, and every flag preceding that prefix remains zero. -/
structure Rows (f : Nat→Bool) (d j : Nat) (s : MachineState) : Prop where
  child : ∀ k, k<2*pairs d → atByte s (2*pairs d+k)=code (row f (9-d) k)
  parent : ∀ k, k<pairs d → atByte s (pairs d+k)=if k<j then code (row f ((9-d)+1) k) else 0
  zero : ∀ k, k<pairs d → atByte s k=0

def scanned (d : Nat) : Phase→Nat
  | .enter | .level => 0
  | .scan j _ | .scanGuard j _ => j
  | _ => pairs d

def At (f : Nat→Bool) (v : Node) (s : MachineState) :=
  v.phase≠.returned → Rows f v.depth (scanned v.depth v.phase) s

theorem init {f : Nat→Bool} {s : MachineState} (initial : Initial f s) : At f ⟨9,.enter⟩ s := by
  intro _; refine ⟨?_,?_,?_⟩
  · exact initial.2
  · intro k h; exact initial.1 _ (by change k<256 at h; change 256+k<512; omega)
  · intro k h; exact initial.1 _ (by change k<256 at h; omega)

theorem carry {f : Nat→Bool} {s t : MachineState} {d j : Nat} (rows : Rows f d j s)
    (width : pairs d≤256) (same : ∀ k, k<1024 → atByte t k=atByte s k) : Rows f d j t := by
  refine ⟨?_,?_,?_⟩
  · intro k h; exact (same _ (by omega)).trans (rows.child _ h)
  · intro k h; exact (same _ (by omega)).trans (rows.parent _ h)
  · intro k h; exact (same _ (by omega)).trans (rows.zero _ h)

theorem descend {f : Nat→Bool} {s : MachineState} {d : Nat} (rows : Rows f d (pairs d) s)
    (positive : 1<d) (small : d≤9) : Rows f (d-1) 0 s := by
  have level : 2*pairs (d-1)=pairs d := by
    have a := (HonestCapState.powers (d-1) (by omega)).1
    change 2*pairs (d-1)=2^(d-1); exact a.symm
  have old : 9-(d-1)=(9-d)+1 := by omega
  refine ⟨?_,?_,?_⟩
  · rw [level,old]; intro k h; simpa only [ite_eq_left h] using rows.parent k h
  · intro k h; exact rows.zero _ (by omega)
  · intro k h; exact rows.zero _ (by omega)

theorem scanned_pair {f : Nat→Bool} {s t : MachineState} {d j : Nat} (rows : Rows f d j s)
    (width : pairs d≤256) (next : j<pairs d)
    (delta : ∀ k, k<1024 → atByte t k=if (row f (9-d) (2*j)||row f (9-d) (2*j+1)) && k==pairs d+j
       then 1 else atByte s k) : Rows f d (j+1) t := by
  refine ⟨?_,?_,?_⟩
  · intro k h; rw [delta _ (by omega)]
    simp only [beq_eq_false_iff_ne.mpr (show 2*pairs d+k≠pairs d+j by omega),Bool.and_false,
      Bool.false_eq_true,ite_false]
    exact rows.child k h
  · intro k h; rw [delta _ (by omega),rows.parent _ h]
    by_cases hit : k=j
    · subst k
      simp only [beq_self_eq_true,Bool.and_true,Nat.lt_succ_self,ite_true,Nat.lt_irrefl,ite_false]
      change (if row f (9-d) (2*j)||row f (9-d) (2*j+1) then _ else _)=
        code (row f (9-d) (2*j)||row f (9-d) (2*j+1))
      cases row f (9-d) (2*j)||row f (9-d) (2*j+1) <;> rfl
    · simp only [beq_eq_false_iff_ne.mpr (show pairs d+k≠pairs d+j by omega),Bool.and_false,Bool.false_eq_true,ite_false]
      simp only [show k<j+1 ↔ k<j by omega]
  · intro k h; rw [delta _ (by omega)]
    simp only [beq_eq_false_iff_ne.mpr (show k≠pairs d+j by omega),Bool.and_false,Bool.false_eq_true,ite_false]
    exact rows.zero k h

theorem inSpan {k : Nat} (h : k<1024) : HonestRanges.Contains HonestFlagEffect.flags (w (activeBase+k)) := by
  change activeBase≤(w (activeBase+k)).toNat ∧ (w (activeBase+k)).toNat≤activeBase+1023
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [activeBase]; omega)]
  omega

theorem addr_eq {k j : Nat} (a : k<1024) (b : j<1024) :
    (w (activeBase+k)==w (activeBase+j))=(k==j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h; have eq := congrArg BitVec.toNat h
    simp only [w,BitVec.toNat_ofNat] at eq
    dsimp [activeBase] at eq
    omega
  · rintro rfl; rfl

end CommitGolfCandidate.Reconstruction.HonestSizeRows
