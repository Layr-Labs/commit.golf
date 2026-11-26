import CommitGolfCandidate.ReconstructedHonestFlagEffect
import CommitGolfCandidate.ReconstructedHonestSizeSchedule

namespace CommitGolfCandidate.Reconstruction.HonestFlagState
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestSizeSchedule HonestFlagEffect HonestRanges

set_option maxRecDepth 32768

abbrev W := BitVec.ofNat 64
def code (b : Bool) : Byte := BitVec.ofNat 8 b.toNat
def atByte (s : MachineState) (k : Nat) := s.getByte (W (base+k))

def Initial (f : Nat→Bool) (s : MachineState) :=
  (∀ k, k<512 → atByte s k=0) ∧ ∀ k, k<512 → atByte s (512+k)=code (f k)

theorem before (trap : HonestInputs.Trapdoor) (ps : Positions) (positive : 0<ps.card)
    (k : Nat) (inside : k<1024) : atByte (HonestInputs.first trap ps) k=0 := by
  let q := W (base+k)
  let w := alignToDword q
  have qnum : q.toNat=base+k := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [base]; omega)]
  have lim := HonestMemoryRanges.aligned_window q
  change w.toNat≤q.toNat ∧ q.toNat≤w.toNat+7 at lim
  rw [qnum] at lim
  have frame := HonestInputs.first_frame trap ps (by omega) w.toNat (by dsimp [base] at *; omega) (by dsimp [base] at *; omega)
  have empty := HonestInputs.initial_zero trap ps w.toNat (Or.inl (by dsimp [base] at *; omega)) (by dsimp [base] at *; omega)
  have word : (HonestInputs.first trap ps).getMem w=0 := by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using frame.trans empty
  change extractByte ((HonestInputs.first trap ps).getMem w) (byteOffset q)=0
  rw [word]; simp [extractByte]

theorem init (trap : HonestInputs.Trapdoor) (ps : Positions) (batch : ps.card=128) :
    Initial (fun _ => false) (HonestInputs.first trap ps) ∧ population (fun _ => false) 9=0 := by
  refine ⟨⟨fun k bound => before trap ps (by omega) k (by omega),fun k bound => before trap ps (by omega) (512+k) (by omega)⟩,?_⟩
  decide

def patch (f : Nat→Bool) (p k : Nat) := if k=p then true else f k

theorem tally_patch (f : Nat→Bool) (p n : Nat) :
    tally (patch f p) n≤tally f n+(if p<n then 1 else 0) := by
  induction n with
  | zero => simp [tally]
  | succ n ih =>
    simp only [tally,patch]
    by_cases eq : n=p
    · subst p; simp at ih ⊢; omega
    · rw [ite_eq_right eq]
      by_cases before : p<n
      · simp only [ite_eq_left before,ite_eq_left (show p<n+1 by omega)] at ih ⊢; omega
      · simp only [ite_eq_right before,ite_eq_right (show ¬p<n+1 by omega)] at ih ⊢; omega

private theorem inRange (k : Nat) (h : k<1024) : Contains flags (W (base+k)) := by
  simp only [Contains,flags,W,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by dsimp [base]; omega)]
  omega

/-- The actual mark may repeat a previously selected cap leaf. Either way its
population increases by at most one, and the 512 lower heap bytes stay zero. -/
theorem transfer {s t : MachineState} (f : Nat→Bool) (known : Initial f s) (event : Option Word)
    (allowed : Valid event) (effect : Effect s t event) :
    ∃ g, Initial g t ∧ population g 9≤population f 9+1 := by
  cases event with
  | none =>
    refine ⟨f,⟨?_,?_⟩,by omega⟩
    · intro k h; exact (effect _ (inRange k (by omega))).trans (known.1 k h)
    · intro k h; exact (effect _ (inRange (512+k) (by omega))).trans (known.2 k h)
  | some p =>
    let j := p.toNat-(base+512)
    have lim : base+512≤p.toNat ∧ p.toNat≤base+1023 := allowed
    have small : j<512 := by dsimp [j]; omega
    have num : base+(512+j)=p.toNat := by dsimp [j]; omega
    have address : p=W (base+(512+j)) := by rw [num]; simp
    have unique (k : Nat) (h : k<1024) : p=W (base+k) ↔ k=512+j := by
      constructor
      · intro eq
        have eqN := congrArg BitVec.toNat eq
        simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show base+k<2^64 by dsimp [base]; omega)] at eqN
        omega
      · intro hk; rw [hk]; exact address
    refine ⟨patch f j,⟨?_,?_⟩,?_⟩
    · intro k h
      have unchanged := effect _ (inRange k (by omega))
      simp only [Option.some.injEq,unique k (by omega),ite_eq_right (show k≠512+j by omega)] at unchanged
      exact unchanged.trans (known.1 k h)
    · intro k h
      have change := effect _ (inRange (512+k) (by omega))
      simp only [Option.some.injEq,unique (512+k) (by omega),Nat.add_right_inj] at change
      by_cases hit : k=j
      · rw [patch,ite_eq_left hit]; change t.getByte _ = 1; simpa only [ite_eq_left hit] using change
      · rw [atByte] at *; simp only [ite_eq_right hit] at change
        exact (change.trans (known.2 k h)).trans (by simp only [patch,ite_eq_right hit])
    · have inc := tally_patch f j 512
      change tally (patch f j) 512 ≤ tally f 512+1
      simpa only [ite_eq_left small] using inc

end CommitGolfCandidate.Reconstruction.HonestFlagState
