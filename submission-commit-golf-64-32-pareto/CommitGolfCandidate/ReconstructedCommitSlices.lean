import CommitGolfCandidate.ReconstructedCommitBlocks

namespace CommitGolfCandidate.Reconstruction.CommitSlices
open CommitGolf CommitGolf.Riscv CommitGolf.ArtifactEncoding RiscvZkvm.Rv64 CommitControl CommitBlocks

set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode

/-- At a segment boundary the certificate carries a price and a public-call count. -/
structure Summary where
  good : Bool
  cycles : Nat
  queries : Nat
  deriving DecidableEq, Repr

def emptySummary : Summary := ⟨true,0,0⟩
def together (a b : Summary) : Summary := ⟨a.good && b.good,a.cycles+b.cycles,a.queries+b.queries⟩
def priceWord (w : BitVec 32) : Summary :=
  match decodeInstruction w with
  | some (.base .ECALL) => ⟨true,30,1⟩
  | some (.base op) => ⟨ordinary op, instructionCycles (.base op),0⟩
  | _ => ⟨false,0,0⟩

theorem word_step {im : Image} (pc c : Word) (w : BitVec 32)
    (read : ∀ s : MachineState, s.pc = pc → fetch im s = decodeInstruction w)
    (good : (priceWord w).good = true) :
    Fragment im 1 (priceWord w).cycles (priceWord w).queries (At pc c) (At (pc+4) c) := by
  have eqs : (priceWord w).good = validStraight w ∧
      (priceWord w).cycles = cost w ∧ (priceWord w).queries = calls w := by
    cases h : decodeInstruction w with
    | none => simp [priceWord,h] at good
    | some i =>
      cases i with
      | base op => cases op <;> simp [priceWord,validStraight,cost,calls,h]
      | word op rd a b => simp [priceWord,h] at good
      | sraiw rd a b => simp [priceWord,h] at good
  rw [eqs.2.1,eqs.2.2]
  exact step pc c w read (eqs.1 ▸ good)

def leafSum (payload start : Nat) : Nat → Summary
  | 0 => emptySummary
  | n+1 => together (leafSum payload start n)
      (priceWord (BitVec.ofNat 32 (payload >>> (32*(start+n)))))

def summarize {n : Nat} (packed : Packed n) (lo hi : Nat) : Summary :=
  match packed with
  | .chunk _ payload => leafSum payload lo (hi-lo)
  | @Packed.join l _ left right =>
      if hi ≤ l then summarize left lo hi
      else if l ≤ lo then summarize right (lo-l) (hi-l)
      else together (summarize left lo l) (summarize right 0 (hi-l))

def View (im : Image) {n : Nat} (p : Packed n) (baseIdx : Nat) : Prop :=
  ∀ (j : Fin n) (s : MachineState), s.pc = addr (baseIdx+j.val) →
    fetch im s = decodeInstruction (p.get 32 j)

private theorem one_chunk (im : Image) (payload baseIdx lo len : Nat) (c : Word)
    (read : ∀ j < len, ∀ s : MachineState, s.pc = addr (baseIdx+lo+j) →
      fetch im s = decodeInstruction (BitVec.ofNat 32 (payload >>> (32*(lo+j)))))
    (good : (leafSum payload lo len).good = true) :
    Fragment im len (leafSum payload lo len).cycles (leafSum payload lo len).queries
      (At (addr (baseIdx+lo)) c) (At (addr (baseIdx+lo+len)) c) := by
  induction len with
  | zero => exact empty im _
  | succ n ih =>
    simp only [leafSum,together,Bool.and_eq_true] at good
    obtain ⟨h1,h2⟩ := good
    have left := ih (fun j hj => read j (by omega)) h1
    have right := word_step (addr (baseIdx+lo+n)) c _ (read n (by omega)) h2
    simpa only [Nat.add_succ,addr_next,leafSum,together] using compose left right

theorem sound (im : Image) {n : Nat} (p : Packed n) (baseIdx lo hi : Nat) (c : Word)
    (view : View im p baseIdx) (ordered : lo ≤ hi) (bounded : hi ≤ n)
    (good : (summarize p lo hi).good = true) :
    Fragment im (hi-lo) (summarize p lo hi).cycles (summarize p lo hi).queries
      (At (addr (baseIdx+lo)) c) (At (addr (baseIdx+hi)) c) := by
  induction p generalizing baseIdx lo hi with
  | chunk n data =>
    have h := one_chunk im data baseIdx lo (hi-lo) c (by
      intro j hj s pc
      exact view ⟨lo+j,by omega⟩ s (by simpa only [Nat.add_assoc] using pc)) good
    rwa [show baseIdx+lo+(hi-lo)=baseIdx+hi by omega] at h
  | @join l r left right ihl ihr =>
    have leftView : View im left baseIdx := by
      intro i s loc
      let j : Fin (l+r) := ⟨i.val,by have := i.isLt; omega⟩
      have h := view j s loc
      rw [get_join_left 32 left right j (show j.val < l from i.isLt)] at h
      exact h
    have rightView : View im right (baseIdx+l) := by
      intro i s loc
      let j : Fin (l+r) := ⟨l+i.val,by have := i.isLt; omega⟩
      have h := view j s (by simpa [j,Nat.add_assoc] using loc)
      rw [get_join_right _ _ _ _ (show ¬j.val<l by dsimp [j]; omega)] at h
      convert h using 1
      congr 3
      apply Fin.ext
      simp [j]
    simp only [summarize] at good ⊢
    by_cases atLeft : hi ≤ l
    · simp only [atLeft,ite_true] at good ⊢
      exact ihl _ _ _ leftView ordered (by omega) good
    · simp only [atLeft,ite_false] at good ⊢
      by_cases atRight : l ≤ lo
      · simp only [atRight,ite_true] at good ⊢
        have h := ihr (baseIdx+l) (lo-l) (hi-l) rightView (by omega) (by omega) good
        rwa [show hi-l-(lo-l)=hi-lo by omega,show baseIdx+l+(lo-l)=baseIdx+lo by omega,
             show baseIdx+l+(hi-l)=baseIdx+hi by omega] at h
      · simp only [atRight,ite_false,together,Bool.and_eq_true] at good ⊢
        obtain ⟨lg,rg⟩ := good
        have first := ihl baseIdx lo l leftView (by omega) (by omega) lg
        have last := ihr (baseIdx+l) 0 (hi-l) rightView (by omega) (by omega) rg
        simp only [Nat.sub_zero,Nat.add_zero] at last
        rw [show baseIdx+l+(hi-l)=baseIdx+hi by omega] at last
        have h := compose first last
        rwa [show l-lo+(hi-l)=hi-lo by omega] at h

/-! ### Compression part: `AtC` states, public calls at eight cycles -/

def priceWordC (w : BitVec 32) : Summary :=
  match decodeInstruction w with
  | some (.base .ECALL) => ⟨true,8,1⟩
  | some (.base op) => ⟨ordinaryC op, instructionCycles (.base op),0⟩
  | _ => ⟨false,0,0⟩

theorem word_stepC {im : Image} (pc c : Word) (w : BitVec 32)
    (read : ∀ s : MachineState, s.pc = pc → fetch im s = decodeInstruction w)
    (good : (priceWordC w).good = true) :
    Fragment im 1 (priceWordC w).cycles (priceWordC w).queries (AtC pc c) (AtC (pc+4) c) := by
  cases h : decodeInstruction w with
  | none => simp [priceWordC,h] at good
  | some i =>
    cases i with
    | word op rd a b => simp [priceWordC,h] at good
    | sraiw rd a b => simp [priceWordC,h] at good
    | base op =>
      have got := fun (s : MachineState) (hs : s.pc = pc) => (read s hs).trans h
      by_cases sys : op = .ECALL
      · subst op
        simpa only [priceWordC,h] using public_stepC im pc c got
      · have ok : ordinaryC op = true := by cases op <;> simp_all [priceWordC]
        have cp : (priceWordC w).cycles = instructionCycles (.base op) := by
          cases op <;> simp_all [priceWordC]
        have cq : (priceWordC w).queries = 0 := by cases op <;> simp_all [priceWordC]
        rw [cp,cq]; exact plain_stepC im pc c op got ok

def leafSumC (payload start : Nat) : Nat → Summary
  | 0 => emptySummary
  | n+1 => together (leafSumC payload start n)
      (priceWordC (BitVec.ofNat 32 (payload >>> (32*(start+n)))))

def summarizeC {n : Nat} (packed : Packed n) (lo hi : Nat) : Summary :=
  match packed with
  | .chunk _ payload => leafSumC payload lo (hi-lo)
  | @Packed.join l _ left right =>
      if hi ≤ l then summarizeC left lo hi
      else if l ≤ lo then summarizeC right (lo-l) (hi-l)
      else together (summarizeC left lo l) (summarizeC right 0 (hi-l))

private theorem one_chunkC (im : Image) (payload baseIdx lo len : Nat) (c : Word)
    (read : ∀ j < len, ∀ s : MachineState, s.pc = addr (baseIdx+lo+j) →
      fetch im s = decodeInstruction (BitVec.ofNat 32 (payload >>> (32*(lo+j)))))
    (good : (leafSumC payload lo len).good = true) :
    Fragment im len (leafSumC payload lo len).cycles (leafSumC payload lo len).queries
      (AtC (addr (baseIdx+lo)) c) (AtC (addr (baseIdx+lo+len)) c) := by
  induction len with
  | zero => exact empty im _
  | succ n ih =>
    simp only [leafSumC,together,Bool.and_eq_true] at good
    obtain ⟨h1,h2⟩ := good
    have left := ih (fun j hj => read j (by omega)) h1
    have right := word_stepC (addr (baseIdx+lo+n)) c _ (read n (by omega)) h2
    simpa only [Nat.add_succ,addr_next,leafSumC,together] using compose left right

theorem soundC (im : Image) {n : Nat} (p : Packed n) (baseIdx lo hi : Nat) (c : Word)
    (view : View im p baseIdx) (ordered : lo ≤ hi) (bounded : hi ≤ n)
    (good : (summarizeC p lo hi).good = true) :
    Fragment im (hi-lo) (summarizeC p lo hi).cycles (summarizeC p lo hi).queries
      (AtC (addr (baseIdx+lo)) c) (AtC (addr (baseIdx+hi)) c) := by
  induction p generalizing baseIdx lo hi with
  | chunk n data =>
    have h := one_chunkC im data baseIdx lo (hi-lo) c (by
      intro j hj s pc
      exact view ⟨lo+j,by omega⟩ s (by simpa only [Nat.add_assoc] using pc)) good
    rwa [show baseIdx+lo+(hi-lo)=baseIdx+hi by omega] at h
  | @join l r left right ihl ihr =>
    have leftView : View im left baseIdx := by
      intro i s loc
      let j : Fin (l+r) := ⟨i.val,by have := i.isLt; omega⟩
      have h := view j s loc
      rw [get_join_left 32 left right j (show j.val < l from i.isLt)] at h
      exact h
    have rightView : View im right (baseIdx+l) := by
      intro i s loc
      let j : Fin (l+r) := ⟨l+i.val,by have := i.isLt; omega⟩
      have h := view j s (by simpa [j,Nat.add_assoc] using loc)
      rw [get_join_right _ _ _ _ (show ¬j.val<l by dsimp [j]; omega)] at h
      convert h using 1
      congr 3
      apply Fin.ext
      simp [j]
    simp only [summarizeC] at good ⊢
    by_cases atLeft : hi ≤ l
    · simp only [atLeft,ite_true] at good ⊢
      exact ihl _ _ _ leftView ordered (by omega) good
    · simp only [atLeft,ite_false] at good ⊢
      by_cases atRight : l ≤ lo
      · simp only [atRight,ite_true] at good ⊢
        have h := ihr (baseIdx+l) (lo-l) (hi-l) rightView (by omega) (by omega) good
        rwa [show hi-l-(lo-l)=hi-lo by omega,show baseIdx+l+(lo-l)=baseIdx+lo by omega,
             show baseIdx+l+(hi-l)=baseIdx+hi by omega] at h
      · simp only [atRight,ite_false,together,Bool.and_eq_true] at good ⊢
        obtain ⟨lg,rg⟩ := good
        have first := ihl baseIdx lo l leftView (by omega) (by omega) lg
        have last := ihr (baseIdx+l) 0 (hi-l) rightView (by omega) (by omega) rg
        simp only [Nat.sub_zero,Nat.add_zero] at last
        rw [show baseIdx+l+(hi-l)=baseIdx+hi by omega] at last
        have h := compose first last
        rwa [show l-lo+(hi-l)=hi-lo by omega] at h

theorem commit_view : View (Artifact.submission.image .commit) Artifact.commitCode 0 := by
  intro j s h
  have code : (Artifact.submission.image .commit).code = ArtifactEncoding.decode 32 Artifact.commitCode :=
    Eq.refl (ArtifactEncoding.decode 32 Artifact.commitCode)
  exact @fetch_packed 150132 _ Artifact.commitCode code j.val j.isLt
    (by have := j.isLt; omega) s (by simpa [addr] using h)

end CommitGolfCandidate.Reconstruction.CommitSlices
