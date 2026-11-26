import CommitGolfCandidate.ReconstructedBindingProjection

namespace CommitGolfCandidate.Reconstruction.Binding

abbrev Key := Digest × Digest
abbrev Compress := Key → Digest
abbrev History := List (Key × Digest)

def zeroDigest : Digest := (0, 0)
def unary (x : Digest) : Key := (x, zeroDigest)

def pairKey (child : Nat) (l r : Digest) : Key :=
  (marked child false l, marked child true r)

theorem pair_ne_unary (d : Fin 25) (pos : 0 < d.val) (l r v : Digest) :
    pairKey d l r ≠ unary v := by
  intro same
  have h := congrArg (fun k : Key => k.2.2) same
  exact marked_right_nonzero d pos r h

theorem pair_injective (d : Fin 25) (pos : 0 < d.val) {a b c e : Digest}
    (ca : Canonical d a) (cb : Canonical d b) (cc : Canonical d c) (ce : Canonical d e)
    (same : pairKey d a b = pairKey d c e) : a = c ∧ b = e := by
  exact ⟨marked_injective d pos false ca cc (congrArg Prod.fst same),
         marked_injective d pos true cb ce (congrArg Prod.snd same)⟩

/-- The key used for the final compression after n continuation calls. -/
def lastKey (C : Compress) (seed : Key) : Nat → Key
  | 0 => seed
  | n+1 => unary (C (lastKey C seed n))

def recorded (rows : History) (C : Compress) (seed : Key) (n : Nat) :=
  ∀ j, j ≤ n → (lastKey C seed j, C (lastKey C seed j)) ∈ rows

def FullCollision (rows : History) : Prop :=
  ∃ (a b : Key) (y : Digest), a ≠ b ∧ (a,y) ∈ rows ∧ (b,y) ∈ rows

private theorem seed_of_last (C : Compress) (rows : History) (safe : ¬ FullCollision rows)
    (n : Nat) (a b : Key) (ha : recorded rows C a n) (hb : recorded rows C b n)
    (eq : lastKey C a n = lastKey C b n) : a = b := by
  induction n with
  | zero => exact eq
  | succ n ih =>
    have answer : C (lastKey C a n) = C (lastKey C b n) := congrArg Prod.fst eq
    have keys : lastKey C a n = lastKey C b n := by
      apply Classical.byContradiction
      intro different
      exact safe ⟨_,_,_,different,ha n (by omega), answer ▸ hb n (by omega)⟩
    exact ih (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega)) keys

/-- Collision between distinct chain ends at this depth. Recording both
complete chains keeps this event tied to the paid entries in the history. -/
def PaidCollision (rows : History) (C : Compress) (d : Nat) : Prop :=
  ∃ l r l' r' : Digest,
    let a := pairKey (d+1) l r
    let b := pairKey (d+1) l' r'
    let n := work d - 1
    Canonical (d+1) l ∧ Canonical (d+1) r ∧ Canonical (d+1) l' ∧ Canonical (d+1) r' ∧
    recorded rows C a n ∧ recorded rows C b n ∧
    lastKey C a n ≠ lastKey C b n ∧
    project d (C (lastKey C a n)) = project d (C (lastKey C b n))

def parent (C : Compress) (d : Nat) (l r : Digest) :=
  project d (C (lastKey C (pairKey (d+1) l r) (work d-1)))

theorem children_of_matching_parent (C : Compress) (rows : History) (d : Nat) (inside : d < 24)
    (safe : ¬ FullCollision rows) (noPaid : ¬ PaidCollision rows C d)
    {l r l' r' : Digest}
    (cl : Canonical (d+1) l) (cr : Canonical (d+1) r)
    (cl' : Canonical (d+1) l') (cr' : Canonical (d+1) r')
    (a : recorded rows C (pairKey (d+1) l r) (work d-1))
    (b : recorded rows C (pairKey (d+1) l' r') (work d-1))
    (same : parent C d l r = parent C d l' r') : l = l' ∧ r = r' := by
  let k := pairKey (d+1) l r
  let k' := pairKey (d+1) l' r'
  have last : lastKey C k (work d-1) = lastKey C k' (work d-1) := by
    apply Classical.byContradiction
    intro ne
    exact noPaid ⟨l,r,l',r',cl,cr,cl',cr',a,b,ne,same⟩
  exact pair_injective ⟨d+1,by omega⟩ (by simp) cl cr cl' cr' (seed_of_last C rows safe _ _ _ a b last)

/-- A checked authentication path from a root at depth 0 to the digest at
depth h. The branch directions select the common position in two openings. -/
inductive Path (rows : History) (C : Compress) : Nat → List Bool → Digest → Digest → Prop
  | root (x : Digest) : Path rows C 0 [] x x
  | step {d : Nat} {dir : List Bool} {root middle : Digest} (prevPath : Path rows C d dir root middle)
      (l r : Digest) (side : Bool) (cl : Canonical (d+1) l) (cr : Canonical (d+1) r)
      (seen : recorded rows C (pairKey (d+1) l r) (work d-1))
      (valid : parent C d l r = middle) :
      Path rows C (d+1) (side :: dir) root (if side then r else l)

theorem path_leaf_unique {rows : History} {C : Compress} {h : Nat} (depth : h ≤ 24)
    (safe : ¬ FullCollision rows) (paid : ∀ d, d < h → ¬ PaidCollision rows C d)
    {dir : List Bool} {root x y : Digest}
    (p : Path rows C h dir root x) (q : Path rows C h dir root y) : x = y := by
  induction p generalizing y with
  | root => cases q; rfl
  | @step d dir root mid prevPath l r side cl cr seen valid ih =>
    cases q with
    | step prevPath' l' r' _ cl' cr' seen' valid' =>
      have middle := ih (by omega) (fun j hj => paid j (by omega)) prevPath'
      have result := children_of_matching_parent C rows d (by omega) safe (paid d (by omega))
        cl cr cl' cr' seen seen' (valid.trans (middle.trans valid'.symm))
      cases side <;> simp [result]

end CommitGolfCandidate.Reconstruction.Binding
