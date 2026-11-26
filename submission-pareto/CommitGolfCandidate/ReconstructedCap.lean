import CommitGolfCandidate.ReconstructedProfile

namespace CommitGolfCandidate.Reconstruction

/-- A missing sibling contributes a field only if its parent is visited. -/
def missing (left right : Bool) : Nat :=
  if left == right then 0 else 1

/-- Four occupied or unoccupied cap endpoints below one depth-seven prefix. -/
structure Block where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
deriving DecidableEq

def Block.active (b : Block) := b.a || b.b || b.c || b.d
def Block.endpoints (b : Block) := b.a.toNat + b.b.toNat + b.c.toNat + b.d.toNat
def Block.outer (b : Block) := missing (b.a || b.b) (b.c || b.d)
def Block.inner (b : Block) := missing b.a b.b + missing b.c b.d

private theorem block_counts (b : Block) :
    b.outer + b.inner ≤ 2 * b.active.toNat ∧
    b.outer ≤ b.endpoints ∧ b.inner ≤ b.endpoints := by
  rcases b with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- A binary occupancy tree with four cap endpoints per bottom block. -/
inductive Cap : Nat → Type where
  | block : Block → Cap 0
  | fork {h : Nat} : Cap h → Cap h → Cap (h + 1)

structure Counts where
  active : Bool
  blocks : Nat
  ordinary : Nat
  outer : Nat
  inner : Nat
  endpoints : Nat

def Cap.count {h : Nat} : Cap h → Counts
  | .block b => ⟨b.active, b.active.toNat, 0, b.outer, b.inner, b.endpoints⟩
  | .fork l r =>
    let x := l.count
    let y := r.count
    ⟨x.active || y.active, x.blocks + y.blocks,
     x.ordinary + y.ordinary + missing x.active y.active,
     x.outer + y.outer, x.inner + y.inner, x.endpoints + y.endpoints⟩

private theorem vacancy (a b : Bool) :
    missing a b + (! (a || b)).toNat ≤ (!a).toNat + (!b).toNat := by
  cases a <;> cases b <;> decide

private theorem counts_bound {h : Nat} (t : Cap h) :
    t.count.ordinary + t.count.blocks + (!t.count.active).toNat ≤ 2 ^ h ∧
    t.count.outer + t.count.inner ≤ 2 * t.count.blocks ∧
    t.count.outer ≤ t.count.endpoints ∧ t.count.inner ≤ t.count.endpoints := by
  induction t with
  | block b =>
    have hb := block_counts b
    simp only [Cap.count, Nat.zero_add, Nat.pow_zero]
    refine ⟨?_, hb⟩
    cases b.active <;> decide
  | @fork h l r hl hr =>
    obtain ⟨hl₁, hl₂, hl₃, hl₄⟩ := hl
    obtain ⟨hr₁, hr₂, hr₃, hr₄⟩ := hr
    have hv := vacancy l.count.active r.count.active
    simp only [Cap.count, Nat.pow_succ]
    omega

/-- Count low fields and even allow separate last, partial groups at depths eight and nine. -/
def capBits (c : Counts) : Nat :=
  240 * c.ordinary + sameSize.capLow * (c.outer + c.inner) +
    sameSize.capHeader *
      ((c.outer + sameSize.capGroup - 1) / sameSize.capGroup +
       (c.inner + sameSize.capGroup - 1) / sameSize.capGroup)

theorem cap_bound (t : Cap 7) (batch : t.count.endpoints ≤ 128) :
    capBits t.count ≤ 59328 := by
  obtain ⟨ho, hp, hx, hy⟩ := counts_bound t
  change _ ≤ 128 at ho
  change 240 * _ + 224 * _ + 31 * ((_ + 4 - 1) / 4 + (_ + 4 - 1) / 4) ≤ 59328
  omega

theorem cap_bound_all (t : Cap 7) : capBits t.count ≤ 59359 := by
  obtain ⟨ho, hp, _, _⟩ := counts_bound t
  change _ ≤ 128 at ho
  have fields : 240 * t.count.ordinary + 224 * (t.count.outer + t.count.inner) ≤ 57344 := by omega
  have groups : (t.count.outer + 4 - 1) / 4 + (t.count.inner + 4 - 1) / 4 ≤ 65 := by omega
  change 240 * _ + 224 * _ + 31 * ((_ + 4 - 1) / 4 + (_ + 4 - 1) / 4) ≤ 59359
  omega

/-- A canonical spread of 128 endpoints witnesses tightness of this format bound. -/
def spread : (h : Nat) → Cap h
  | 0 => .block ⟨true, false, false, false⟩
  | h + 1 => .fork (spread h) (spread h)

theorem cap_tight : (spread 7).count.endpoints = 128 ∧
    capBits (spread 7).count = 59328 := by decide

def alignedBytes (bits : Nat) := (bits + 63) / 64 * 8

theorem format_bound (t : Cap 7) (batch : t.count.endpoints ≤ 128) :
    alignedBytes (128 * recordBits + capBits t.count) ≤ sameSize.proofBytes := by
  have hc := cap_bound t batch
  rw [lower_record.2.2]
  change (128 * 3633 + capBits t.count + 63) / 64 * 8 ≤ 65544
  omega

theorem format_tight :
    alignedBytes (128 * recordBits + capBits (spread 7).count) = sameSize.proofBytes := by
  rw [cap_tight.2, lower_record.2.2]
  decide

end CommitGolfCandidate.Reconstruction
