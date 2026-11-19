import CommitGolfCandidate.CounterSaltGame

/-! Linked generator schedules. Each generator call either takes a keyed input (a private key
with a public counter) or reads, in place, the whole reply of an earlier call. The hidden part of
every reply is never disclosed, so every generator input carries private bits: those of the key,
or those of the reply it reads. `CounterSalt` is the schedule with every call keyed;
`NonceChain` (adapted from submission c28dd9ca, dadon) is one keyed start followed by links. -/
namespace CommitGolfCandidate.Permutation.LinkedSalt
open Finset NonceChain
set_option linter.unusedSectionVars false

/-- Call `i` is keyed when `link i = none`; otherwise it reads the reply of the earlier call
`j` with `link i = some j`. No reply feeds two calls. -/
structure Schedule (n : Nat) where
  link : Fin n → Option (Fin n)
  link_lt : ∀ i j, link i = some j → j.val < i.val
  link_inj : ∀ i i' j, link i = some j → link i' = some j → i = i'

variable {S K : Type} {n : Nat}

/-- The input of call `i`, given the keyed inputs `x`, the key `k` and the replies `y`. -/
def Schedule.input (σ : Schedule n) (x : Fin n → K → S) (k : K) (y : Fin n → S) (i : Fin n) : S :=
  match σ.link i with
  | none => x i k
  | some j => y j

/-- The replies of the real generator under the permutation `π`. -/
def Schedule.reply (σ : Schedule n) (π : Equiv.Perm S) (x : Fin n → K → S) (k : K) (i : Fin n) : S :=
  π (σ.input x k (fun j => if _h : j.val < i.val then σ.reply π x k j else x j k) i)
termination_by i.val

/-- Each real reply answers its own input. -/
theorem Schedule.reply_eq (σ : Schedule n) (π : Equiv.Perm S) (x : Fin n → K → S) (k : K)
    (i : Fin n) : σ.reply π x k i = π (σ.input x k (σ.reply π x k) i) := by
  rw [Schedule.reply]
  congr 1
  unfold Schedule.input
  cases h : σ.link i with
  | none => rfl
  | some j => exact dif_pos (σ.link_lt i j h)

/-- The bad event for a key `k`, proposed replies `y` and a public trace `t`: a keyed input was
queried or equals a reply, or a reply was queried, answered or repeated. -/
def LinkedBad [DecidableEq S] (x : Fin n → K → S) (k : K) (y : Fin n → S) (t : Trace S) : Prop :=
  (∃ i, x i k ∈ t.usedIn ∪ univ.image y) ∨ Exposed y (t.usedIn ∪ t.usedOut)

end CommitGolfCandidate.Permutation.LinkedSalt
