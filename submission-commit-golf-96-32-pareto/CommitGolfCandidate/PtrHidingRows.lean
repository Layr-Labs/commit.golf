import CommitGolfCandidate.LateHidingTree
import CommitGolfCandidate.MidHidingObserver

/-! All unopened leaf digests become fresh in one step, for the chained tree.

After the three unsalted calls of every leaf have been answered, each leaf's
final row is a fixed function of the pair words. Four games share one table,
one draw of pair words and one vector `fresh` of independent digests.

| game | table | leaf layer |
| --- | --- | --- |
| real | plain | read at every row |
| all programmed | every row answers its fresh digest | `fresh` |
| opened programmed | opened rows answer their fresh digest | `fresh` |
| ideal | plain | read at opened rows, `fresh` elsewhere |

Real and all-programmed agree exactly when the rows are distinct and uncached
(`GoodRows`), and so do ideal and opened-programmed. In between, the tree is the
same unless some row is an input the tree reads. Those inputs are computed from
`fresh` and the plain table, so no salt enters them and a union bound over the
pair words applies. With equal trees the two programmed games differ only in the
answers at unopened rows, and the observer finds one with probability at most
`8 * budget / 2^128`, once a midpoint shared by five pairs is excluded.

This is `S4HidingIdeal` of the shared-midpoint tree with the tree of `S5Model`:
one ternary level, binary parents above it, and chains of up to sixteen calls
at heights 8 to 15. A chain's later inputs depend on the table's earlier
answers. `rowsRead` therefore lists every call of every chain under one table,
and `chain_congr` shows by induction along the chain that a table agreeing on
that list computes the same chain. Stored widths play no part, because
`storeReply` is applied to values that are already equal.

The decomposition follows dadon's b4f31491 (`MoonHiding`, section 5). Programming
the opened rows as well is what removes his query-level tree invariant. -/
set_option Elab.async false
set_option maxHeartbeats 350000
namespace CommitGolfCandidate.PtrHiding
open CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance idealDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

attribute [local irreducible] List.finRange Chained.Binary.opening

/-! ### What the tree reads

`S5Model` applies the hash to `Chained.Input`, a 768-bit vector, and the
contract's `Compression` takes `BitVec COMPRESSION_INPUT_LENGTH`. The two types
agree only after unfolding the parameter. A rewrite whose pattern has to match
such a block does not fire, so the proofs below use `rfl`, `exact` and the
unfolding lemmas `parent_rows_chain` and `parent_chain`. -/

/-- The inputs of the first `n + 1` calls of one chain under `H`, in call order. -/
def chainRows (H : Compression) (h : Chained.Height) (seed : Chained.Seed) : Nat → List Late.Block
  | 0 => [Chained.pack (.inl (Chained.workClass h, seed))]
  | j+1 => chainRows H h seed j ++
      ([Chained.encodeNext (Chained.workClass h) (j+1) (Chained.Binary.continueM (M := Id) H h j seed)] :
        List Late.Block)

theorem chain_rows_length (H : Compression) (h : Chained.Height) (seed : Chained.Seed) (n : Nat) :
    (chainRows H h seed n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ j ih =>
    have split : (chainRows H h seed (j+1)).length = (chainRows H h seed j).length + 1 :=
      List.length_append
    rw [split, ih]

/-- A table that agrees with `H` on the inputs of a chain under `H` computes the same chain. -/
theorem chain_congr (H H' : Compression) (h : Chained.Height) (seed : Chained.Seed) (n : Nat)
    (same : ∀ x ∈ chainRows H h seed n, H' x = H x) :
    Chained.Binary.continueM (M := Id) H' h n seed = Chained.Binary.continueM (M := Id) H h n seed := by
  induction n with
  | zero => exact same _ (List.mem_singleton_self _)
  | succ j ih =>
    have before := ih (fun x member => same x (List.mem_append_left _ member))
    change H' (Chained.encodeNext (Chained.workClass h) (j+1) (Chained.Binary.continueM (M := Id) H' h j seed)) =
      H (Chained.encodeNext (Chained.workClass h) (j+1) (Chained.Binary.continueM (M := Id) H h j seed))
    rw [before]
    exact same _ (List.mem_append_right _ (List.mem_singleton_self _))

/-- The inputs of the calls that compute parent `j` at height `d` under `H`:
one row at the ternary bottom, a whole chain above it. -/
def pairRows (H : Compression) (h : Chained.Height) (l r : Late.Digest) :=
  chainRows H h (r++l) (Chained.calls h-1)

private theorem pairCongr (H H' : Compression) (h : Chained.Height) (l r : Late.Digest)
    (same : ∀ x∈pairRows H h l r,H' x=H x) :
    Chained.Binary.parentM (M:=Id) H' h l r=Chained.Binary.parentM (M:=Id) H h l r :=
  congrArg (Chained.storeReply h) (chain_congr H H' h (r++l) (Chained.calls h-1) same)

def layerRows (H : Compression) (h : Chained.Height) : List Late.Digest → List Late.Block
  | l::r::tail=>pairRows H h l r++layerRows H h tail
  | _=>[]

private theorem layerLength (H : Compression) (h : Chained.Height) : ∀ xs : List Late.Digest,
    (parents H h xs).length=xs.length/2
  | []=>rfl
  | [v]=>by simp [parents,Chained.Binary.parentsM] <;> rfl
  | l::r::tail=>by
    change (Chained.Binary.parentM (M:=Id) H h l r::parents H h tail).length=_
    simp only [List.length_cons,layerLength H h tail];omega

private theorem layerCount (H : Compression) (h : Chained.Height) : ∀ xs : List Late.Digest,
    (layerRows H h xs).length=xs.length/2*Chained.calls h
  | []=>by simp [layerRows]
  | [_]=>by simp [layerRows]
  | l::r::tail=>by
    rw [layerRows,List.length_append,pairRows,chain_rows_length,layerCount H h tail]
    rw [List.length_cons,List.length_cons,show (tail.length+1+1)/2=tail.length/2+1 by omega,Nat.add_mul]
    have:=Chained.calls_positive h;omega

private theorem layerCongr (H H' : Compression) (h : Chained.Height) : ∀ xs : List Late.Digest,
    (∀ x∈layerRows H h xs,H' x=H x) → parents H' h xs=parents H h xs
  | [],_=>rfl
  | [_],_=>rfl
  | l::r::tail,same=>by
    change Chained.Binary.parentM (M:=Id) H' h l r::parents H' h tail=Chained.Binary.parentM (M:=Id) H h l r::parents H h tail
    exact congrArg₂ List.cons (pairCongr H H' h l r (fun x m=>same x (List.mem_append_left _ m)))
      (layerCongr H H' h tail (fun x m=>same x (List.mem_append_right _ m)))

def rowsRead (H : Compression) : Nat → List Late.Digest → List Late.Block
  | 0,_=>[]
  | d+1,xs=>layerRows H (Chained.Binary.height (23-d)) xs ++ rowsRead H d (parents H (Chained.Binary.height (23-d)) xs)
theorem rows_read_length (H : Compression) (d : Nat) (xs : List Late.Digest) :
    (rowsRead H d xs).length=towerCost d xs.length := by
  induction d generalizing xs with
  | zero=>rfl
  | succ d ih=>rw [rowsRead,List.length_append,layerCount,ih,layerLength];rfl

theorem levels_congr (H H' : Compression) (d : Nat) (xs : List Late.Digest)
    (same : ∀ x∈rowsRead H d xs,H' x=H x) : levels H' d xs=levels H d xs := by
  induction d generalizing xs with
  | zero=>rfl
  | succ d ih=>
    let h:=Chained.Binary.height (23-d)
    have here:=layerCongr H H' h xs (fun x m=>same x (List.mem_append_left _ m))
    have rest:=ih (parents H h xs) (fun x m=>same x (List.mem_append_right _ m))
    change xs::levels H' d (parents H' h xs)=xs::levels H d (parents H h xs)
    rw [here,rest]

end CommitGolfCandidate.PtrHiding
