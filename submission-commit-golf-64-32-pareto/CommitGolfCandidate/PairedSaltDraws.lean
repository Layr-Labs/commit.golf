import CommitGolfCandidate.TwoPermutationHidingBridge
import CommitGolfCandidate.CountingCoins

/-! # One RANDOM draw per pair is a uniform salt tape

The paired commit draws 32 bytes for each pair of leaves, inside its leaf loop. The first 16 bytes
are the salt of the even leaf and the last 16 the salt of the odd leaf. `TranscriptRefinesView`
asks for one uniform `CompleteSaltTape`. This module is the step between the two, in the place of
`packed_salt_tape_uniform` for the bulk draw:

* `paired_salt_draws_uniform`: `LENGTH / 2` sequential draws of 256 bits, read as a tape by
  `pairedSaltTape`, are one draw of `sampleCompleteSaltTape`, before any continuation;
* `paired_salt_draws_run`: the same under `fixedOracleRun`, for draws lifted into `World`;
* `lift_pair_draws`, `map_tiles_flatten`, `fold_draws`: the bookkeeping that brings the draws of a
  tiled loop into the form `xs.mapM fun _ => $ᵗ PairWord`.

With the oracle fixed, calls between the draws are deterministic, so the draws of all tiles are
already consecutive in the run and nothing has to be commuted.

Ported from `LateCoins` of our 96-32 tree (384-bit draws, 192-bit salts). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate

set_option autoImplicit false

local instance pairedDrawsDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

noncomputable local instance pairedDrawsFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

/-- The 32 bytes of one RANDOM draw, little-endian. -/
abbrev PairWord := BitVec 256

abbrev PairIndex := Fin (LENGTH / 2)

/-- The salt of the even leaf is the first 16 bytes of the pair's draw, that of the odd leaf the
last 16. -/
def pairSalt (word : PairWord) (odd : Bool) : BitVec 128 :=
  word.extractLsb' (if odd then 128 else 0) 128

def unpackPairs (words : PairIndex → PairWord) : CompleteSaltTape := fun i =>
  pairSalt (words ⟨i.val / 2, by
    have bound := i.isLt
    change i.val < 16777216 at bound
    change i.val / 2 < 8388608
    omega⟩) (i.val.testBit 0)

def packPairs (salts : CompleteSaltTape) (p : PairIndex) : PairWord :=
  let bound := p.isLt
  salts ⟨2 * p.val + 1, by change p.val < 8388608 at bound; change _ < 16777216; omega⟩ ++
  salts ⟨2 * p.val, by change p.val < 8388608 at bound; change _ < 16777216; omega⟩

theorem unpack_pack_pairs (salts : CompleteSaltTape) : unpackPairs (packPairs salts) = salts := by
  funext i
  unfold unpackPairs packPairs pairSalt
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
  split
  · rw [BitVec.extractLsb'_append_eq_left]
    congr 1
    apply Fin.ext
    simp_all
    omega
  · rw [BitVec.extractLsb'_append_eq_right]
    congr 1
    apply Fin.ext
    simp_all
    omega

theorem pack_unpack_pairs (words : PairIndex → PairWord) : packPairs (unpackPairs words) = words := by
  funext p
  unfold packPairs unpackPairs pairSalt
  have odd : (2 * p.val + 1).testBit 0 = true := by
    simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]; simp
  have even : (2 * p.val).testBit 0 = false := by
    simp [Nat.testBit_eq_decide_div_mod_eq]
  simp only [odd, even, Bool.false_eq_true, if_false, if_true]
  have a : (2 * p.val + 1) / 2 = p.val := by omega
  have b : 2 * p.val / 2 = p.val := by omega
  simp only [a, b, Fin.eta]
  exact BitVec.extractLsb'_append_extractLsb'

theorem unpack_pairs_bijective : Function.Bijective unpackPairs :=
  ⟨Function.LeftInverse.injective pack_unpack_pairs, Function.RightInverse.surjective unpack_pack_pairs⟩

/-- A uniform table of pair words is a uniform salt tape. -/
theorem unpack_pairs_uniform {α : Type} (next : CompleteSaltTape → ProbComp α) :
    (($ᵗ (PairIndex → PairWord)) >>= fun words => next (unpackPairs words)) =ᵈ
      (sampleCompleteSaltTape >>= next) := by
  rw [← bind_map_left]
  have transport := @SampleableType.map_uniformSample_evalDistEq_of_bijective
    (PairIndex → PairWord) CompleteSaltTape inferInstance completeSaltSampler unpackPairs
    unpack_pairs_bijective
  exact transport.bind_left next

/-- Independent draws in sequence are a uniform table. -/
theorem iid_pair_words {ι α : Type} (xs : List ι) (count : Nat) (length : xs.length = count)
    (next : List PairWord → ProbComp α) :
    (($ᵗ (Fin count → PairWord)) >>= fun table => next (List.ofFn table)) =ᵈ
      (xs.mapM (fun _ => ($ᵗ PairWord : ProbComp PairWord)) >>= next) := by
  subst count
  induction xs generalizing next with
  | nil =>
    simp only [List.length_nil, List.ofFn_zero, List.mapM_nil, pure_bind]
    exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)
  | cons head tail ih =>
    let vec := Fin.consEquiv (fun _ : Fin (tail.length + 1) => PairWord)
    apply (uniform_transport_bind (transportOfEquiv vec.symm)
      (fun table => next (List.ofFn table))).trans
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    apply EvalDistEq.bind_right
    intro first
    change (do let table ← $ᵗ (Fin tail.length → PairWord)
               next (List.ofFn (Fin.cons first table))) =ᵈ _
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    exact ih (fun tape => next (first :: tape))

/-- The salt tape read from the pair words in draw order. -/
def pairedSaltTape (words : List PairWord) : CompleteSaltTape := fun i =>
  pairSalt (words[i.val / 2]?.getD 0) (i.val.testBit 0)

theorem paired_tape_of_fn (table : PairIndex → PairWord) :
    pairedSaltTape (List.ofFn table) = unpackPairs table := by
  funext i
  have bound : i.val / 2 < LENGTH / 2 := by
    have h := i.isLt
    change i.val < 16777216 at h
    change i.val / 2 < 8388608
    omega
  simp only [pairedSaltTape, unpackPairs, List.getElem?_ofFn, dif_pos bound, Option.getD_some]

/-- **One draw per pair is a uniform salt tape.** The paired counterpart of
`packed_salt_tape_uniform`. -/
theorem paired_salt_draws_uniform {ι α : Type} (xs : List ι) (length : xs.length = LENGTH / 2)
    (next : CompleteSaltTape → ProbComp α) :
    (xs.mapM (fun _ => ($ᵗ PairWord : ProbComp PairWord)) >>= fun words =>
        next (pairedSaltTape words)) =ᵈ
      (sampleCompleteSaltTape >>= next) := by
  refine (iid_pair_words xs (LENGTH / 2) length (fun words => next (pairedSaltTape words))).symm.trans ?_
  simp only [paired_tape_of_fn]
  exact unpack_pairs_uniform next

/-! ### Draws inside a program -/

/-- A run of lifted coins followed by a continuation, with the oracle fixed. -/
theorem fixed_oracle_run_coins_bind (oracle : Oracle) {α β : Type} (coins : ProbComp α)
    (next : α → OracleComp World β) :
    fixedOracleRun oracle ((liftM coins : OracleComp World α) >>= next) =
      (coins >>= fun value => fixedOracleRun oracle (next value)) := by
  unfold fixedOracleRun
  rw [oracle_run_coins_bind, map_bind]

/-- Lifted draws in sequence are the lift of the sequence. -/
theorem lift_pair_draws {ι : Type} (xs : List ι) :
    xs.mapM (fun _ => (liftM ($ᵗ PairWord : ProbComp PairWord) : OracleComp World PairWord)) =
      (liftM (xs.mapM (fun _ => ($ᵗ PairWord : ProbComp PairWord))) : OracleComp World (List PairWord)) := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mapM_cons, liftM_bind, liftM_pure]
    rw [ih]

/-- **The per-pair draws of a program are a uniform salt tape**, under every fixed oracle and
before every continuation. -/
theorem paired_salt_draws_run {ι α : Type} (oracle : Oracle) (xs : List ι)
    (length : xs.length = LENGTH / 2) (next : CompleteSaltTape → OracleComp World α) :
    fixedOracleRun oracle
        ((liftM (xs.mapM (fun _ => ($ᵗ PairWord : ProbComp PairWord))) : OracleComp World (List PairWord)) >>=
          fun words => next (pairedSaltTape words)) =ᵈ
      (sampleCompleteSaltTape >>= fun salts => fixedOracleRun oracle (next salts)) := by
  rw [fixed_oracle_run_coins_bind]
  exact paired_salt_draws_uniform xs length (fun salts => fixedOracleRun oracle (next salts))

/-- The draws of consecutive tiles are one list of draws. -/
theorem map_tiles_flatten {m : Type → Type} [Monad m] [LawfulMonad m] {ι κ ω : Type}
    (tiles : List ι) (inner : List κ) (draw : m ω) :
    (tiles.mapM (fun _ => inner.mapM (fun _ => draw)) >>= fun rows => pure rows.flatten) =
      (tiles.flatMap (fun _ => inner)).mapM (fun _ => draw) := by
  induction tiles with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mapM_cons, List.flatMap_cons, List.mapM_append, bind_assoc, pure_bind,
      List.flatten_cons]
    refine bind_congr fun first => ?_
    rw [← ih]
    simp only [bind_assoc, pure_bind]

/-- A loop that draws once per step and updates a state is the draws followed by the fold. -/
theorem fold_draws {m : Type → Type} [Monad m] [LawfulMonad m] {ι σ ω : Type}
    (draw : m ω) (step : σ → ω → σ) (xs : List ι) (start : σ) :
    xs.foldlM (fun state _ => draw >>= fun word => pure (step state word)) start =
      (xs.mapM (fun _ => draw) >>= fun words => pure (words.foldl step start)) := by
  induction xs generalizing start with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldlM_cons, List.mapM_cons, bind_assoc, pure_bind, List.foldl_cons]
    refine bind_congr fun word => ?_
    rw [ih]

end TwoPermutationPrototype.Sampling
