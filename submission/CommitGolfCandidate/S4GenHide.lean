import CommitGolfCandidate.S4PermGen
import CommitGolfCandidate.S3PermBridge
import CommitGolfCandidate.S4Gen

/-! Contract-level form of the counter-mode nonce generator. The commitment draws a 32-byte seed
and makes `S4_GEN_BLOCKS` forward permutation queries; leaf `i` takes 16 bytes of the reply to
block `i / 11`. Against an adversary whose first stage runs before the seed is drawn and whose
second stage sees the nonce vector, the generated vector is as good as a uniform one up to
`S5_GEN_LOSS`.

The proof moves each event probability to the lazy permutation model (`perm_sampling_prob`) and
applies `GenCall.gen_bound` with seed `BitVec 256`, counters `Fin S4_GEN_BLOCKS` and revealed part
`BitVec 1408` (reply bytes 24..200; every part has `2^192` preimages). The ideal side's
`S4_GEN_BLOCKS` independent uniform parts carry `11 * S4_GEN_BLOCKS = 2^24 + 6` fields of 16 bytes:
the first `2^24` are a uniform nonce vector and the last six are discarded. -/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance s4GenHideDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec
open CommitGolfCandidate.Permutation
open Finset

/-! ### Fixed-oracle runs and total variation -/

theorem s4_run_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (next : α → OracleComp World β) :
    fixedOracleRun oracle (computation >>= next) =
      (fixedOracleRun oracle computation >>= fun value => fixedOracleRun oracle (next value)) := by
  simp only [fixedOracleRun, oracle_run_bind, map_bind, map_pure, bind_map_left]
  simp only [map_eq_bind_pure_comp]
  apply bind_congr
  intro first
  cases first
  apply bind_congr
  intro second
  cases second
  rfl

private theorem s4_le_add_ofReal_of_toReal {a b : ENNReal} {ε : ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hε : 0 ≤ ε) (h : a.toReal ≤ b.toReal + ε) : a ≤ b + ENNReal.ofReal ε := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ ENNReal.ofReal (b.toReal + ε) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal b.toReal + ENNReal.ofReal ε := ENNReal.ofReal_add ENNReal.toReal_nonneg hε
    _ = b + ENNReal.ofReal ε := by rw [ENNReal.ofReal_toReal hb]

/-- Total variation is the largest event discrepancy. -/
theorem s4_tv_le_of_events {α : Type} (mx my : ProbComp α) (ε : ℝ) (nonneg : 0 ≤ ε)
    (close : ∀ event : α → Prop,
      |(prEvent (event <$> mx)).toReal - (prEvent (event <$> my)).toReal| ≤ ε) :
    measureTVDist mx my ≤ ε := by
  rw [measureTVDist_eq_toReal_measureETVDist]
  apply ENNReal.toReal_le_of_le_ofReal nonneg
  rw [measureETVDist, MeasureTheory.Measure.etvDist]
  refine iSup_le fun set => ?_
  have left := prEvent_eq_evalDist_of_discrete mx (fun value => value ∈ set.1)
  have right := prEvent_eq_evalDist_of_discrete my (fun value => value ∈ set.1)
  simp only [Set.ofPred_mem_eq] at left right
  have bound := abs_sub_le_iff.mp (close (fun value => value ∈ set.1))
  rw [← left, ← right, ENNReal.absDiff_le_iff]
  exact ⟨s4_le_add_ofReal_of_toReal (prEvent_ne_top _) (prEvent_ne_top _) nonneg
      (by linarith [bound.1]),
    s4_le_add_ofReal_of_toReal (prEvent_ne_top _) (prEvent_ne_top _) nonneg (by linarith [bound.2])⟩

/-- Expectation commutes with a finite average of the payoff. -/
theorem s4_exp_avg {σ κ : Type} (I : Finset κ) (F : κ → σ → PState PermState → ℝ)
    (st : Strat PermState σ) (s : PState PermState) :
    st.exp s (fun a s' => avg I fun j => F j a s') = avg I fun j => st.exp s (F j) := by
  induction st generalizing s with
  | done a => rfl
  | fwd x k ih =>
    simp only [Strat.exp, ih]
    exact avg_comm _ _ _
  | inv y k ih =>
    simp only [Strat.exp, ih]
    exact avg_comm _ _ _
  | rand n k ih =>
    simp only [Strat.exp, ih]
    exact avg_comm _ _ _

/-! ### The generator as an oracle computation -/

/-- The revealed part of a generator reply: bytes 24..200. -/
def s4GenOut (s : PermState) : BitVec 1408 := BitVec.ofNat 1408 (s.toNat / 2 ^ 192)

/-- Query the blocks of the counters in order and return their revealed parts. -/
def s4GenParts (seed : BitVec 256) : List (Fin S4_GEN_BLOCKS) → OracleComp World (List (BitVec 1408))
  | [] => pure []
  | k :: ks =>
    (liftM (World.query (.inr (.inr (.inl (s4GenInput seed k.val))))) : OracleComp World _) >>=
      fun reply => s4GenParts seed ks >>= fun parts => pure (s4GenOut reply :: parts)

theorem s4_gen_parts_nil (seed : BitVec 256) : s4GenParts seed [] = pure [] := rfl

theorem s4_gen_parts_cons (seed : BitVec 256) (k : Fin S4_GEN_BLOCKS) (ks : List (Fin S4_GEN_BLOCKS)) :
    s4GenParts seed (k :: ks) =
      ((liftM (World.query (.inr (.inr (.inl (s4GenInput seed k.val))))) : OracleComp World _) >>=
        fun reply => s4GenParts seed ks >>= fun parts => pure (s4GenOut reply :: parts)) := rfl

-- Only the two equations above are used; unfolding the definition on a concrete list of
-- 1,525,202 counters would recurse through the whole list.
attribute [irreducible] s4GenParts

/-- The nonce vector read off the revealed parts: nonce `i` is field `i % 11` of part `i / 11`. -/
def s4SaltOfParts (parts : List (BitVec 1408)) (index : Index) : Nonce128 :=
  BitVec.ofNat 128 ((parts.getD (index.val / 11) 0).toNat / 2 ^ (128 * (index.val % 11)))

/-- The generated nonce vector as a function of a fixed permutation. -/
def s4GenSalt (permutation : Perm) (seed : BitVec 256) : Index → Nonce128 := s4GenNonce permutation seed

/-- The same vector through 1,525,202 forward queries. -/
def s4GenQuery (seed : BitVec 256) : OracleComp World (Index → Nonce128) :=
  s4GenParts seed (List.finRange S4_GEN_BLOCKS) >>= fun parts => pure (s4SaltOfParts parts)

theorem s4_card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem s4_getD_of_lt {β : Type} (l : List β) (d : β) {n : ℕ} (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem s4_pure_bound {β : Type} (value : β) :
    PublicQueryBound (pure value : OracleComp World β) 0 := trivial

theorem s4_gen_out_toNat (s : PermState) : (s4GenOut s).toNat = s.toNat / 2 ^ 192 := by
  have bound : s.toNat < 2 ^ 1600 := s.isLt
  unfold s4GenOut
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

theorem fixed_s4_gen_parts (oracle : Oracle) (seed : BitVec 256) :
    ∀ ks : List (Fin S4_GEN_BLOCKS), fixedOracleRun oracle (s4GenParts seed ks) =
      pure (ks.map fun k => s4GenOut (oracle.permutation (s4GenInput seed k.val)))
  | [] => by
    rw [s4_gen_parts_nil, List.map_nil]
    exact fixed_oracle_run_pure oracle []
  | k :: ks => by
    rw [s4_gen_parts_cons]
    rw [fixed_oracle_run_public oracle (.inr (.inl (s4GenInput seed k.val))), s4_run_bind,
      fixed_s4_gen_parts oracle seed ks, pure_bind, fixed_oracle_run_pure]
    rfl

theorem s4_salt_of_parts_map (permutation : Perm) (seed : BitVec 256) (index : Index) :
    s4SaltOfParts ((List.finRange S4_GEN_BLOCKS).map fun k =>
        s4GenOut (permutation (s4GenInput seed k.val))) index =
      s4GenNonce permutation seed index := by
  have small : index.val / 11 < S4_GEN_BLOCKS := by
    have bound : index.val < 16777216 := index.isLt
    have blocks : S4_GEN_BLOCKS = 1525202 := rfl
    omega
  unfold s4SaltOfParts s4GenNonce
  rw [s4_getD_of_lt _ _ (by simpa using small), List.getElem_map, List.getElem_finRange,
    s4_gen_out_toNat, Nat.div_div_eq_div_mul, ← pow_add]
  rfl

theorem fixed_s4_gen_query (oracle : Oracle) (seed : BitVec 256) :
    fixedOracleRun oracle (s4GenQuery seed) = pure (s4GenSalt oracle.permutation seed) := by
  unfold s4GenQuery
  have salt : s4SaltOfParts ((List.finRange S4_GEN_BLOCKS).map fun k =>
        s4GenOut (oracle.permutation (s4GenInput seed k.val))) =
      s4GenSalt oracle.permutation seed :=
    funext fun index => s4_salt_of_parts_map oracle.permutation seed index
  rw [s4_run_bind, fixed_s4_gen_parts, pure_bind, fixed_oracle_run_pure, salt]

theorem s4_gen_parts_bound (seed : BitVec 256) :
    ∀ ks : List (Fin S4_GEN_BLOCKS), PublicQueryBound (s4GenParts seed ks) ks.length
  | [] => by
    rw [s4_gen_parts_nil]
    exact s4_pure_bound []
  | k :: ks => by
    rw [s4_gen_parts_cons]
    change 1 ≤ (k :: ks).length ∧ ∀ reply : BitVec PERMUTATION_WIDTH, PublicQueryBound
      (s4GenParts seed ks >>= fun parts => pure (s4GenOut reply :: parts)) ((k :: ks).length - 1)
    refine ⟨by simp, fun reply => ?_⟩
    have bound := public_query_bound_bind (s4_gen_parts_bound seed ks)
      (fun parts => s4_pure_bound (s4GenOut reply :: parts))
    exact bound.mono (by simp)

/-- The query bound for any list of counters (the list stays symbolic). -/
theorem s4_gen_salt_bound (seed : BitVec 256) (ks : List (Fin S4_GEN_BLOCKS)) :
    PublicQueryBound (s4GenParts seed ks >>= fun parts =>
      (pure (s4SaltOfParts parts) : OracleComp World (Index → Nonce128))) ks.length :=
  public_query_bound_bind (s4_gen_parts_bound seed ks) (fun parts => s4_pure_bound (s4SaltOfParts parts))

theorem s4_gen_salt_bound_of (seed : BitVec 256) (ks : List (Fin S4_GEN_BLOCKS)) (n : ℕ)
    (hn : ks.length = n) :
    PublicQueryBound (s4GenParts seed ks >>= fun parts =>
      (pure (s4SaltOfParts parts) : OracleComp World (Index → Nonce128))) n := by
  subst hn
  exact s4_gen_salt_bound seed ks

theorem s4_gen_query_bound (seed : BitVec 256) : PublicQueryBound (s4GenQuery seed) S4_GEN_BLOCKS :=
  s4_gen_salt_bound_of seed (List.finRange S4_GEN_BLOCKS) S4_GEN_BLOCKS List.length_finRange

/-! ### The generator in the lazy model -/

theorem s4_gen_counter_lt (k : Fin S4_GEN_BLOCKS) : 6106910984 + 176 * k.val < 2 ^ 1344 := by
  have hk : k.val < 1525202 := k.isLt
  have small : 6106910984 + 176 * k.val < 2 ^ 33 := by omega
  exact lt_of_lt_of_le small (Nat.pow_le_pow_right (by norm_num) (by norm_num))

theorem s4_gen_input_lt (r : BitVec 256) (k : Fin S4_GEN_BLOCKS) :
    6106910984 + 176 * k.val + r.toNat * 2 ^ 1344 < 2 ^ 1600 := by
  have hr : r.toNat + 1 ≤ 2 ^ 256 := r.isLt
  have hk := s4_gen_counter_lt k
  calc 6106910984 + 176 * k.val + r.toNat * 2 ^ 1344 < 2 ^ 1344 + r.toNat * 2 ^ 1344 := by omega
    _ = (r.toNat + 1) * 2 ^ 1344 := by ring
    _ ≤ 2 ^ 256 * 2 ^ 1344 := Nat.mul_le_mul_right _ hr
    _ = 2 ^ 1600 := by rw [← pow_add]

theorem s4_gen_input_toNat (r : BitVec 256) (k : Fin S4_GEN_BLOCKS) :
    (s4GenInput r k.val).toNat = 6106910984 + 176 * k.val + r.toNat * 2 ^ 1344 := by
  unfold s4GenInput
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (s4_gen_input_lt r k)

theorem s4_gen_input_injective :
    Function.Injective fun p : BitVec 256 × Fin S4_GEN_BLOCKS => s4GenInput p.1 p.2.val := by
  rintro ⟨r, k⟩ ⟨r', k'⟩ h
  have h' : 6106910984 + 176 * k.val + r.toNat * 2 ^ 1344 =
      6106910984 + 176 * k'.val + r'.toNat * 2 ^ 1344 := by
    rw [← s4_gen_input_toNat, ← s4_gen_input_toNat]
    exact congrArg BitVec.toNat h
  have low := congrArg (· % 2 ^ 1344) h'
  have high := congrArg (· / 2 ^ 1344) h'
  simp only [Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 1344),
    Nat.mod_eq_of_lt (s4_gen_counter_lt k), Nat.mod_eq_of_lt (s4_gen_counter_lt k'),
    Nat.div_eq_of_lt (s4_gen_counter_lt k), Nat.div_eq_of_lt (s4_gen_counter_lt k'),
    zero_add] at low high
  have scaled : 176 * k.val = 176 * k'.val := Nat.add_left_cancel low
  have e2 : k.val = k'.val := Nat.eq_of_mul_eq_mul_left (by norm_num) scaled
  rw [BitVec.eq_of_toNat_eq high, Fin.ext e2]

/-- The generator of the commitment: seed `BitVec 256`, counter `Fin S4_GEN_BLOCKS`, revealed
part bytes 24..200 of the reply. -/
def s4GenCallModel : GenCall PermState (BitVec 256) (Fin S4_GEN_BLOCKS) (BitVec 1408) where
  enc p := s4GenInput p.1 p.2.val
  enc_inj := s4_gen_input_injective
  out := s4GenOut

theorem s4_gen_out_fiber (n : BitVec 1408) :
    (univ.filter fun s : PermState => s4GenOut s = n).card ≤ 2 ^ 192 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : PermState => s4GenOut s = n)
    (t := (univ : Finset (BitVec 192))) (fun s => BitVec.ofNat 192 s.toNat)
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s4GenOut, BitVec.toNat_ofNat] at e1 e2
      have hA : a.toNat < 2 ^ 1600 := a.isLt
      have hB : b.toNat < 2 ^ 1600 := b.isLt
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s4_card_bitvec] at h

/-- Every revealed part has exactly `2^192` preimages among the 1600-bit states. -/
theorem s4_gen_out_regular (n : BitVec 1408) :
    (univ.filter fun s : PermState => s4GenCallModel.out s = n).card = 2 ^ 192 := by
  change (univ.filter fun s : PermState => s4GenOut s = n).card = 2 ^ 192
  by_contra h
  have hlt : (univ.filter fun s : PermState => s4GenOut s = n).card < 2 ^ 192 :=
    lt_of_le_of_ne (s4_gen_out_fiber n) h
  have hsum : (univ : Finset PermState).card =
      ∑ b ∈ (univ : Finset (BitVec 1408)), (univ.filter fun s : PermState => s4GenOut s = b).card :=
    Finset.card_eq_sum_card_fiberwise (by intro x _; simp)
  have hlt2 : ∑ b ∈ (univ : Finset (BitVec 1408)),
        (univ.filter fun s : PermState => s4GenOut s = b).card <
      ∑ _b ∈ (univ : Finset (BitVec 1408)), 2 ^ 192 :=
    Finset.sum_lt_sum (fun b _ => s4_gen_out_fiber b) ⟨n, Finset.mem_univ _, hlt⟩
  rw [← hsum, Finset.card_univ, s4_card_bitvec, Finset.sum_const, Finset.card_univ,
    s4_card_bitvec, smul_eq_mul, ← pow_add] at hlt2
  exact absurd hlt2 (lt_irrefl _)

theorem to_strat_s4_gen_parts (compression : Compression) (seed : BitVec 256) :
    ∀ ks : List (Fin S4_GEN_BLOCKS), toStrat compression (s4GenParts seed ks) = s4GenCallModel.blocks seed ks
  | [] => by
    rw [s4_gen_parts_nil, to_strat_pure]
    rfl
  | k :: ks => by
    rw [s4_gen_parts_cons]
    simp only [GenCall.blocks]
    rw [to_strat_permute]
    simp only [to_strat_bind, to_strat_s4_gen_parts compression seed ks, to_strat_pure]
    rfl

theorem to_strat_s4_gen_query (compression : Compression) (seed : BitVec 256) :
    toStrat compression (s4GenQuery seed) =
      (s4GenCallModel.blocks seed (List.finRange S4_GEN_BLOCKS)).bind fun parts =>
        Strat.done (s4SaltOfParts parts) := by
  unfold s4GenQuery
  simp only [to_strat_bind, to_strat_s4_gen_parts, to_strat_pure]

/-! ### The ideal parts are a uniform nonce vector -/

/-- If two numbers below `2^1408` agree on all eleven 128-bit fields, they are equal. -/
theorem s4_fields_eq {a b : ℕ} (ha : a < 2 ^ 1408) (hb : b < 2 ^ 1408)
    (h : ∀ j < 11, a / 2 ^ (128 * j) % 2 ^ 128 = b / 2 ^ (128 * j) % 2 ^ 128) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 1408
  · have hj : i / 128 < 11 := by omega
    have key := congrArg (fun x => Nat.testBit x (i % 128)) (h (i / 128) hj)
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at key
    have hq : i % 128 < 128 := Nat.mod_lt _ (by norm_num)
    have hi' : i % 128 + 128 * (i / 128) = i := by omega
    simpa [hq, hi'] using key
  · have hle : 2 ^ 1408 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

theorem s4_salt_of_parts_ofFn (v : Fin S4_GEN_BLOCKS → BitVec 1408) (index : Index)
    (block : Fin S4_GEN_BLOCKS) (j : ℕ) (position : index.val = 11 * block.val + j) (hj : j < 11) :
    s4SaltOfParts (List.ofFn v) index = BitVec.ofNat 128 ((v block).toNat / 2 ^ (128 * j)) := by
  have h1 : index.val / 11 = block.val := by omega
  have h2 : index.val % 11 = j := by omega
  unfold s4SaltOfParts
  rw [h1, h2, s4_getD_of_lt _ _ (by simp), List.getElem_ofFn]

/-- The last block. -/
def s4GenLast : Fin S4_GEN_BLOCKS := ⟨S4_GEN_BLOCKS - 1, by unfold S4_GEN_BLOCKS; omega⟩

/-- The six fields of the last block that hold no nonce (fields 5..10). -/
def s4GenExtra (v : Fin S4_GEN_BLOCKS → BitVec 1408) (j : Fin 6) : Nonce128 :=
  BitVec.ofNat 128 ((v s4GenLast).toNat / 2 ^ (128 * (j.val + 5)))

/-- The parts as the nonce vector and the six spare fields. -/
def s4GenSplit (v : Fin S4_GEN_BLOCKS → BitVec 1408) : (Index → Nonce128) × (Fin 6 → Nonce128) :=
  (s4SaltOfParts (List.ofFn v), s4GenExtra v)

theorem s4_gen_split_injective : Function.Injective s4GenSplit := by
  intro v w h
  have hs : s4SaltOfParts (List.ofFn v) = s4SaltOfParts (List.ofFn w) := congrArg Prod.fst h
  have he : s4GenExtra v = s4GenExtra w := congrArg Prod.snd h
  have length : LENGTH = 16777216 := rfl
  have field : ∀ x y : ℕ, BitVec.ofNat 128 x = BitVec.ofNat 128 y → x % 2 ^ 128 = y % 2 ^ 128 := by
    intro x y hxy
    simpa only [BitVec.toNat_ofNat] using congrArg BitVec.toNat hxy
  funext block
  apply BitVec.eq_of_toNat_eq
  apply s4_fields_eq (v block).isLt (w block).isLt
  intro j hj
  by_cases inside : 11 * block.val + j < LENGTH
  · have e := congrFun hs ⟨11 * block.val + j, inside⟩
    rw [s4_salt_of_parts_ofFn v _ block j rfl hj, s4_salt_of_parts_ofFn w _ block j rfl hj] at e
    exact field _ _ e
  · rw [length] at inside
    have hb : block.val < 1525202 := block.isLt
    have last : block = s4GenLast := by
      apply Fin.ext
      show block.val = S4_GEN_BLOCKS - 1
      have top : S4_GEN_BLOCKS - 1 = 1525201 := rfl
      rw [top]
      omega
    subst last
    have hj5 : j - 5 + 5 = j := by omega
    have e : BitVec.ofNat 128 ((v s4GenLast).toNat / 2 ^ (128 * (j - 5 + 5))) =
        BitVec.ofNat 128 ((w s4GenLast).toNat / 2 ^ (128 * (j - 5 + 5))) :=
      congrFun he ⟨j - 5, by omega⟩
    rw [hj5] at e
    exact field _ _ e

/-- Card identity with symbolic sizes (the concrete powers are never formed). -/
theorem s4_split_card_of (a b : ℕ) (h : 11 * a = b + 6) :
    Fintype.card (Fin a → BitVec 1408) =
      Fintype.card ((Fin b → BitVec 128) × (Fin 6 → BitVec 128)) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin, s4_card_bitvec, s4_card_bitvec, ← pow_add, ← h,
    show (1408 : ℕ) = 128 * 11 by norm_num, pow_mul, pow_mul]

theorem s4_gen_blocks_fields : 11 * S4_GEN_BLOCKS = LENGTH + 6 := by
  unfold S4_GEN_BLOCKS LENGTH LOG_LENGTH
  norm_num

theorem s4_gen_split_card :
    Fintype.card (Fin S4_GEN_BLOCKS → BitVec 1408) =
      Fintype.card ((Index → Nonce128) × (Fin 6 → Nonce128)) :=
  s4_split_card_of S4_GEN_BLOCKS LENGTH s4_gen_blocks_fields

/-- The parts are the nonce vector and the six spare fields, bijectively. -/
noncomputable def s4GenSplitEquiv :
    (Fin S4_GEN_BLOCKS → BitVec 1408) ≃ (Index → Nonce128) × (Fin 6 → Nonce128) :=
  Equiv.ofBijective s4GenSplit
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨s4_gen_split_injective, s4_gen_split_card⟩)

theorem s4_gen_split_equiv_fst (v : Fin S4_GEN_BLOCKS → BitVec 1408) :
    (s4GenSplitEquiv v).1 = s4SaltOfParts (List.ofFn v) := by
  rw [s4GenSplitEquiv, Equiv.ofBijective_apply]
  rfl

/-- Uniform parts give a uniform nonce vector. -/
theorem s4_avg_parts (g : (Index → Nonce128) → ℝ) :
    avg univ (fun v : Fin S4_GEN_BLOCKS → BitVec 1408 => g (s4SaltOfParts (List.ofFn v))) =
      avg univ g := by
  have first : ∀ v : Fin S4_GEN_BLOCKS → BitVec 1408,
      g (s4SaltOfParts (List.ofFn v)) =
        (fun p : (Index → Nonce128) × (Fin 6 → Nonce128) => g p.1) (s4GenSplitEquiv v) := by
    intro v
    show g (s4SaltOfParts (List.ofFn v)) = g (s4GenSplitEquiv v).1
    rw [s4_gen_split_equiv_fst]
  have spare : ∀ salt : Index → Nonce128,
      avg (univ : Finset (Fin 6 → Nonce128)) (fun _ => g salt) = g salt :=
    fun salt => avg_const univ_nonempty (g salt)
  rw [avg_congr fun v _ => first v,
    avg_univ_equiv s4GenSplitEquiv (fun p : (Index → Nonce128) × (Fin 6 → Nonce128) => g p.1),
    avg_univ_prod (fun p : (Index → Nonce128) × (Fin 6 → Nonce128) => g p.1)]
  exact avg_congr fun salt _ => spare salt

/-! ### The two experiments in the lazy model -/

variable {State α : Type}

/-- Real experiment: the continuation receives the generated nonce vector. -/
def s4RealGame (compression : Compression) (first : OracleComp World State)
    (next : State → (Index → Nonce128) → OracleComp World α) : ProbComp α := do
  let permutation ← $ᵗ Perm
  let state ← fixedOracleRun ⟨compression, permutation⟩ first
  let seed ← $ᵗ BitVec 256
  fixedOracleRun ⟨compression, permutation⟩ (next state (s4GenSalt permutation seed))

/-- Ideal experiment: the continuation receives a uniform nonce vector. -/
def s4IdealGame (compression : Compression) (first : OracleComp World State)
    (next : State → (Index → Nonce128) → OracleComp World α) : ProbComp α := do
  let permutation ← $ᵗ Perm
  let state ← fixedOracleRun ⟨compression, permutation⟩ first
  let salt ← $ᵗ (Index → Nonce128)
  fixedOracleRun ⟨compression, permutation⟩ (next state salt)

/-- The real experiment for one seed, as a single oracle computation. -/
def s4RealComp (first : OracleComp World State)
    (next : State → (Index → Nonce128) → OracleComp World α) (seed : BitVec 256) :
    OracleComp World α :=
  first >>= fun state => s4GenQuery seed >>= fun salt => next state salt

/-- The ideal experiment for one nonce vector, as a single oracle computation. -/
def s4IdealComp (first : OracleComp World State)
    (next : State → (Index → Nonce128) → OracleComp World α) (salt : Index → Nonce128) :
    OracleComp World α :=
  first >>= fun state => next state salt

open Classical in
/-- Second stage of the lazy-model game: the continuation on the nonce vector read off the
revealed parts, reporting whether the event holds. -/
noncomputable def s4StratNext (compression : Compression)
    (next : State → (Index → Nonce128) → OracleComp World α) (event : α → Prop)
    (state : State) (parts : List (BitVec 1408)) : Strat PermState Bool :=
  (toStrat compression (next state (s4SaltOfParts parts))).bind fun result =>
    Strat.done (decide (event result))

theorem s4_strat_next_QB (compression : Compression)
    (next : State → (Index → Nonce128) → OracleComp World α) (event : α → Prop) (budget : Nat)
    (bounded : ∀ state salt, PublicQueryBound (next state salt) budget)
    (state : State) (parts : List (BitVec 1408)) :
    (s4StratNext compression next event state parts).QB budget := by
  classical
  have bound := (to_strat_QB compression (bounded state (s4SaltOfParts parts))).bind
    (fun result => Strat.QB.done (decide (event result)) 0)
  exact bound

theorem s4_real_strat_prob (compression : Compression) (first : OracleComp World State)
    (next : State → (Index → Nonce128) → OracleComp World α) (event : α → Prop)
    (seed : BitVec 256) :
    (toStrat compression (s4RealComp first next seed)).prob PState.init
        (fun result _ => event result) =
      ((toStrat compression first).bind fun a =>
        (s4GenCallModel.blocks seed (List.finRange S4_GEN_BLOCKS)).bind
          (s4StratNext compression next event a)).prob PState.init (fun b _ => b = true) := by
  unfold Strat.prob s4RealComp
  simp only [to_strat_bind, to_strat_s4_gen_query, s4StratNext, Strat.exp_bind, Strat.exp,
    decide_eq_true_eq]

theorem s4_ideal_strat_prob (compression : Compression) (first : OracleComp World State)
    (next : State → (Index → Nonce128) → OracleComp World α) (event : α → Prop)
    (parts : List (BitVec 1408)) :
    (toStrat compression (s4IdealComp first next (s4SaltOfParts parts))).prob PState.init
        (fun result _ => event result) =
      ((toStrat compression first).bind fun a =>
        s4StratNext compression next event a parts).prob PState.init (fun b _ => b = true) := by
  unfold Strat.prob s4IdealComp
  simp only [to_strat_bind, s4StratNext, Strat.exp_bind, Strat.exp, decide_eq_true_eq]

theorem s4_gen_real_avg {σ : Type} (ks : List (Fin S4_GEN_BLOCKS)) (A1 : Strat PermState σ)
    (A2 : σ → List (BitVec 1408) → Strat PermState Bool) (E : Bool → PState PermState → Prop) :
    (s4GenCallModel.genReal ks A1 A2).prob PState.init E =
      avg univ fun seed : BitVec 256 =>
        (A1.bind fun a => (s4GenCallModel.blocks seed ks).bind (A2 a)).prob PState.init E := by
  unfold GenCall.genReal Strat.prob
  rw [Strat.exp_bind]
  simp only [Strat.exp_uniform]
  rw [s4_exp_avg]
  refine avg_congr fun seed _ => ?_
  rw [Strat.exp_bind]

theorem s4_gen_ideal_avg {σ : Type} (A1 : Strat PermState σ)
    (A2 : σ → List (BitVec 1408) → Strat PermState Bool) (E : Bool → PState PermState → Prop) :
    (s4GenCallModel.genIdeal S4_GEN_BLOCKS A1 A2).prob PState.init E =
      avg univ fun v : Fin S4_GEN_BLOCKS → BitVec 1408 =>
        (A1.bind fun a => A2 a (List.ofFn v)).prob PState.init E := by
  unfold GenCall.genIdeal Strat.prob
  rw [Strat.exp_bind]
  simp only [Strat.exp_uniform]
  rw [s4_exp_avg]
  refine avg_congr fun v _ => ?_
  rw [Strat.exp_bind]

/-! ### Event probabilities of the two experiments -/

theorem s4_real_game_event (compression : Compression) (first : OracleComp World State)
    (next : State → (Index → Nonce128) → OracleComp World α) (event : α → Prop) :
    prEvent (event <$> s4RealGame compression first next) =
      ENNReal.ofReal ((s4GenCallModel.genReal (List.finRange S4_GEN_BLOCKS) (toStrat compression first)
        (s4StratNext compression next event)).prob PState.init fun b _ => b = true) := by
  have reordered : 𝒟[s4RealGame compression first next] =
      𝒟[do let seed ← $ᵗ (BitVec 256)
           let permutation ← $ᵗ Perm
           fixedOracleRun ⟨compression, permutation⟩ (s4RealComp first next seed)] := by
    have inner : ∀ (seed : BitVec 256) (permutation : Perm),
        fixedOracleRun ⟨compression, permutation⟩ (s4RealComp first next seed) =
          (fixedOracleRun ⟨compression, permutation⟩ first >>= fun state =>
            fixedOracleRun ⟨compression, permutation⟩
              (next state (s4GenSalt permutation seed))) := by
      intro seed permutation
      unfold s4RealComp
      rw [s4_run_bind]
      apply bind_congr
      intro state
      rw [s4_run_bind, fixed_s4_gen_query, pure_bind]
    unfold s4RealGame
    simp only [inner]
    trans 𝒟[do let permutation ← $ᵗ Perm
                let seed ← $ᵗ (BitVec 256)
                let state ← fixedOracleRun ⟨compression, permutation⟩ first
                fixedOracleRun ⟨compression, permutation⟩
                  (next state (s4GenSalt permutation seed))]
    · apply _root_.evalDist_bind_congr
      intro permutation
      exact (distribution_bind_comm ($ᵗ (BitVec 256))
        (fixedOracleRun ⟨compression, permutation⟩ first) _).symm
    · exact distribution_bind_comm ($ᵗ Perm) ($ᵗ (BitVec 256)) _
  rw [(EvalDistEq.of_evalDist_eq reordered).prEvent_eq event]
  rw [prEvent_bind_eq_sum_fintype, s4_gen_real_avg,
    ← sum_inv_card_mul_ofReal _ fun seed => Strat.prob_nonneg _ _ _]
  refine Finset.sum_congr rfl fun seed _ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, perm_sampling_prob, s4_real_strat_prob]

theorem s4_ideal_game_event (compression : Compression) (first : OracleComp World State)
    (next : State → (Index → Nonce128) → OracleComp World α) (event : α → Prop) :
    prEvent (event <$> s4IdealGame compression first next) =
      ENNReal.ofReal ((s4GenCallModel.genIdeal S4_GEN_BLOCKS (toStrat compression first)
        (s4StratNext compression next event)).prob PState.init fun b _ => b = true) := by
  have reordered : 𝒟[s4IdealGame compression first next] =
      𝒟[do let salt ← $ᵗ (Index → Nonce128)
           let permutation ← $ᵗ Perm
           fixedOracleRun ⟨compression, permutation⟩ (s4IdealComp first next salt)] := by
    have inner : ∀ (salt : Index → Nonce128) (permutation : Perm),
        fixedOracleRun ⟨compression, permutation⟩ (s4IdealComp first next salt) =
          (fixedOracleRun ⟨compression, permutation⟩ first >>= fun state =>
            fixedOracleRun ⟨compression, permutation⟩ (next state salt)) := by
      intro salt permutation
      exact s4_run_bind _ _ _
    unfold s4IdealGame
    simp only [inner]
    trans 𝒟[do let permutation ← $ᵗ Perm
                let salt ← $ᵗ (Index → Nonce128)
                let state ← fixedOracleRun ⟨compression, permutation⟩ first
                fixedOracleRun ⟨compression, permutation⟩ (next state salt)]
    · apply _root_.evalDist_bind_congr
      intro permutation
      exact (distribution_bind_comm ($ᵗ (Index → Nonce128))
        (fixedOracleRun ⟨compression, permutation⟩ first) _).symm
    · exact distribution_bind_comm ($ᵗ Perm) ($ᵗ (Index → Nonce128)) _
  have ideal : avg univ (fun v : Fin S4_GEN_BLOCKS → BitVec 1408 =>
        ((toStrat compression first).bind fun a =>
          s4StratNext compression next event a (List.ofFn v)).prob PState.init
            (fun b _ => b = true)) =
      avg univ (fun salt : Index → Nonce128 =>
        (toStrat compression (s4IdealComp first next salt)).prob PState.init
          (fun result _ => event result)) :=
    (avg_congr fun v _ => (s4_ideal_strat_prob compression first next event (List.ofFn v)).symm).trans
      (s4_avg_parts fun salt => (toStrat compression (s4IdealComp first next salt)).prob PState.init
        (fun result _ => event result))
  rw [(EvalDistEq.of_evalDist_eq reordered).prEvent_eq event]
  rw [prEvent_bind_eq_sum_fintype, s4_gen_ideal_avg, ideal,
    ← sum_inv_card_mul_ofReal _ fun salt => Strat.prob_nonneg _ _ _]
  refine Finset.sum_congr rfl fun salt _ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, perm_sampling_prob]

/-! ### The bound -/

/-- Generator loss: `gen_bound` at these sizes is at most `(q1 + q2 + 2^21) / 2^169`. -/
noncomputable def S5_GEN_LOSS (firstBudget nextBudget : Nat) : ℝ :=
  ((firstBudget + nextBudget + 2 ^ 21 : Nat) : ℝ) / 2 ^ 168

theorem s4_gen_loss_arith (q1 q2 : ℕ) :
    2 * ((q1 + S4_GEN_BLOCKS + q2 : ℕ) : ℝ) / (Fintype.card (BitVec 256) : ℝ) +
        4 * ((q1 + S4_GEN_BLOCKS + q2 : ℕ) : ℝ) * (S4_GEN_BLOCKS : ℝ) / ((2 ^ 192 : ℕ) : ℝ) ≤
      S5_GEN_LOSS q1 q2 := by
  unfold S5_GEN_LOSS
  rw [s4_card_bitvec]
  have blocks : S4_GEN_BLOCKS = 1525202 := rfl
  simp only [blocks, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  have h1 : (0 : ℝ) ≤ (q1 : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (q2 : ℝ) := Nat.cast_nonneg _
  have e256 : (2 : ℝ) ^ 256 = 2 ^ 168 * 2 ^ 88 := by rw [← pow_add]
  have e192 : (2 : ℝ) ^ 192 = 2 ^ 168 * 2 ^ 24 := by rw [← pow_add]
  have hc : (0 : ℝ) < 2 ^ 168 := by positivity
  rw [e256, e192]
  generalize (2 : ℝ) ^ 168 = c at hc ⊢
  set Q : ℝ := (q1 : ℝ) + 1525202 + q2 with hQ
  set X : ℝ := (q1 : ℝ) + q2 + 2 ^ 21 with hX
  have hQX : Q ≤ X := by rw [hQ, hX]; norm_num; linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hcX : 0 ≤ c * X := mul_nonneg hc.le (by rw [hX]; positivity)
  have hcQX : c * Q ≤ c * X := mul_le_mul_of_nonneg_left hQX hc.le
  have t1 : 2 * Q / (c * 2 ^ 88) ≤ X / (2 * c) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have t2 : 4 * Q * 1525202 / (c * 2 ^ 24) ≤ X / (2 * c) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have t3 : X / (2 * c) + X / (2 * c) = X / c := by
    field_simp
    ring
  linarith

theorem s4_gen_core (compression : Compression) (first : OracleComp World State)
    (next : State → (Index → Nonce128) → OracleComp World α)
    (firstBudget nextBudget : Nat) (firstBounded : PublicQueryBound first firstBudget)
    (nextBounded : ∀ state salt, PublicQueryBound (next state salt) nextBudget) :
    measureTVDist (s4RealGame compression first next) (s4IdealGame compression first next) ≤
      S5_GEN_LOSS firstBudget nextBudget := by
  apply s4_tv_le_of_events _ _ _ (by unfold S5_GEN_LOSS; positivity)
  intro event
  rw [s4_real_game_event, s4_ideal_game_event, ENNReal.toReal_ofReal (Strat.prob_nonneg _ _ _),
    ENNReal.toReal_ofReal (Strat.prob_nonneg _ _ _)]
  have bound := s4GenCallModel.gen_bound (2 ^ 192) s4_gen_out_regular (List.finRange S4_GEN_BLOCKS)
    (List.nodup_finRange S4_GEN_BLOCKS) (toStrat compression first)
    (s4StratNext compression next event) firstBudget nextBudget
    (to_strat_QB compression firstBounded)
    (fun state parts => s4_strat_next_QB compression next event nextBudget nextBounded state parts)
  rw [List.length_finRange] at bound
  exact bound.trans (s4_gen_loss_arith firstBudget nextBudget)

/-- **Generated nonces.** Replacing the uniform nonce vector by the generator's output, under a
uniform seed drawn after the first stage, changes any bounded continuation by at most
`S5_GEN_LOSS`. -/
theorem s4_generator_indistinguishable (compression : Compression) {State α : Type}
    (first : OracleComp World State) (next : State → (Index → Nonce128) → OracleComp World α)
    (firstBudget nextBudget : Nat) (firstBounded : PublicQueryBound first firstBudget)
    (nextBounded : ∀ state salt, PublicQueryBound (next state salt) nextBudget) :
    measureTVDist
      (do let permutation ← $ᵗ Perm
          let state ← fixedOracleRun ⟨compression, permutation⟩ first
          let seed ← $ᵗ BitVec 256
          fixedOracleRun ⟨compression, permutation⟩ (next state (s4GenSalt permutation seed)))
      (do let permutation ← $ᵗ Perm
          let state ← fixedOracleRun ⟨compression, permutation⟩ first
          let salt ← $ᵗ (Index → Nonce128)
          fixedOracleRun ⟨compression, permutation⟩ (next state salt)) ≤ S5_GEN_LOSS firstBudget nextBudget :=
  s4_gen_core compression first next firstBudget nextBudget firstBounded nextBounded

end CommitGolfCandidate
