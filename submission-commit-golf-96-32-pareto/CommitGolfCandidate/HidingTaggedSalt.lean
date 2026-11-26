import CommitGolfCandidate.HidingHybrid
import CommitGolfCandidate.HidingFreshness

/-! Simultaneous reprogramming of all unopened Call 0 inputs (`leafInitInput i (salt i) (m i)`
for `i ∉ positions`) from the real compression table to independent uniform 256-bit digests
`freshInit i`.

Because every Call 0 input carries the unique 64-bit position tag `leafTag i = 4072 + 256*i`
in bits `[128, 192)` alongside a 128-bit uniform salt in bits `[0, 128)`:
- Any fixed query (prior cache, cache outputs, or second-stage observer query) can match at
  most one unopened position via `tagIndex`, yielding `≤ 1 / 2^128` per query (`≤ 3 * budget / 2^128`).
- Any freshly sampled 256-bit digest (`freshInit` or internal compression output during honest
  tree construction) must simultaneously hit one of `≤ LENGTH` tags (64 bits) AND its salt
  (128 bits), yielding `≤ LENGTH / 2^192` per draw (`≤ 6 * LENGTH^2 / 2^192 = 6 / 2^144`). -/
namespace CommitGolfCandidate

local instance (priority := high) hidingTaggedSaltDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

/-! ### 1. Unopened salt/tag hit predicates and probability bounds -/

/-- Whether the low 192 bits of a 256-bit digest match `(salt i, leafTag i)` for some unopened `i`. -/
def digestHitsUnopened (positions : Positions) (salt : Index → Salt) (v : Digest) : Bool :=
  match tagIndexOfWord (v.extractLsb' 128 64) with
  | some i => decide (i ∉ positions ∧ v.extractLsb' 0 128 = salt i)
  | none => false

/-- Whether the low 192 bits of a 768-bit compression input match `(salt i, leafTag i)` for some unopened `i`. -/
def inputHitsUnopened (positions : Positions) (salt : Index → Salt)
    (x : BitVec COMPRESSION_INPUT_LENGTH) : Bool :=
  match tagIndex x with
  | some i => decide (i ∉ positions ∧ x.extractLsb' 0 128 = salt i)
  | none => false

/-- Mark any compression query satisfying a boolean predicate. -/
def marksPred (pred : BitVec COMPRESSION_INPUT_LENGTH → Bool) : World.Domain → Bool
  | .inr (.inl x) => pred x
  | _ => false

def marksUnopened (positions : Positions) (salt : Index → Salt) : World.Domain → Bool :=
  marksPred (inputHitsUnopened positions salt)

theorem inputHitsUnopened_eq_digestHitsUnopened (positions : Positions) (salt : Index → Salt)
    (x : BitVec COMPRESSION_INPUT_LENGTH) :
    inputHitsUnopened positions salt x = digestHitsUnopened positions salt (x.extractLsb' 0 256) := by
  have hlow : (x.extractLsb' 0 256).extractLsb' 0 128 = x.extractLsb' 0 128 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp [BitVec.getLsbD_extractLsb', hk, show k < 256 by omega]
  have htag : (x.extractLsb' 0 256).extractLsb' 128 64 = x.extractLsb' 128 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp [BitVec.getLsbD_extractLsb', hk, show 128 + k < 256 by omega]
  unfold inputHitsUnopened digestHitsUnopened tagIndex
  rw [hlow, htag]

theorem inputHitsUnopened_leafInitInput_opened (positions : Positions) (salt : Index → Salt)
    (idx : Index) (opened : idx ∈ positions) (s : Salt) (v : Entry) :
    inputHitsUnopened positions salt (leafInitInput idx s v) = false := by
  rw [inputHitsUnopened, tagIndex_leafInitInput]
  simp [opened]

theorem inputHitsUnopened_leafInitInput_unopened (positions : Positions) (salt : Index → Salt)
    (idx : Index) (unopened : idx ∉ positions) (v : Entry) :
    inputHitsUnopened positions salt (leafInitInput idx (salt idx) v) = true := by
  rw [inputHitsUnopened, tagIndex_leafInitInput, leafInitInput_salt]
  simp [unopened]

theorem inputHitsUnopened_leafInput (positions : Positions) (salt : Index → Salt)
    (d : Digest) (block : LeafBlock) :
    inputHitsUnopened positions salt (leafInput d block) = digestHitsUnopened positions salt d := by
  rw [inputHitsUnopened_eq_digestHitsUnopened, leafInput_digest]

theorem padInput_low256 (right left : Digest) :
    (padInput (right ++ left)).extractLsb' 0 256 = left := by
  have h1 : (padInput (right ++ left)).extractLsb' 0 512 = right ++ left :=
    BitVec.extractLsb'_append_eq_right
  have h2 : (right ++ left).extractLsb' 0 256 = left :=
    BitVec.extractLsb'_append_eq_right
  have h3 (x : BitVec COMPRESSION_INPUT_LENGTH) :
      (x.extractLsb' 0 512).extractLsb' 0 256 = x.extractLsb' 0 256 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp [BitVec.getLsbD_extractLsb', hk, show k < 512 by omega]
  rw [← h3 (padInput (right ++ left)), h1, h2]

theorem inputHitsUnopened_padInput (positions : Positions) (salt : Index → Salt)
    (right left : Digest) :
    inputHitsUnopened positions salt (padInput (right ++ left)) = digestHitsUnopened positions salt left := by
  rw [inputHitsUnopened_eq_digestHitsUnopened, padInput_low256]

/-- For any fixed `salt`, a uniform 256-bit digest hits an unopened `(salt i, leafTag i)`
with probability at most `LENGTH / 2^192`. -/
theorem digest_hits_unopened_uniform_prob (positions : Positions) (salt : Index → Salt) :
    prEvent ((fun v : Digest => digestHitsUnopened positions salt v = true) <$> ($ᵗ Digest)) ≤
      (LENGTH : ENNReal) / 2 ^ 192 := by
  classical
  have implies_exists :
      prEvent ((fun v : Digest => digestHitsUnopened positions salt v = true) <$> ($ᵗ Digest)) ≤
      prEvent ((fun v : Digest => ∃ i : Index, v.extractLsb' 0 192 = leafTag i ++ salt i) <$> ($ᵗ Digest)) := by
    apply prEvent_mono_of_support
    intro v _ hhit
    unfold digestHitsUnopened at hhit
    cases htag : tagIndexOfWord (v.extractLsb' 128 64) with
    | none => simp [htag] at hhit
    | some i =>
      rw [htag] at hhit
      simp only [decide_eq_true_eq] at hhit
      refine ⟨i, ?_⟩
      have htagEq : v.extractLsb' 128 64 = leafTag i := by
        dsimp only [tagIndexOfWord] at htag
        split at htag
        · rename_i hcond
          simp only [Option.some.injEq] at htag
          subst htag
          apply BitVec.eq_of_toNat_eq
          rw [leafTag_toNat]
          dsimp only at hcond ⊢
          omega
        · simp at htag
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      by_cases h128 : k < 128
      · rw [BitVec.getLsbD_append]; simp [h128, ← hhit.2, BitVec.getLsbD_extractLsb', hk]
      · rw [BitVec.getLsbD_append]
        have hk64 : k - 128 < 64 := by omega
        have h1 : (v.extractLsb' 128 64).getLsbD (k - 128) = (leafTag i).getLsbD (k - 128) :=
          congrArg (fun w : Word => w.getLsbD (k - 128)) htagEq
        simp only [h128, ↓reduceIte, ← h1, BitVec.getLsbD_extractLsb', hk, hk64, decide_true, Bool.true_and]
        exact congrArg v.getLsbD (by omega)
  have single_prob (target : BitVec 192) :
      prEvent ((fun v : Digest => v.extractLsb' 0 192 = target) <$> ($ᵗ Digest)) ≤ 1 / (2 ^ 192 : ENNReal) := by
    rw [SampleableType.prEvent_uniformSample]
    have cardLe : (Finset.univ.filter (fun v : Digest => v.extractLsb' 0 192 = target)).card ≤ 2 ^ 64 := by
      calc (Finset.univ.filter (fun v : Digest => v.extractLsb' 0 192 = target)).card
          ≤ (Finset.univ.image (fun hi : BitVec 64 => hi ++ target)).card := by
            apply Finset.card_le_card
            intro v hv
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
            rw [Finset.mem_image]
            refine ⟨v.extractLsb' 192 64, Finset.mem_univ _, ?_⟩
            apply BitVec.eq_of_getLsbD_eq
            intro k hk
            by_cases h192 : k < 192
            · rw [BitVec.getLsbD_append]
              simp [h192, ← hv, BitVec.getLsbD_extractLsb', hk]
            · rw [BitVec.getLsbD_append]
              simp only [h192, ↓reduceIte, BitVec.getLsbD_extractLsb', show k - 192 < 64 by omega,
                decide_true, Bool.true_and]
              exact congrArg v.getLsbD (by omega)
        _ ≤ Finset.univ.card := Finset.card_image_le
        _ = 2 ^ 64 := by simp
    have hcard : Fintype.card Digest = 2 ^ 256 := by simp [Digest]
    rw [hcard]
    calc ((Finset.univ.filter (fun v : Digest => v.extractLsb' 0 192 = target)).card : ENNReal) / (2 ^ 256 : Nat)
        ≤ ((2 ^ 64 : Nat) : ENNReal) / ((2 ^ 256 : Nat) : ENNReal) :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr cardLe) _
      _ = 1 / (2 ^ 192 : ENNReal) := by
          rw [show ((2 ^ 256 : Nat) : ENNReal) = (2 ^ 64 : ENNReal) * (2 ^ 192 : ENNReal) by
                rw [← pow_add]; norm_num,
              show ((2 ^ 64 : Nat) : ENNReal) = (2 ^ 64 : ENNReal) * 1 by norm_num]
          exact ENNReal.mul_div_mul_left 1 (2 ^ 192) (by positivity) (by finiteness)
  have union := prEvent_exists_finset_le (Finset.univ : Finset Index) ($ᵗ Digest)
    (fun i v => v.extractLsb' 0 192 = leafTag i ++ salt i)
  refine implies_exists.trans ?_
  have eqEv : (fun v : Digest => ∃ i ∈ (Finset.univ : Finset Index), v.extractLsb' 0 192 = leafTag i ++ salt i) =
      (fun v : Digest => ∃ i : Index, v.extractLsb' 0 192 = leafTag i ++ salt i) := by
    funext v; simp
  rw [eqEv] at union
  refine union.trans ?_
  calc ∑ i : Index, prEvent ((fun v : Digest => v.extractLsb' 0 192 = leafTag i ++ salt i) <$> ($ᵗ Digest))
      ≤ ∑ _i : Index, (1 / (2 ^ 192 : ENNReal)) := Finset.sum_le_sum (fun i _ => single_prob _)
    _ = (LENGTH : ENNReal) / 2 ^ 192 := by
        simp [Finset.sum_const, nsmul_eq_mul, Index, div_eq_mul_inv]

/-- Any single fixed compression input hits a fresh uniform 128-bit salt vector with
probability at most `1 / 2^128` (because `tagIndex` selects at most one position). -/
theorem input_hits_unopened_salt_prob (positions : Positions)
    (x : BitVec COMPRESSION_INPUT_LENGTH) :
    prEvent ((fun salt : Index → Salt => inputHitsUnopened positions salt x = true) <$> ($ᵗ (Index → Salt))) ≤
      1 / (2 ^ 128 : ENNReal) := by
  unfold inputHitsUnopened
  cases htag : tagIndex x with
  | none =>
    have h0 : prEvent ((fun _ : Index → Salt => false = true) <$> ($ᵗ (Index → Salt))) = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      intro _ _ h; exact Bool.noConfusion h
    rw [h0]; exact bot_le
  | some i =>
    by_cases hi : i ∈ positions
    · have h0 : prEvent ((fun salt : Index → Salt => decide (i ∉ positions ∧ x.extractLsb' 0 128 = salt i) = true) <$> ($ᵗ (Index → Salt))) = 0 := by
        apply prEvent_eq_zero_of_forall_mem_support
        intro salt _ h; simp [hi] at h
      rw [h0]; exact bot_le
    · have heq : (fun salt : Index → Salt => decide (i ∉ positions ∧ x.extractLsb' 0 128 = salt i) = true) =
          fun salt => salt i = x.extractLsb' 0 128 := by
        funext salt; simp [hi, eq_comm]
      rw [heq, salt128_guess_probability i (x.extractLsb' 0 128)]

theorem digest_hits_unopened_salt_prob (positions : Positions) (v : Digest) :
    prEvent ((fun salt : Index → Salt => digestHitsUnopened positions salt v = true) <$> ($ᵗ (Index → Salt))) ≤
      1 / (2 ^ 128 : ENNReal) := by
  have h := input_hits_unopened_salt_prob positions (padInput ((0 : Digest) ++ v))
  simpa only [inputHitsUnopened_padInput] using h

theorem list_input_hits_salt_bound (positions : Positions)
    (trace : List (BitVec COMPRESSION_INPUT_LENGTH)) :
    prEvent ((fun salt : Index → Salt => trace.any (inputHitsUnopened positions salt) = true) <$> ($ᵗ (Index → Salt))) ≤
      (trace.length : ENNReal) / 2 ^ 128 := by
  classical
  have inc :
      prEvent ((fun salt : Index → Salt => trace.any (inputHitsUnopened positions salt) = true) <$> ($ᵗ (Index → Salt))) ≤
      prEvent ((fun salt : Index → Salt => ∃ x ∈ trace.toFinset, inputHitsUnopened positions salt x = true) <$> ($ᵗ (Index → Salt))) := by
    apply prEvent_mono_of_support
    intro salt _ h
    obtain ⟨x, hx, hhit⟩ := List.any_eq_true.mp h
    exact ⟨x, List.mem_toFinset.mpr hx, hhit⟩
  refine inc.trans ((prEvent_exists_finset_le trace.toFinset ($ᵗ (Index → Salt))
    (fun x salt => inputHitsUnopened positions salt x = true)).trans ?_)
  calc ∑ x ∈ trace.toFinset, prEvent ((fun salt : Index → Salt => inputHitsUnopened positions salt x = true) <$> ($ᵗ (Index → Salt)))
      ≤ ∑ _x ∈ trace.toFinset, (1 / (2 ^ 128 : ENNReal)) :=
        Finset.sum_le_sum (fun x _ => input_hits_unopened_salt_prob positions x)
    _ = (trace.toFinset.card : ENNReal) / 2 ^ 128 := by
        simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (trace.length : ENNReal) / 2 ^ 128 :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr (List.toFinset_card_le trace)) _

/-! ### 2. Splitting `salt` into opened vs unopened coordinates -/

def combineSalts (positions : Positions) (sOpen sHidden : Index → Salt) : Index → Salt :=
  fun i => if i ∈ positions then sOpen i else sHidden i

private def combineOn (list : List Index) (a b : Index → Salt) : Index → Salt :=
  fun i => if i ∈ list then a i else b i

private theorem combineOn_uniform (list : List Index) (nodup : list.Nodup)
    {α : Type} (next : (Index → Salt) → ProbComp α) :
    𝒟[do let a ← $ᵗ (Index → Salt)
         let b ← $ᵗ (Index → Salt)
         next (combineOn list a b)] =
    𝒟[do let salt ← $ᵗ (Index → Salt); next salt] := by
  induction list generalizing next with
  | nil =>
    have heq (a b : Index → Salt) : combineOn [] a b = b := by funext i; simp [combineOn]
    simp only [heq]
    exact OracleComp.evalDist_bind_const _ _
  | cons idx rest ih =>
    obtain ⟨notMem, restNodup⟩ := List.nodup_cons.mp nodup
    have step :
        𝒟[do let a ← $ᵗ (Index → Salt)
             let v ← $ᵗ Salt
             let b ← $ᵗ (Index → Salt)
             next (combineOn (idx :: rest) (Function.update a idx v) b)] =
        𝒟[do let a ← $ᵗ (Index → Salt)
             let b ← $ᵗ (Index → Salt)
             next (combineOn (idx :: rest) a b)] := by
      exact uniform_coordinate_bind idx (fun a => do
        let b ← $ᵗ (Index → Salt)
        next (combineOn (idx :: rest) a b))
    rw [← step]
    have splitEq (a b : Index → Salt) (v : Salt) :
        combineOn (idx :: rest) (Function.update a idx v) b =
          Function.update (combineOn rest a b) idx v := by
      funext i
      by_cases h : i = idx
      · subst h; simp [combineOn]
      · simp [combineOn, h]
    simp only [splitEq]
    trans 𝒟[do let v ← $ᵗ Salt
                let a ← $ᵗ (Index → Salt)
                let b ← $ᵗ (Index → Salt)
                next (Function.update (combineOn rest a b) idx v)]
    · exact distribution_bind_comm _ _ _
    · trans 𝒟[do let v ← $ᵗ Salt
                  let salt ← $ᵗ (Index → Salt)
                  next (Function.update salt idx v)]
      · apply _root_.evalDist_bind_congr
        intro v
        exact ih restNodup (fun salt => next (Function.update salt idx v))
      · trans 𝒟[do let salt ← $ᵗ (Index → Salt)
                    let v ← $ᵗ Salt
                    next (Function.update salt idx v)]
        · exact distribution_bind_comm _ _ _
        · exact uniform_coordinate_bind idx next

theorem combine_salts_uniform (positions : Positions) {α : Type}
    (next : (Index → Salt) → ProbComp α) :
    𝒟[do let sOpen ← $ᵗ (Index → Salt)
         let sHidden ← $ᵗ (Index → Salt)
         next (combineSalts positions sOpen sHidden)] =
    𝒟[do let salt ← $ᵗ (Index → Salt); next salt] := by
  have heq (a b : Index → Salt) : combineSalts positions a b = combineOn positions.toList a b := by
    funext i; simp [combineSalts, combineOn]
  simp only [heq]
  exact combineOn_uniform positions.toList (Finset.nodup_toList positions) next

theorem inputHitsUnopened_combine (positions : Positions) (sOpen sHidden : Index → Salt)
    (x : BitVec COMPRESSION_INPUT_LENGTH) :
    inputHitsUnopened positions (combineSalts positions sOpen sHidden) x =
      inputHitsUnopened positions sHidden x := by
  unfold inputHitsUnopened combineSalts
  cases tagIndex x with
  | none => rfl
  | some i =>
    by_cases hi : i ∈ positions <;> simp [hi]

theorem marksUnopened_combine (positions : Positions) (sOpen sHidden : Index → Salt) :
    marksUnopened positions (combineSalts positions sOpen sHidden) = marksUnopened positions sHidden := by
  funext q
  rcases q with _ | (x | _) <;> simp [marksUnopened, marksPred, inputHitsUnopened_combine]

theorem hybridTranscript_combine (compress : Compression) (positions : Positions)
    (message : Message) (sOpen sHidden : Index → Salt) (freshInit : Index → Digest) :
    hybridTranscript compress positions message (combineSalts positions sOpen sHidden) freshInit =
      hybridTranscript compress positions message sOpen freshInit := by
  have hheap : hybridHeap compress positions message (combineSalts positions sOpen sHidden) freshInit =
      hybridHeap compress positions message sOpen freshInit := by
    unfold hybridHeap
    congr 1
    funext idx
    split
    · unfold hybridLeafDigest combineSalts
      split <;> simp_all
    · rfl
  unfold hybridTranscript
  rw [hheap]
  exact Prod.ext rfl (reference_opening_salt_congr _
    (combineSalts positions sOpen sHidden) sOpen positions
    (fun i hi => by simp [combineSalts, hi]))

/-! ### 3. Simultaneous reprogramming of all unopened Call 0 inputs -/

def reprogramList (message : Message) (salt : Index → Salt) (freshInit : Index → Digest) :
    List Index → Compression → Compression
  | [], table => table
  | i :: rest, table =>
      Function.update (reprogramList message salt freshInit rest table)
        (leafInitInput i (salt i) (message i)) (freshInit i)

private theorem leafInitInput_ne_of_index_ne (salt : Index → Salt) (message : Message)
    {i j : Index} (hne : i ≠ j) :
    leafInitInput i (salt i) (message i) ≠ leafInitInput j (salt j) (message j) := by
  intro h
  have ht := congrArg (fun x => x.extractLsb' 128 64) h
  rw [leafInitInput_tag, leafInitInput_tag] at ht
  exact hne (leafTag_injective ht)

theorem reprogramList_mem (message : Message) (salt : Index → Salt) (freshInit : Index → Digest)
    (list : List Index) (nodup : list.Nodup) (table : Compression)
    (i : Index) (hi : i ∈ list) :
    reprogramList message salt freshInit list table (leafInitInput i (salt i) (message i)) = freshInit i := by
  induction list with
  | nil => simp at hi
  | cons hd tl ih =>
    obtain ⟨notMem, tlNodup⟩ := List.nodup_cons.mp nodup
    rcases List.mem_cons.mp hi with rfl | htl
    · dsimp only [reprogramList]
      erw [Function.update_self]
    · have hne : i ≠ hd := fun h => notMem (h ▸ htl)
      dsimp only [reprogramList]
      erw [Function.update_of_ne (leafInitInput_ne_of_index_ne salt message hne)]
      exact ih tlNodup htl

theorem reprogramList_outside (message : Message) (salt : Index → Salt) (freshInit : Index → Digest)
    (list : List Index) (table : Compression) (x : BitVec COMPRESSION_INPUT_LENGTH)
    (houtside : ∀ i ∈ list, x ≠ leafInitInput i (salt i) (message i)) :
    reprogramList message salt freshInit list table x = table x := by
  induction list with
  | nil => rfl
  | cons hd tl ih =>
    dsimp only [reprogramList, Function.update]
    rw [dif_neg (houtside hd List.mem_cons_self)]
    exact ih (fun i hi => houtside i (List.mem_cons_of_mem _ hi))

private theorem reprogramList_update_comm (message : Message) (salt : Index → Salt)
    (freshInit : Index → Digest) (list : List Index) (table : Compression)
    (i : Index) (hnot : i ∉ list) (v : Digest) :
    Function.update (reprogramList message salt freshInit list table)
      (leafInitInput i (salt i) (message i)) v =
    reprogramList message salt freshInit list
      (Function.update table (leafInitInput i (salt i) (message i)) v) := by
  induction list with
  | nil => rfl
  | cons hd tl ih =>
    have hne : i ≠ hd := fun h => hnot (h ▸ List.mem_cons_self)
    have hnot' : i ∉ tl := fun h => hnot (List.mem_cons_of_mem _ h)
    rw [reprogramList, reprogramList, ← ih hnot']
    exact Function.update_comm (leafInitInput_ne_of_index_ne salt message hne).symm _ _ _

private theorem reprogramList_freshInit_update (message : Message) (salt : Index → Salt)
    (freshInit : Index → Digest) (list : List Index) (table : Compression)
    (i : Index) (hnot : i ∉ list) (v : Digest) :
    reprogramList message salt (Function.update freshInit i v) list table =
      reprogramList message salt freshInit list table := by
  induction list with
  | nil => rfl
  | cons hd tl ih =>
    have hne : hd ≠ i := fun h => hnot (h ▸ List.mem_cons_self)
    have hnot' : i ∉ tl := fun h => hnot (List.mem_cons_of_mem _ h)
    rw [reprogramList, reprogramList, Function.update_of_ne hne, ih hnot']

/-- Simultaneous reprogramming on distinct inputs preserves the uniform compression table. -/
theorem reprogramList_uniform (message : Message) (salt : Index → Salt)
    (list : List Index) (nodup : list.Nodup) {α : Type} (next : Compression → ProbComp α) :
    𝒟[do let freshInit ← $ᵗ (Index → Digest)
         let table ← $ᵗ Compression
         next (reprogramList message salt freshInit list table)] =
    𝒟[do let table ← $ᵗ Compression; next table] := by
  induction list with
  | nil =>
    simp only [reprogramList]
    exact OracleComp.evalDist_bind_const _ _
  | cons hd tl ih =>
    obtain ⟨notMem, tlNodup⟩ := List.nodup_cons.mp nodup
    have splitFresh := uniform_coordinate_bind hd (fun freshInit : Index → Digest => do
      let table ← $ᵗ Compression
      next (reprogramList message salt freshInit (hd :: tl) table))
    rw [← splitFresh]
    simp only [reprogramList, Function.update_self]
    have simpRest (freshInit : Index → Digest) (v : Digest) (table : Compression) :
        Function.update (reprogramList message salt (Function.update freshInit hd v) tl table)
          (leafInitInput hd (salt hd) (message hd)) v =
        reprogramList message salt freshInit tl
          (Function.update table (leafInitInput hd (salt hd) (message hd)) v) := by
      rw [reprogramList_freshInit_update message salt freshInit tl table hd notMem v,
        reprogramList_update_comm message salt freshInit tl table hd notMem v]
    simp only [simpRest]
    trans 𝒟[do let freshInit ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                next (reprogramList message salt freshInit tl table)]
    · apply _root_.evalDist_bind_congr
      intro freshInit
      exact compression_table_update_bind (leafInitInput hd (salt hd) (message hd))
        (fun table => next (reprogramList message salt freshInit tl table))
    · exact ih tlNodup

noncomputable def unopenedList (positions : Positions) : List Index :=
  (Finset.univ.filter (fun i : Index => i ∉ positions)).toList

theorem unopenedList_nodup (positions : Positions) : (unopenedList positions).Nodup :=
  Finset.nodup_toList _

theorem mem_unopenedList (positions : Positions) (i : Index) :
    i ∈ unopenedList positions ↔ i ∉ positions := by
  simp [unopenedList]

def cacheHitsUnopened (cache : CompressionCache) (positions : Positions)
    (message : Message) (salt : Index → Salt) : Prop :=
  ∃ i : Index, i ∉ positions ∧ cache (leafInitInput i (salt i) (message i)) ≠ none

theorem reprogram_agrees_outside (permutation : Perm) (cache : CompressionCache)
    (positions : Positions) (message : Message) (salt : Index → Salt) (freshInit : Index → Digest)
    (table : Compression) (query : World.Domain)
    (unmarked : marksUnopened positions salt query = false) :
    (Oracle.mk (tableExtending cache table) permutation).world query =
      (Oracle.mk (tableExtending cache (reprogramList message salt freshInit (unopenedList positions) table)) permutation).world query := by
  rcases query with coins | publicQuery
  · rfl
  · rcases publicQuery with x | permQuery
    · have houtside : ∀ i ∈ unopenedList positions, x ≠ leafInitInput i (salt i) (message i) := by
        intro i hi heq
        subst heq
        have hun : i ∉ positions := (mem_unopenedList positions i).mp hi
        have hmark := inputHitsUnopened_leafInitInput_unopened positions salt i hun (message i)
        change inputHitsUnopened positions salt _ = false at unmarked
        rw [hmark] at unmarked
        exact Bool.noConfusion unmarked
      simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr, pure_inj, tableExtending]
      rw [reprogramList_outside message salt freshInit (unopenedList positions) table x houtside]
    · rcases permQuery with _ | _ <;> rfl

theorem reprogram_transcript_eq_hybrid (cache : CompressionCache) (positions : Positions)
    (message : Message) (salt : Index → Salt) (freshInit : Index → Digest) (table : Compression)
    (noHit : ¬ cacheHitsUnopened cache positions message salt) :
    let table' := reprogramList message salt freshInit (unopenedList positions) table
    referenceTranscript (tableExtending cache table') message salt positions =
      hybridTranscript (tableExtending cache table') positions message salt freshInit := by
  dsimp only
  let C := tableExtending cache (reprogramList message salt freshInit (unopenedList positions) table)
  have hheap : saltedHeap C message salt = hybridHeap C positions message salt freshInit := by
    unfold saltedHeap hybridHeap
    congr 1
    funext idx
    split
    · rename_i inside
      unfold hybridLeafDigest
      by_cases hi : (⟨idx, inside⟩ : Index) ∈ positions
      · rw [if_pos hi]
      · rw [if_neg hi]
        let i : Index := ⟨idx, inside⟩
        have hi' : i ∉ positions := hi
        have hnone : cache (leafInitInput i (salt i) (message i)) = none := by
          by_contra hne
          exact noHit ⟨i, hi', hne⟩
        have hC : C (leafInitInput i (salt i) (message i)) = freshInit i := by
          change (cache (leafInitInput i (salt i) (message i))).getD
            (reprogramList message salt freshInit (unopenedList positions) table
              (leafInitInput i (salt i) (message i))) = freshInit i
          rw [hnone, Option.getD_none,
            reprogramList_mem message salt freshInit (unopenedList positions)
              (unopenedList_nodup positions) table i ((mem_unopenedList positions i).mpr hi')]
        unfold leafDigest
        change leafDigestFromInit C (C (leafInitInput i (salt i) (message i))) (message i) =
          leafDigestFromInit C (freshInit i) (message i)
        rw [hC]
    · rfl
  unfold referenceTranscript hybridTranscript
  rw [hheap]

/-! ### 4. Bottom-up `evalHybridTranscript` (≤ 5*LENGTH queries, exact heap, clean trace) -/

/-- Compute one hybrid leaf digest (`≤ 4` compression queries). -/
def evalHybridLeaf (positions : Positions) (message : Message) (salt : Index → Salt)
    (freshInit : Index → Digest) (idx : Index) : OracleComp World Digest :=
  if idx ∈ positions then do
    let d0 ← (liftM (World.query (.inr (.inl (leafInitInput idx (salt idx) (message idx))))) : OracleComp World Digest)
    hashBlocks (leafTailBlocks (message idx)) d0
  else
    hashBlocks (leafTailBlocks (message idx)) (freshInit idx)

/-- Compute all leaf digests in one bottom-up pass (at most `4 * n` queries). -/
def evalHybridLeaves (positions : Positions) (message : Message) (salt : Index → Salt)
    (freshInit : Index → Digest) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun _ => 0)
  | n + 1 => do
      let rest ← evalHybridLeaves positions message salt freshInit n
      if h : n < LENGTH then
        let d ← evalHybridLeaf positions message salt freshInit ⟨n, h⟩
        pure (Function.update rest n d)
      else pure rest

/-- Compute internal nodes `LENGTH - 1` down to `LENGTH - k` bottom-up (`k` queries). -/
def evalParents (leaves : Nat → Digest) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun node => if LENGTH ≤ node ∧ node < 2 * LENGTH then leaves (node - LENGTH) else 0)
  | k + 1 => do
      let heap ← evalParents leaves k
      let node := LENGTH - 1 - k
      let p ← hashParent (heap (2 * node)) (heap (2 * node + 1))
      pure (Function.update heap node p)

def evalHybridTranscript (positions : Positions) (message : Message) (salt : Index → Salt)
    (freshInit : Index → Digest) : OracleComp World (Commitment × Proof) := do
  let leaves ← evalHybridLeaves positions message salt freshInit LENGTH
  let heap ← evalParents leaves (LENGTH - 1)
  pure (heap 1, referenceOpening heap salt positions)

def evalHybridObserve {α : Type} (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest)
    (observe : Commitment → Proof → OracleComp World α) : OracleComp World α := do
  let transcript ← evalHybridTranscript positions message salt freshInit
  observe transcript.1 transcript.2

theorem eval_hybrid_leaf_bound (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) (idx : Index) :
    PublicQueryBound (evalHybridLeaf positions message salt freshInit idx) 4 := by
  unfold evalHybridLeaf
  split_ifs
  · change 1 ≤ 4 ∧ ∀ d0, PublicQueryBound (hashBlocks (leafTailBlocks _) d0) 3
    exact ⟨by decide, fun d0 => by simpa [leafTailBlocks] using hash_blocks_bound (leafTailBlocks _) d0⟩
  · exact (hash_blocks_bound _ _).mono (by simp [leafTailBlocks])

theorem eval_hybrid_leaves_bound (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) (n : Nat) :
    PublicQueryBound (evalHybridLeaves positions message salt freshInit n) (4 * n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [evalHybridLeaves, show 4 * (n + 1) = 4 * n + 4 by omega]
    apply public_query_bound_bind ih
    intro rest
    split
    · rename_i h
      change PublicQueryBound _ (4 + 0)
      exact public_query_bound_bind (eval_hybrid_leaf_bound positions message salt freshInit ⟨n, h⟩) (fun _ => trivial)
    · trivial

theorem eval_parents_bound (leaves : Nat → Digest) (k : Nat) :
    PublicQueryBound (evalParents leaves k) k := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [evalParents]
    apply public_query_bound_bind ih
    intro heap
    dsimp only
    rw [← Nat.add_zero 1]
    exact public_query_bound_bind (hash_parent_bound _ _) (fun _ => trivial)

theorem fixed_eval_hybrid_leaf (oracle : Oracle) (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) (idx : Index) :
    fixedOracleRun oracle (evalHybridLeaf positions message salt freshInit idx) =
      pure (hybridLeafDigest oracle.compression positions message salt freshInit idx) := by
  unfold evalHybridLeaf hybridLeafDigest
  split
  · erw [fixed_oracle_run_public]
    have h := fixed_hash_blocks oracle (leafTailBlocks (message idx))
      (oracle.compression (leafInitInput idx (salt idx) (message idx))) pure
    simp only [bind_pure, fixed_oracle_run_pure] at h
    exact h
  · have h := fixed_hash_blocks oracle (leafTailBlocks (message idx)) (freshInit idx) pure
    simpa only [bind_pure, fixed_oracle_run_pure, leafDigestFromInit] using h

theorem fixed_eval_hybrid_leaves (oracle : Oracle) (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) (n : Nat) :
    fixedOracleRun oracle (evalHybridLeaves positions message salt freshInit n) =
      pure (fun i => if h : i < n ∧ i < LENGTH then
        hybridLeafDigest oracle.compression positions message salt freshInit ⟨i, h.2⟩ else 0) := by
  induction n with
  | zero =>
    rw [evalHybridLeaves, fixed_oracle_run_pure]
    exact congrArg pure (funext fun i => by simp)
  | succ n ih =>
    rw [evalHybridLeaves, fixed_oracle_run_bind, ih, pure_bind]
    split
    · rename_i hn
      rw [fixed_oracle_run_bind, fixed_eval_hybrid_leaf, pure_bind, fixed_oracle_run_pure]
      congr 1; funext i
      by_cases hi : i = n
      · subst hi; simp [hn]
      · rw [Function.update_of_ne hi]
        by_cases hlt : i < n
        · simp [hlt, show i < n + 1 by omega]
        · simp [hlt, show ¬ i < n + 1 by omega]
    · rename_i hn
      rw [fixed_oracle_run_pure]
      congr 1; funext i
      by_cases hlt : i < LENGTH
      · simp [hlt, show i < n ↔ i < n + 1 by omega]
      · simp [hlt]

theorem fixed_eval_parents (oracle : Oracle) (leaves : Nat → Digest) (k : Nat)
    (hk : k ≤ LENGTH - 1) :
    fixedOracleRun oracle (evalParents leaves k) =
      pure (fun node =>
        if LENGTH - k ≤ node ∧ node < 2 * LENGTH then
          referenceHeap oracle.compression LENGTH leaves node
        else 0) := by
  induction k with
  | zero =>
    rw [evalParents, fixed_oracle_run_pure]
    congr 1; funext node
    simp only [Nat.sub_zero]
    split
    · rename_i h
      have hsub : node - LENGTH < LENGTH := by omega
      have hadd : LENGTH + (node - LENGTH) = node := by omega
      rw [← hadd, reference_heap_leaf _ _ _ _ hsub, Nat.add_sub_cancel_left]
    · rfl
  | succ k ih =>
    rw [evalParents, fixed_oracle_run_bind, ih (by omega), pure_bind]
    let node := LENGTH - 1 - k
    have hpos : 0 < node := by dsimp only [node]; omega
    have hlt : node < LENGTH := by dsimp only [node]; omega
    have h2l : LENGTH - k ≤ 2 * node ∧ 2 * node < 2 * LENGTH := by dsimp only [node]; omega
    have h2r : LENGTH - k ≤ 2 * node + 1 ∧ 2 * node + 1 < 2 * LENGTH := by dsimp only [node]; omega
    dsimp only
    rw [fixed_oracle_run_bind]
    have hp := fixed_hash_parent oracle
      (if LENGTH - k ≤ 2 * node ∧ 2 * node < 2 * LENGTH then referenceHeap oracle.compression LENGTH leaves (2 * node) else 0)
      (if LENGTH - k ≤ 2 * node + 1 ∧ 2 * node + 1 < 2 * LENGTH then referenceHeap oracle.compression LENGTH leaves (2 * node + 1) else 0)
      pure
    simp only [bind_pure, fixed_oracle_run_pure] at hp
    rw [hp, if_pos h2l, if_pos h2r, ← reference_heap_parent oracle.compression LENGTH leaves node hpos hlt,
      pure_bind, fixed_oracle_run_pure]
    congr 1; funext m
    have hnodeEq : LENGTH - 1 - k = node := rfl
    rw [hnodeEq]
    by_cases hm : m = node
    · subst hm
      have hnodeIn : LENGTH - (k + 1) ≤ node ∧ node < 2 * LENGTH := by dsimp only [node]; omega
      rw [Function.update_self, if_pos hnodeIn]
    · rw [Function.update_of_ne hm]
      have hiff : (LENGTH - k ≤ m ∧ m < 2 * LENGTH) ↔ (LENGTH - (k + 1) ≤ m ∧ m < 2 * LENGTH) := by
        dsimp only [node] at hm; omega
      by_cases hc : LENGTH - (k + 1) ≤ m ∧ m < 2 * LENGTH
      · rw [if_pos (hiff.mpr hc), if_pos hc]
      · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]

/-! ### 5. Generic trace/flag/cache lemmas -/

theorem flagged_run_trace_pred (oracle : Oracle) (pred : BitVec COMPRESSION_INPUT_LENGTH → Bool)
    {α : Type} (computation : OracleComp World α) (flag : Bool) :
    flaggedRun oracle (marksPred pred) computation flag =
      ((fun result : α × List (BitVec COMPRESSION_INPUT_LENGTH) =>
        (result.1, (), flag || result.2.any pred)) <$>
        fixedOracleRun oracle (traceCompression computation)) := by
  induction computation using OracleComp.inductionOn generalizing flag with
  | pure value =>
    simp only [flaggedRun, simulateQ_pure, StateT.run_pure, trace_compression_pure,
      fixed_oracle_run_pure, map_pure, List.any_nil, Bool.or_false]
  | query_bind query next ih =>
    rw [flagged_run_query_bind, trace_run_query_bind, map_bind]
    apply bind_congr
    intro answer
    rw [ih]
    simp only [bind_pure_comp, Functor.map_map]
    apply congrArg (fun f => f <$> fixedOracleRun oracle (traceCompression (next answer)))
    funext result
    have head : (compressionHead query).any pred = marksPred pred query := by
      rcases query with coins | publicQuery
      · rfl
      · rcases publicQuery with input | permQuery
        · change (pred input || false) = _
          exact Bool.or_false _
        · rcases permQuery <;> rfl
    simp only [List.any_append, head, Bool.or_assoc]

theorem trace_compression_bind {α β : Type} (c1 : OracleComp World α) (c2 : α → OracleComp World β) :
    traceCompression (c1 >>= c2) =
      (do let (a, t1) ← traceCompression c1
          let (b, t2) ← traceCompression (c2 a)
          pure (b, t1 ++ t2)) := by
  induction c1 using OracleComp.inductionOn with
  | pure v =>
    simp only [pure_bind, trace_compression_pure, List.nil_append]
    change traceCompression (c2 v) = (traceCompression (c2 v) >>= fun r => pure r)
    rw [bind_pure]
  | query_bind query next ih =>
    simp only [bind_assoc, trace_compression_query_bind]
    apply congrArg (fun k => (liftM (World.query query) : OracleComp World _) >>= k)
    funext ans
    rw [ih ans]
    simp only [bind_assoc, pure_bind, List.append_assoc]

theorem trace_compression_bound {α : Type} (comp : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound comp budget) :
    PublicQueryBound (traceCompression comp) budget := by
  induction comp using OracleComp.inductionOn generalizing budget with
  | pure _ => trivial
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ ans, PublicQueryBound (next ans) (budget - Oracle.callCost query)) at bounded
    rw [trace_compression_query_bind]
    refine ⟨bounded.1, fun ans => ?_⟩
    have h1 := ih ans (budget - Oracle.callCost query) (bounded.2 ans)
    have h2 : ∀ r : α × List (BitVec COMPRESSION_INPUT_LENGTH),
        PublicQueryBound (match r with | (value, trace) => (pure (value, compressionHead query ++ trace) : OracleComp World _)) 0 :=
      fun ⟨_, _⟩ => trivial
    exact @public_query_bound_bind _ _ (traceCompression (next ans))
      (fun r => match r with | (value, trace) => pure (value, compressionHead query ++ trace))
      (budget - Oracle.callCost query) 0 h1 h2

theorem compression_run_cache_mono (permutation : Perm) {α : Type}
    (comp : OracleComp World α) (cache : CompressionCache) (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation comp cache)) :
    ∀ x v, cache x = some v → result.2 x = some v := by
  induction comp using OracleComp.inductionOn generalizing cache result with
  | pure _ =>
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result; exact fun _ _ h => h
  | query_bind query next ih =>
    rcases query with coins | publicQuery
    · rw [compression_run_private] at reached
      obtain ⟨ans, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      exact ih ans cache result reached
    · rcases publicQuery with input | permQuery
      · rw [compression_run_compress] at reached
        cases hcached : cache input with
        | some ans =>
          rw [hcached] at reached
          exact ih ans cache result reached
        | none =>
          rw [hcached] at reached
          obtain ⟨ans, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
          intro x v hxv
          apply ih ans (cache.cacheQuery input ans) result reached x v
          by_cases heq : x = input
          · subst heq; rw [hcached] at hxv; contradiction
          · rw [QueryCache.cacheQuery_of_ne _ _ heq]; exact hxv
      · rcases permQuery with input | input
        · rw [compression_run_permute] at reached
          exact ih (permutation input) cache result reached
        · rw [compression_run_inverse] at reached
          exact ih (permutation.symm input) cache result reached

/-- If a starting cache contains no bad digest values, then across `budget` public queries
in lazy `compressionRun`, the probability of ever sampling a bad digest value is at most `budget * p`. -/
theorem compression_run_cache_bad_bound (permutation : Perm) (pred : Digest → Bool)
    (p : ENNReal) (hp : prEvent ((fun v : Digest => pred v = true) <$> ($ᵗ Digest)) ≤ p)
    {α : Type} (comp : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound comp budget)
    (cache : CompressionCache) (clean : ∀ x v, cache x = some v → pred v = false) :
    prEvent ((fun res : α × CompressionCache => ∃ x v, res.2 x = some v ∧ pred v = true) <$>
      compressionRun permutation comp cache) ≤ (budget : ENNReal) * p := by
  induction comp using OracleComp.inductionOn generalizing budget cache with
  | pure value =>
    rw [compression_run_pure]
    have h0 : prEvent ((fun res : α × CompressionCache => ∃ x v, res.2 x = some v ∧ pred v = true) <$>
        (pure (value, cache) : ProbComp _)) = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      intro res hres hbad
      simp only [support_pure, Set.mem_singleton_iff] at hres
      subst hres
      obtain ⟨x, v, hxv, hpred⟩ := hbad
      rw [clean x v hxv] at hpred
      exact Bool.noConfusion hpred
    rw [h0]; exact bot_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ ans, PublicQueryBound (next ans) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      apply prEvent_bind_le_of_forall_le_of_support
      intro ans _
      exact ih ans budget (by simpa [Oracle.callCost] using bounded.2 ans) cache clean
    · have hpos : 1 ≤ budget := bounded.1
      have htails : ∀ ans, PublicQueryBound (next ans) (budget - 1) := bounded.2
      have hle : ((budget - 1 : Nat) : ENNReal) * p ≤ (budget : ENNReal) * p := by
        gcongr; exact Nat.sub_le _ _
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases hcached : cache input with
        | some ans =>
          exact (ih ans (budget - 1) (htails ans) cache clean).trans hle
        | none =>
          have hcont : ∀ ans ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ (pred ans = true) →
              prEvent ((fun res : α × CompressionCache => ∃ x v, res.2 x = some v ∧ pred v = true) <$>
                compressionRun permutation (next ans) (cache.cacheQuery input ans)) ≤
              ((budget - 1 : Nat) : ENNReal) * p := by
            intro ans _ hnot
            have hfalse : pred ans = false := Bool.eq_false_iff.mpr hnot
            apply ih ans (budget - 1) (htails ans) (cache.cacheQuery input ans)
            intro x v hxv
            by_cases heq : x = input
            · subst heq
              rw [QueryCache.cacheQuery_self] at hxv
              cases hxv; exact hfalse
            · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hxv
              exact clean x v hxv
          have comb := (prEvent_bind_le_prEvent_add_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun ans => compressionRun permutation (next ans) (cache.cacheQuery input ans))
            (fun ans => pred ans = true)
            (fun res => ∃ x v, res.2 x = some v ∧ pred v = true)
            hcont).trans (add_le_add hp le_rfl)
          refine comb.trans_eq ?_
          rw [show (budget : ENNReal) = 1 + ((budget - 1 : Nat) : ENNReal) by
            rw [← Nat.cast_one, ← Nat.cast_add]; congr 1; omega]
          ring
      · rcases permQuery with input | input
        · rw [compression_run_permute]
          exact (ih (permutation input) (budget - 1) (htails _) cache clean).trans hle
        · rw [compression_run_inverse]
          exact (ih (permutation.symm input) (budget - 1) (htails _) cache clean).trans hle

/-! ### 6. Deterministic trace cleanliness of `evalHybridTranscript` under a clean final cache -/

private theorem hashBlocks_trace_clean (permutation : Perm) (positions : Positions)
    (sHidden : Index → Salt) (blocks : List LeafBlock) (init : Digest) (cache : CompressionCache)
    (res : (Digest × List (BitVec COMPRESSION_INPUT_LENGTH)) × CompressionCache)
    (reached : res ∈ support (compressionRun permutation (traceCompression (hashBlocks blocks init)) cache))
    (initClean : digestHitsUnopened positions sHidden init = false)
    (cacheClean : ∀ x v, res.2 x = some v → digestHitsUnopened positions sHidden v = false) :
    digestHitsUnopened positions sHidden res.1.1 = false ∧
    ∀ x ∈ res.1.2, inputHitsUnopened positions sHidden x = false := by
  induction blocks generalizing init cache res with
  | nil =>
    rw [hashBlocks, trace_compression_pure, compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst res
    exact ⟨initClean, by simp⟩
  | cons block rest ih =>
    rw [hashBlocks] at reached
    erw [trace_compression_query_bind, compression_run_compress] at reached
    have hq : inputHitsUnopened positions sHidden (leafInput init block) = false := by
      rw [inputHitsUnopened_leafInput]; exact initClean
    cases hcached : cache (leafInput init block) with
    | some ans =>
      change BitVec 256 at ans
      rw [hcached] at reached
      dsimp only at reached
      rw [compression_run_bind] at reached
      obtain ⟨⟨⟨out, tr⟩, c'⟩, hrest, hfinal⟩ := (mem_support_bind_iff _ _ _).mp reached
      dsimp only at hfinal
      rw [compression_run_pure] at hfinal
      simp only [support_pure, Set.mem_singleton_iff] at hfinal
      subst res
      have hans : digestHitsUnopened positions sHidden ans = false :=
        cacheClean _ _ (compression_run_cache_mono permutation _ cache _ hrest _ _ hcached)
      have hih := ih ans cache ((out, tr), c') hrest hans cacheClean
      refine ⟨hih.1, ?_⟩
      intro x hx
      simp only [compressionHead, List.singleton_append, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hq
      · exact hih.2 x hx
    | none =>
      rw [hcached] at reached
      dsimp only at reached
      obtain ⟨ans, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      change BitVec 256 at ans
      rw [compression_run_bind] at reached
      obtain ⟨⟨⟨out, tr⟩, c'⟩, hrest, hfinal⟩ := (mem_support_bind_iff _ _ _).mp reached
      dsimp only at hfinal
      rw [compression_run_pure] at hfinal
      simp only [support_pure, Set.mem_singleton_iff] at hfinal
      subst res
      have hans : digestHitsUnopened positions sHidden ans = false :=
        cacheClean _ _ (compression_run_cache_mono permutation _ _ _ hrest _ _ (QueryCache.cacheQuery_self _ _ _))
      have hih := ih ans _ ((out, tr), c') hrest hans cacheClean
      refine ⟨hih.1, ?_⟩
      intro x hx
      simp only [compressionHead, List.singleton_append, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hq
      · exact hih.2 x hx

private theorem evalHybridLeaves_trace_clean (permutation : Perm) (positions : Positions)
    (message : Message) (sOpen sHidden : Index → Salt) (freshInit : Index → Digest)
    (n : Nat) (cache : CompressionCache)
    (res : ((Nat → Digest) × List (BitVec COMPRESSION_INPUT_LENGTH)) × CompressionCache)
    (reached : res ∈ support (compressionRun permutation
      (traceCompression (evalHybridLeaves positions message sOpen freshInit n)) cache))
    (freshClean : ∀ i : Index, digestHitsUnopened positions sHidden (freshInit i) = false)
    (cacheClean : ∀ x v, res.2 x = some v → digestHitsUnopened positions sHidden v = false) :
    (∀ k < n, k < LENGTH → digestHitsUnopened positions sHidden (res.1.1 k) = false) ∧
    ∀ x ∈ res.1.2, inputHitsUnopened positions sHidden x = false := by
  induction n generalizing cache res with
  | zero =>
    rw [evalHybridLeaves, trace_compression_pure, compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst res
    exact ⟨fun k hk => by omega, by simp⟩
  | succ n ih =>
    rw [evalHybridLeaves, trace_compression_bind, compression_run_bind] at reached
    obtain ⟨⟨⟨rest, tr1⟩, c1⟩, h1, h2⟩ := (mem_support_bind_iff _ _ _).mp reached
    dsimp only at h2
    rw [compression_run_bind] at h2
    obtain ⟨⟨⟨leaves2, tr2⟩, c2⟩, h2', hfinal⟩ := (mem_support_bind_iff _ _ _).mp h2
    dsimp only at hfinal
    rw [compression_run_pure] at hfinal
    simp only [support_pure, Set.mem_singleton_iff] at hfinal
    subst res
    have c1Clean : ∀ x v, c1 x = some v → digestHitsUnopened positions sHidden v = false :=
      fun x v hxv => cacheClean x v (compression_run_cache_mono permutation _ c1 _ h2' x v hxv)
    have hih := ih cache ((rest, tr1), c1) h1 c1Clean
    split at h2'
    · rename_i hn
      let idx : Index := ⟨n, hn⟩
      rw [trace_compression_bind, compression_run_bind] at h2'
      obtain ⟨⟨⟨d, trd⟩, cd⟩, hd, hupd⟩ := (mem_support_bind_iff _ _ _).mp h2'
      dsimp only at hupd
      rw [compression_run_bind] at hupd
      obtain ⟨⟨⟨leaves3, tru⟩, cu⟩, hu, hfin2⟩ := (mem_support_bind_iff _ _ _).mp hupd
      dsimp only at hu hfin2
      rw [trace_compression_pure, compression_run_pure] at hu
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hu
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hu
      rw [compression_run_pure] at hfin2
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfin2
      have hdClean : digestHitsUnopened positions sHidden d = false ∧
          ∀ x ∈ trd, inputHitsUnopened positions sHidden x = false := by
        unfold evalHybridLeaf at hd
        split at hd
        · rename_i hopen
          erw [trace_compression_query_bind, compression_run_compress] at hd
          have hq0 : inputHitsUnopened positions sHidden (leafInitInput idx (sOpen idx) (message idx)) = false :=
            inputHitsUnopened_leafInitInput_opened positions sHidden idx hopen (sOpen idx) (message idx)
          cases hcached : c1 (leafInitInput idx (sOpen idx) (message idx)) with
          | some d0 =>
            change BitVec 256 at d0
            rw [hcached] at hd
            dsimp only at hd
            rw [compression_run_bind] at hd
            obtain ⟨⟨⟨d', trtail⟩, c'⟩, htail, hfin3⟩ := (mem_support_bind_iff _ _ _).mp hd
            dsimp only at hfin3
            rw [compression_run_pure] at hfin3
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin3
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfin3
            have hd0 : digestHitsUnopened positions sHidden d0 = false :=
              cacheClean _ _ (compression_run_cache_mono permutation _ c1 _ htail _ _ hcached)
            have hblk := hashBlocks_trace_clean permutation positions sHidden (leafTailBlocks (message idx))
              d0 c1 ((d, trtail), c2) htail hd0 cacheClean
            refine ⟨hblk.1, ?_⟩
            intro x hx
            simp only [compressionHead, List.singleton_append, List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hq0
            · exact hblk.2 x hx
          | none =>
            rw [hcached] at hd
            dsimp only at hd
            obtain ⟨d0, _, hd⟩ := (mem_support_bind_iff _ _ _).mp hd
            change BitVec 256 at d0
            rw [compression_run_bind] at hd
            obtain ⟨⟨⟨d', trtail⟩, c'⟩, htail, hfin3⟩ := (mem_support_bind_iff _ _ _).mp hd
            dsimp only at hfin3
            rw [compression_run_pure] at hfin3
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin3
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfin3
            have hd0 : digestHitsUnopened positions sHidden d0 = false :=
              cacheClean _ _ (compression_run_cache_mono permutation _ _ _ htail _ _ (QueryCache.cacheQuery_self _ _ _))
            have hblk := hashBlocks_trace_clean permutation positions sHidden (leafTailBlocks (message idx))
              d0 _ ((d, trtail), c2) htail hd0 cacheClean
            refine ⟨hblk.1, ?_⟩
            intro x hx
            simp only [compressionHead, List.singleton_append, List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hq0
            · exact hblk.2 x hx
        · exact hashBlocks_trace_clean permutation positions sHidden (leafTailBlocks (message idx))
            (freshInit idx) c1 ((d, trd), c2) hd (freshClean idx) cacheClean
      refine ⟨?_, ?_⟩
      · intro k hk hL
        dsimp only
        by_cases hkn : k = n
        · subst hkn; simpa only [Function.update_self] using hdClean.1
        · rw [Function.update_of_ne hkn]; exact hih.1 k (by omega) hL
      · intro x hx
        simp only [List.append_nil, List.mem_append] at hx
        rcases hx with hx | hx
        · exact hih.2 x hx
        · exact hdClean.2 x hx
    · rename_i hn
      rw [trace_compression_pure, compression_run_pure] at h2'
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2'
      refine ⟨fun k hk hL => hih.1 k (by omega) hL, ?_⟩
      intro x hx
      simp only [List.append_nil] at hx
      exact hih.2 x hx

private theorem evalParents_trace_clean (permutation : Perm) (positions : Positions)
    (sHidden : Index → Salt) (leaves : Nat → Digest) (k : Nat) (hk : k ≤ LENGTH - 1)
    (cache : CompressionCache)
    (res : ((Nat → Digest) × List (BitVec COMPRESSION_INPUT_LENGTH)) × CompressionCache)
    (reached : res ∈ support (compressionRun permutation (traceCompression (evalParents leaves k)) cache))
    (leavesClean : ∀ i < LENGTH, digestHitsUnopened positions sHidden (leaves i) = false)
    (cacheClean : ∀ x v, res.2 x = some v → digestHitsUnopened positions sHidden v = false) :
    (∀ node, LENGTH - k ≤ node → node < 2 * LENGTH → digestHitsUnopened positions sHidden (res.1.1 node) = false) ∧
    ∀ x ∈ res.1.2, inputHitsUnopened positions sHidden x = false := by
  induction k generalizing cache res with
  | zero =>
    rw [evalParents, trace_compression_pure, compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst res
    refine ⟨?_, by simp⟩
    intro node hlo hhi
    simp only [Nat.sub_zero] at hlo
    dsimp only
    rw [if_pos ⟨hlo, hhi⟩]
    exact leavesClean (node - LENGTH) (by omega)
  | succ k ih =>
    rw [evalParents, trace_compression_bind, compression_run_bind] at reached
    obtain ⟨⟨⟨heap, tr1⟩, c1⟩, h1, h2⟩ := (mem_support_bind_iff _ _ _).mp reached
    dsimp only at h2
    rw [compression_run_bind] at h2
    obtain ⟨⟨⟨heap2, tr2⟩, c2⟩, h2', hfinal⟩ := (mem_support_bind_iff _ _ _).mp h2
    dsimp only at hfinal
    rw [compression_run_pure] at hfinal
    simp only [support_pure, Set.mem_singleton_iff] at hfinal
    subst res
    have c1Clean : ∀ x v, c1 x = some v → digestHitsUnopened positions sHidden v = false :=
      fun x v hxv => cacheClean x v (compression_run_cache_mono permutation _ c1 _ h2' x v hxv)
    have hih := ih (by omega) cache ((heap, tr1), c1) h1 c1Clean
    let node := LENGTH - 1 - k
    have h2l : LENGTH - k ≤ 2 * node ∧ 2 * node < 2 * LENGTH := by dsimp only [node]; omega
    have hleftClean : digestHitsUnopened positions sHidden (heap (2 * node)) = false :=
      hih.1 (2 * node) h2l.1 h2l.2
    have hqClean : inputHitsUnopened positions sHidden (padInput (heap (2 * node + 1) ++ heap (2 * node))) = false := by
      rw [inputHitsUnopened_padInput]; exact hleftClean
    rw [trace_compression_bind, compression_run_bind] at h2'
    obtain ⟨⟨⟨p, trp⟩, cp⟩, hp, hupd⟩ := (mem_support_bind_iff _ _ _).mp h2'
    dsimp only at hupd
    rw [compression_run_bind] at hupd
    obtain ⟨⟨⟨heap3, tru⟩, cu⟩, hu, hfin2⟩ := (mem_support_bind_iff _ _ _).mp hupd
    dsimp only at hu hfin2
    rw [trace_compression_pure, compression_run_pure] at hu
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hu
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hu
    rw [compression_run_pure] at hfin2
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfin2
    have hpClean : digestHitsUnopened positions sHidden p = false ∧
        ∀ x ∈ trp, inputHitsUnopened positions sHidden x = false := by
      rw [hashParent] at hp
      erw [trace_compression_query_bind, compression_run_compress] at hp
      cases hcached : c1 (padInput (heap (2 * node + 1) ++ heap (2 * node))) with
      | some ans =>
        change BitVec 256 at ans
        rw [hcached] at hp
        dsimp only at hp
        rw [compression_run_bind] at hp
        obtain ⟨⟨⟨ans', tr'⟩, c'⟩, htail, hfin3⟩ := (mem_support_bind_iff _ _ _).mp hp
        dsimp only at htail hfin3
        erw [trace_compression_pure, compression_run_pure] at htail
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htail
        rw [compression_run_pure] at hfin3
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin3
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfin3
        refine ⟨cacheClean _ _ hcached, ?_⟩
        intro x hx
        simp only [compressionHead, List.append_nil, List.mem_singleton] at hx
        subst hx; exact hqClean
      | none =>
        rw [hcached] at hp
        dsimp only at hp
        obtain ⟨ans, _, hp⟩ := (mem_support_bind_iff _ _ _).mp hp
        change BitVec 256 at ans
        rw [compression_run_bind] at hp
        obtain ⟨⟨⟨ans', tr'⟩, c'⟩, htail, hfin3⟩ := (mem_support_bind_iff _ _ _).mp hp
        dsimp only at htail hfin3
        erw [trace_compression_pure, compression_run_pure] at htail
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htail
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htail
        rw [compression_run_pure] at hfin3
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin3
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfin3
        refine ⟨cacheClean _ _ (QueryCache.cacheQuery_self _ _ _), ?_⟩
        intro x hx
        simp only [compressionHead, List.append_nil, List.mem_singleton] at hx
        subst hx; exact hqClean
    refine ⟨?_, ?_⟩
    · intro m hlo hhi
      dsimp only
      have hnodeEq : LENGTH - 1 - k = node := rfl
      rw [hnodeEq]
      by_cases hm : m = node
      · subst hm; simpa only [Function.update_self] using hpClean.1
      · rw [Function.update_of_ne hm]; exact hih.1 m (by dsimp only [node] at hm; omega) hhi
    · intro x hx
      simp only [List.append_nil, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hih.2 x hx
      · exact hpClean.2 x hx

attribute [local irreducible] evalHybridLeaves evalParents

theorem eval_hybrid_transcript_bound (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) :
    PublicQueryBound (evalHybridTranscript positions message salt freshInit) (5 * LENGTH) := by
  unfold evalHybridTranscript
  have h1 := eval_hybrid_leaves_bound positions message salt freshInit LENGTH
  have h2 (leaves : Nat → Digest) :
      PublicQueryBound (do
        let heap ← evalParents leaves (LENGTH - 1)
        pure (heap 1, referenceOpening heap salt positions)) (LENGTH - 1) := by
    rw [← Nat.add_zero (LENGTH - 1)]
    exact public_query_bound_bind (eval_parents_bound leaves (LENGTH - 1)) (fun _ => trivial)
  exact (public_query_bound_bind h1 h2).mono (by clear * -; omega)

theorem fixed_eval_hybrid_transcript (oracle : Oracle) (positions : Positions)
    (message : Message) (salt : Index → Salt) (freshInit : Index → Digest) :
    fixedOracleRun oracle (evalHybridTranscript positions message salt freshInit) =
      pure (hybridTranscript oracle.compression positions message salt freshInit) := by
  unfold evalHybridTranscript
  rw [fixed_oracle_run_bind, fixed_eval_hybrid_leaves, pure_bind,
    fixed_oracle_run_bind, fixed_eval_parents oracle _ (LENGTH - 1) (le_refl _), pure_bind,
    fixed_oracle_run_pure]
  have hleaves : (fun i => if h : i < LENGTH ∧ i < LENGTH then
      hybridLeafDigest oracle.compression positions message salt freshInit ⟨i, h.2⟩ else 0) =
      (fun i => if inside : i < LENGTH then
        hybridLeafDigest oracle.compression positions message salt freshInit ⟨i, inside⟩ else 0) := by
    funext i; by_cases hi : i < LENGTH <;> simp [hi]
  have h1 : LENGTH - (LENGTH - 1) = 1 := by decide
  have hroot : (if LENGTH - (LENGTH - 1) ≤ 1 ∧ 1 < 2 * LENGTH then
      referenceHeap oracle.compression LENGTH (fun i => if h : i < LENGTH ∧ i < LENGTH then
        hybridLeafDigest oracle.compression positions message salt freshInit ⟨i, h.2⟩ else 0) 1 else 0) =
      hybridHeap oracle.compression positions message salt freshInit 1 := by
    rw [h1, hleaves, if_pos (by decide)]; rfl
  have hopen : referenceOpening
      (fun node => if LENGTH - (LENGTH - 1) ≤ node ∧ node < 2 * LENGTH then
        referenceHeap oracle.compression LENGTH (fun i => if h : i < LENGTH ∧ i < LENGTH then
          hybridLeafDigest oracle.compression positions message salt freshInit ⟨i, h.2⟩ else 0) node else 0)
      salt positions =
      referenceOpening (hybridHeap oracle.compression positions message salt freshInit) salt positions := by
    unfold referenceOpening referenceOpeningByte
    apply List.map_congr_left
    intro offset hoff
    rw [List.mem_range] at hoff
    dsimp only
    by_cases hbatch : positions.card = BATCH
    · rw [if_pos hbatch, if_pos hbatch]
      by_cases hrec : offset < 71680
      · rw [if_pos hrec, if_pos hrec]
        by_cases hsalt : offset % 560 < 16
        · rw [if_pos hsalt, if_pos hsalt]
        · rw [if_neg hsalt, if_neg hsalt]
          have hlevel : (offset % 560 - 16) / 32 < LOG_LENGTH := by change _ < 24; omega
          let idx : Index := ⟨openingIndex positions (offset / 560), opening_index_bound positions (offset / 560)⟩
          have hb := opening_sibling_bounds idx ((offset % 560 - 16) / 32) hlevel
          rw [h1, if_pos ⟨hb.1, hb.2⟩, hleaves]
          rfl
      · rw [if_neg hrec, if_neg hrec]
        have hoff_lt : offset < 75776 := by
          unfold openingProofBytes at hoff
          rw [if_pos hbatch] at hoff
          exact hoff
        have hcap_bd : 1 ≤ 128 + (offset - 71680) / 32 ∧ 128 + (offset - 71680) / 32 < 2 * LENGTH := by
          unfold LENGTH LOG_LENGTH; omega
        rw [h1, if_pos hcap_bd, hleaves]
        rfl
    · rw [if_neg hbatch, if_neg hbatch]
      by_cases hsalt : offset % 784 < 16
      · rw [if_pos hsalt, if_pos hsalt]
      · rw [if_neg hsalt, if_neg hsalt]
        have hlevel : (offset % 784 - 16) / 32 < LOG_LENGTH := by change _ < 24; omega
        let idx : Index := ⟨openingIndex positions (offset / 784), opening_index_bound positions (offset / 784)⟩
        have hb := opening_sibling_bounds idx ((offset % 784 - 16) / 32) hlevel
        rw [h1, if_pos ⟨hb.1, hb.2⟩, hleaves]
        rfl
  congr 1
  exact Prod.ext hroot hopen

theorem fixed_eval_hybrid_observe {α : Type} (oracle : Oracle) (positions : Positions)
    (message : Message) (salt : Index → Salt) (freshInit : Index → Digest)
    (observe : Commitment → Proof → OracleComp World α) :
    fixedOracleRun oracle (evalHybridObserve positions message salt freshInit observe) =
      observeHybridTranscript oracle positions message salt freshInit observe := by
  rw [evalHybridObserve, fixed_oracle_run_bind, fixed_eval_hybrid_transcript, pure_bind]
  rfl

theorem evalHybridTranscript_trace_clean (permutation : Perm) (positions : Positions)
    (message : Message) (sOpen sHidden : Index → Salt) (freshInit : Index → Digest)
    (cache : CompressionCache)
    (res : ((Commitment × Proof) × List (BitVec COMPRESSION_INPUT_LENGTH)) × CompressionCache)
    (reached : res ∈ support (compressionRun permutation
      (traceCompression (evalHybridTranscript positions message sOpen freshInit)) cache))
    (freshClean : ∀ i : Index, digestHitsUnopened positions sHidden (freshInit i) = false)
    (cacheClean : ∀ x v, res.2 x = some v → digestHitsUnopened positions sHidden v = false) :
    res.1.2.any (inputHitsUnopened positions sHidden) = false := by
  unfold evalHybridTranscript at reached
  rw [trace_compression_bind, compression_run_bind] at reached
  obtain ⟨⟨⟨leaves, tr1⟩, c1⟩, h1, h2⟩ := (mem_support_bind_iff _ _ _).mp reached
  dsimp only at h2
  rw [compression_run_bind] at h2
  obtain ⟨⟨⟨out2, tr2⟩, c2⟩, h2', hfinal⟩ := (mem_support_bind_iff _ _ _).mp h2
  dsimp only at hfinal
  rw [compression_run_pure] at hfinal
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst res
  have c1Clean : ∀ x v, c1 x = some v → digestHitsUnopened positions sHidden v = false :=
    fun x v hxv => cacheClean x v (compression_run_cache_mono permutation _ c1 _ h2' x v hxv)
  have hleaves := evalHybridLeaves_trace_clean permutation positions message sOpen sHidden freshInit
    LENGTH cache ((leaves, tr1), c1) h1 freshClean c1Clean
  rw [trace_compression_bind, compression_run_bind] at h2'
  obtain ⟨⟨⟨heap, trp⟩, cp⟩, hp, hfin⟩ := (mem_support_bind_iff _ _ _).mp h2'
  dsimp only at hfin
  rw [compression_run_bind] at hfin
  obtain ⟨⟨⟨out3, tr3⟩, c3⟩, h3, hfin2⟩ := (mem_support_bind_iff _ _ _).mp hfin
  dsimp only at h3 hfin2
  rw [trace_compression_pure, compression_run_pure] at h3
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h3
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
  rw [compression_run_pure] at hfin2
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfin2
  have hparents := evalParents_trace_clean permutation positions sHidden leaves (LENGTH - 1) (le_refl _)
    c1 ((heap, trp), c2) hp (fun i hi => hleaves.1 i hi hi) cacheClean
  simp only [List.append_nil, List.any_eq_false]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · simp [hleaves.2 x hx]
  · simp [hparents.2 x hx]

attribute [local irreducible] evalHybridTranscript

/-! ### 7. Main theorem: `Real(m)` vs `Hybrid(m)` TV distance -/

/-- Phase 1 hitting bound: probability that honest hybrid tree evaluation makes any query
marked by `marksUnopened positions sHidden`. -/
theorem phase1_hit_bound (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (message : Message) (positions : Positions) (sOpen : Index → Salt) :
    prEvent ((fun res : ((Commitment × Proof) × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt) =>
        res.1.2.any (inputHitsUnopened positions res.2) = true) <$>
      (do let sHidden ← $ᵗ (Index → Salt)
          let freshInit ← $ᵗ (Index → Digest)
          let table ← $ᵗ Compression
          let tr ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (traceCompression (evalHybridTranscript positions message sOpen freshInit))
          pure (tr, sHidden))) ≤
      (keys.card : ENNReal) / 2 ^ 128 + (6 * (LENGTH * LENGTH) : ENNReal) / 2 ^ 192 := by
  classical
  have stepLazy :
      𝒟[do let sHidden ← $ᵗ (Index → Salt)
           let freshInit ← $ᵗ (Index → Digest)
           let table ← $ᵗ Compression
           let tr ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
             (traceCompression (evalHybridTranscript positions message sOpen freshInit))
           pure (tr, sHidden)] =
      𝒟[do let sHidden ← $ᵗ (Index → Salt)
           let freshInit ← $ᵗ (Index → Digest)
           let run ← compressionRun permutation
             (traceCompression (evalHybridTranscript positions message sOpen freshInit)) cache
           pure (run.1, sHidden)] := by
    apply _root_.evalDist_bind_congr; intro sHidden
    apply _root_.evalDist_bind_congr; intro freshInit
    have heq := compression_sampling_equivalence permutation
      (traceCompression (evalHybridTranscript positions message sOpen freshInit)) cache
    have hmap := (EvalDistEq.of_evalDist_eq heq).map (fun tr => (tr, sHidden))
    have hsym := hmap.evalDist_eq.symm
    simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_def] at hsym
    exact hsym
  rw [(EvalDistEq.of_evalDist_eq stepLazy).prEvent_eq]
  -- Pull out `cacheBad`: some cached value in `keys` hits an unopened `(sHidden i, leafTag i)`.
  let cacheBad (sHidden : Index → Salt) : Prop :=
    ∃ x ∈ keys, ∃ v, cache x = some v ∧ digestHitsUnopened positions sHidden v = true
  have hCacheBadProb : prEvent (cacheBad <$> ($ᵗ (Index → Salt))) ≤ (keys.card : ENNReal) / 2 ^ 128 := by
    have hinc : prEvent (cacheBad <$> ($ᵗ (Index → Salt))) ≤
        prEvent ((fun sHidden => ∃ x ∈ keys, match cache x with
          | some v => digestHitsUnopened positions sHidden v = true
          | none => False) <$> ($ᵗ (Index → Salt))) := by
      apply prEvent_mono_of_support
      intro sHidden _ ⟨x, hx, v, hxv, hhit⟩
      exact ⟨x, hx, by rw [hxv]; exact hhit⟩
    refine hinc.trans ((prEvent_exists_finset_le keys ($ᵗ (Index → Salt)) _).trans ?_)
    calc ∑ x ∈ keys, prEvent ((fun sHidden => match cache x with
            | some v => digestHitsUnopened positions sHidden v = true
            | none => False) <$> ($ᵗ (Index → Salt)))
        ≤ ∑ _x ∈ keys, (1 / (2 ^ 128 : ENNReal)) := by
          apply Finset.sum_le_sum; intro x _
          cases hcx : cache x with
          | none =>
            dsimp only
            have h0 : prEvent ((fun _ : Index → Salt => False) <$> ($ᵗ (Index → Salt))) = 0 := by
              apply prEvent_eq_zero_of_forall_mem_support
              intro _ _ h; exact h
            rw [h0]; exact bot_le
          | some v => exact digest_hits_unopened_salt_prob positions v
      _ = (keys.card : ENNReal) / 2 ^ 128 := by simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hGoodSalt : ∀ sHidden ∈ support ($ᵗ (Index → Salt)), ¬ cacheBad sHidden →
      prEvent ((fun res : ((Commitment × Proof) × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt) =>
          res.1.2.any (inputHitsUnopened positions res.2) = true) <$>
        (do let freshInit ← $ᵗ (Index → Digest)
            let run ← compressionRun permutation
              (traceCompression (evalHybridTranscript positions message sOpen freshInit)) cache
            pure (run.1, sHidden))) ≤ (6 * (LENGTH * LENGTH) : ENNReal) / 2 ^ 192 := by
    intro sHidden _ hnoCacheBad
    have hCacheClean : ∀ x v, cache x = some v → digestHitsUnopened positions sHidden v = false := by
      intro x v hxv
      by_contra hne
      have htrue : digestHitsUnopened positions sHidden v = true := Bool.eq_true_of_not_eq_false hne
      exact hnoCacheBad ⟨x, covered x (by rw [hxv]; simp), v, hxv, htrue⟩
    -- Pull out `freshBad`: some coordinate of `freshInit` satisfies `digestHitsUnopened`.
    let freshBad (freshInit : Index → Digest) : Prop :=
      ∃ i : Index, digestHitsUnopened positions sHidden (freshInit i) = true
    have hFreshBadProb : prEvent (freshBad <$> ($ᵗ (Index → Digest))) ≤
        (LENGTH * LENGTH : ENNReal) / 2 ^ 192 := by
      have hu := prEvent_exists_finset_le (Finset.univ : Finset Index) ($ᵗ (Index → Digest))
        (fun i fi => digestHitsUnopened positions sHidden (fi i) = true)
      have heq : (fun fi : Index → Digest => ∃ i ∈ (Finset.univ : Finset Index),
          digestHitsUnopened positions sHidden (fi i) = true) = freshBad := by funext fi; simp [freshBad]
      rw [heq] at hu
      refine hu.trans ?_
      calc ∑ i : Index, prEvent ((fun fi : Index → Digest =>
              digestHitsUnopened positions sHidden (fi i) = true) <$> ($ᵗ (Index → Digest)))
          ≤ ∑ _i : Index, ((LENGTH : ENNReal) / 2 ^ 192) := by
            apply Finset.sum_le_sum; intro i _
            have hmarg := (EvalDistEq.of_evalDist_eq (uniform_coordinate_distribution (Domain := Index) (Range := Digest) i)).prEvent_eq
              (fun v => digestHitsUnopened positions sHidden v = true)
            simp only [prEvent_map, Function.comp_def] at hmarg
            rw [hmarg]
            exact digest_hits_unopened_uniform_prob positions sHidden
        _ = (LENGTH * LENGTH : ENNReal) / 2 ^ 192 := by
            simp [Finset.sum_const, nsmul_eq_mul, Index, mul_div_assoc]
    have hGoodFresh : ∀ freshInit ∈ support ($ᵗ (Index → Digest)), ¬ freshBad freshInit →
        prEvent ((fun res : ((Commitment × Proof) × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt) =>
            res.1.2.any (inputHitsUnopened positions res.2) = true) <$>
          (do let run ← compressionRun permutation
                (traceCompression (evalHybridTranscript positions message sOpen freshInit)) cache
              pure (run.1, sHidden))) ≤ (5 * (LENGTH * LENGTH) : ENNReal) / 2 ^ 192 := by
      intro freshInit _ hnoFresh
      have hFreshClean : ∀ i : Index, digestHitsUnopened positions sHidden (freshInit i) = false := by
        intro i; by_contra hne
        exact hnoFresh ⟨i, Bool.eq_true_of_not_eq_false hne⟩
      have hmono :
          prEvent ((fun res : ((Commitment × Proof) × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt) =>
              res.1.2.any (inputHitsUnopened positions res.2) = true) <$>
            (do let run ← compressionRun permutation
                  (traceCompression (evalHybridTranscript positions message sOpen freshInit)) cache
                pure (run.1, sHidden))) ≤
          prEvent ((fun run : ((Commitment × Proof) × List (BitVec COMPRESSION_INPUT_LENGTH)) × CompressionCache =>
              ∃ x v, run.2 x = some v ∧ digestHitsUnopened positions sHidden v = true) <$>
            compressionRun permutation
              (traceCompression (evalHybridTranscript positions message sOpen freshInit)) cache) := by
        simp only [bind_pure_comp, prEvent_map, Function.comp_def]
        apply prEvent_mono_of_support
        intro run hrun hhit
        by_contra hnone
        push Not at hnone
        have hclean : ∀ x v, run.2 x = some v → digestHitsUnopened positions sHidden v = false :=
          fun x v hxv => Bool.eq_false_iff.mpr (hnone x v hxv)
        have hfalse := evalHybridTranscript_trace_clean permutation positions message sOpen sHidden
          freshInit cache run hrun hFreshClean hclean
        rw [hfalse] at hhit
        exact Bool.noConfusion hhit
      refine hmono.trans ?_
      have hb := compression_run_cache_bad_bound permutation (digestHitsUnopened positions sHidden)
        ((LENGTH : ENNReal) / 2 ^ 192) (digest_hits_unopened_uniform_prob positions sHidden)
        (traceCompression (evalHybridTranscript positions message sOpen freshInit))
        (5 * LENGTH) (trace_compression_bound _ _ (eval_hybrid_transcript_bound positions message sOpen freshInit))
        cache hCacheClean
      refine hb.trans_eq ?_
      rw [← mul_div_assoc]
      exact congrArg (· / (2 ^ 192 : ENNReal)) (by push_cast; ring)
    have hcomb := (prEvent_bind_le_prEvent_add_of_support ($ᵗ (Index → Digest))
      (fun freshInit => do
        let run ← compressionRun permutation
          (traceCompression (evalHybridTranscript positions message sOpen freshInit)) cache
        pure (run.1, sHidden))
      freshBad _ hGoodFresh).trans (add_le_add hFreshBadProb le_rfl)
    refine hcomb.trans_eq ?_
    rw [← ENNReal.add_div]
    exact congrArg (· / (2 ^ 192 : ENNReal)) (by ring)
  exact (prEvent_bind_le_prEvent_add_of_support ($ᵗ (Index → Salt)) _ cacheBad _ hGoodSalt).trans
    (add_le_add hCacheBadProb le_rfl)

/-- Main Step B theorem: replacing all unopened Call 0 outputs with independent uniform
256-bit digests changes the adversary's observation by at most `3*budget/2^128 + 6*N^2/2^192`. -/
theorem reference_vs_hybrid_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (budget : Nat) (keysBound : keys.card ≤ budget)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α)
    (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    measureTVDist
      (referenceObservation permutation cache message positions observe)
      (hybridObservation permutation cache message positions observe) ≤
      ((3 * budget : Nat) : ℝ) / 2 ^ 128 + (6 * (LENGTH * LENGTH) : ℝ) / 2 ^ 192 := by
  classical
  -- Step 1: Rewrite both `Real(m)` and `Hybrid(m)` on a common probability space
  -- `(sOpen, sHidden, freshInit, table)`.
  let realJoint : ProbComp α := do
    let sOpen ← $ᵗ (Index → Salt)
    let sHidden ← $ᵗ (Index → Salt)
    let freshInit ← $ᵗ (Index → Digest)
    let table ← $ᵗ Compression
    let s := combineSalts positions sOpen sHidden
    let table' := reprogramList message s freshInit (unopenedList positions) table
    observeTranscript ⟨tableExtending cache table', permutation⟩ message s positions observe
  let midJoint : ProbComp α := do
    let sOpen ← $ᵗ (Index → Salt)
    let sHidden ← $ᵗ (Index → Salt)
    let freshInit ← $ᵗ (Index → Digest)
    let table ← $ᵗ Compression
    let s := combineSalts positions sOpen sHidden
    let table' := reprogramList message s freshInit (unopenedList positions) table
    fixedOracleRun ⟨tableExtending cache table', permutation⟩
      (evalHybridObserve positions message sOpen freshInit observe)
  let hybridJoint : ProbComp α := do
    let sOpen ← $ᵗ (Index → Salt)
    let sHidden ← $ᵗ (Index → Salt)
    let freshInit ← $ᵗ (Index → Digest)
    let table ← $ᵗ Compression
    fixedOracleRun ⟨tableExtending cache table, permutation⟩
      (evalHybridObserve positions message sOpen freshInit observe)
  have hRealEq : 𝒟[referenceObservation permutation cache message positions observe] = 𝒟[realJoint] := by
    unfold referenceObservation realJoint
    trans 𝒟[do let salt ← $ᵗ (Index → Salt)
                let table ← $ᵗ Compression
                observeTranscript ⟨tableExtending cache table, permutation⟩ message salt positions observe]
    · exact distribution_bind_comm _ _ _
    · rw [← combine_salts_uniform positions]
      apply _root_.evalDist_bind_congr; intro sOpen
      apply _root_.evalDist_bind_congr; intro sHidden
      exact (reprogramList_uniform message (combineSalts positions sOpen sHidden)
        (unopenedList positions) (unopenedList_nodup positions) (fun table =>
          observeTranscript ⟨tableExtending cache table, permutation⟩ message
            (combineSalts positions sOpen sHidden) positions observe)).symm
  have hHybridEq : 𝒟[hybridObservation permutation cache message positions observe] = 𝒟[hybridJoint] := by
    unfold hybridObservation hybridObservationForSalt hybridJoint
    rw [← combine_salts_uniform positions]
    apply _root_.evalDist_bind_congr; intro sOpen
    apply _root_.evalDist_bind_congr; intro sHidden
    trans 𝒟[do let freshInit ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                observeHybridTranscript ⟨tableExtending cache table, permutation⟩ positions message
                  (combineSalts positions sOpen sHidden) freshInit observe]
    · exact distribution_bind_comm _ _ _
    · apply _root_.evalDist_bind_congr; intro freshInit
      apply _root_.evalDist_bind_congr; intro table
      rw [fixed_eval_hybrid_observe]
      unfold observeHybridTranscript
      rw [hybridTranscript_combine]
  -- Step 2: Bound `d(realJoint, midJoint) ≤ keys.card / 2^128` via `cacheHitsUnopened`.
  have hRealMid : measureTVDist realJoint midJoint ≤ ((keys.card : ENNReal) / 2 ^ 128).toReal := by
    unfold realJoint midJoint
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Salt)) _ _ (by positivity)
    intro sOpen
    refine (measureTVDist_bind_left_le_prEvent_of_evalDistEq ($ᵗ (Index → Salt)) _ _
      (fun sHidden => cacheHitsUnopened cache positions message (combineSalts positions sOpen sHidden)) ?_).trans ?_
    · intro sHidden hnoHit
      apply EvalDistEq.of_evalDist_eq
      apply _root_.evalDist_bind_congr; intro freshInit
      apply _root_.evalDist_bind_congr; intro table
      rw [fixed_eval_hybrid_observe]
      unfold observeTranscript observeHybridTranscript
      dsimp only
      rw [reprogram_transcript_eq_hybrid cache positions message (combineSalts positions sOpen sHidden)
        freshInit table hnoHit, hybridTranscript_combine]
    · apply ENNReal.toReal_mono (by finiteness)
      have hinc :
          prEvent ((fun sHidden => cacheHitsUnopened cache positions message (combineSalts positions sOpen sHidden)) <$> ($ᵗ (Index → Salt))) ≤
          prEvent ((fun sHidden => ∃ x ∈ keys, inputHitsUnopened positions sHidden x = true) <$> ($ᵗ (Index → Salt))) := by
        apply prEvent_mono_of_support
        intro sHidden _ ⟨i, hi, hne⟩
        refine ⟨leafInitInput i (combineSalts positions sOpen sHidden i) (message i), covered _ hne, ?_⟩
        rw [← inputHitsUnopened_combine positions sOpen sHidden]
        exact inputHitsUnopened_leafInitInput_unopened positions (combineSalts positions sOpen sHidden) i hi (message i)
      refine hinc.trans ((prEvent_exists_finset_le keys ($ᵗ (Index → Salt))
        (fun x sHidden => inputHitsUnopened positions sHidden x = true)).trans ?_)
      calc ∑ x ∈ keys, prEvent ((fun sHidden => inputHitsUnopened positions sHidden x = true) <$> ($ᵗ (Index → Salt)))
          ≤ ∑ _x ∈ keys, (1 / (2 ^ 128 : ENNReal)) :=
            Finset.sum_le_sum (fun x _ => input_hits_unopened_salt_prob positions x)
        _ = (keys.card : ENNReal) / 2 ^ 128 := by simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  -- Step 3: Bound `d(hybridJoint, midJoint)` via `oracle_change_distance_le_hit` + Phase 1 + Phase 2.
  have hHybridMid : measureTVDist hybridJoint midJoint ≤
      ((keys.card : ENNReal) / 2 ^ 128 + (6 * (LENGTH * LENGTH) : ENNReal) / 2 ^ 192 +
        (budget : ENNReal) / 2 ^ 128).toReal := by
    unfold hybridJoint midJoint
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Salt)) _ _ (by positivity)
    intro sOpen
    have hAvg : measureTVDist
        (do let sHidden ← $ᵗ (Index → Salt)
            let freshInit ← $ᵗ (Index → Digest)
            let table ← $ᵗ Compression
            fixedOracleRun ⟨tableExtending cache table, permutation⟩
              (evalHybridObserve positions message sOpen freshInit observe))
        (do let sHidden ← $ᵗ (Index → Salt)
            let freshInit ← $ᵗ (Index → Digest)
            let table ← $ᵗ Compression
            let s := combineSalts positions sOpen sHidden
            let table' := reprogramList message s freshInit (unopenedList positions) table
            fixedOracleRun ⟨tableExtending cache table', permutation⟩
              (evalHybridObserve positions message sOpen freshInit observe)) ≤
        (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
          (do let sHidden ← $ᵗ (Index → Salt)
              let freshInit ← $ᵗ (Index → Digest)
              let table ← $ᵗ Compression
              flaggedRun ⟨tableExtending cache table, permutation⟩ (marksUnopened positions sHidden)
                (evalHybridObserve positions message sOpen freshInit observe)))).toReal := by
      apply distance_bind_le_averaged_bad ($ᵗ (Index → Salt)) _ _ _
      intro sHidden
      apply distance_bind_le_averaged_bad ($ᵗ (Index → Digest)) _ _ _
      intro freshInit
      apply distance_bind_le_averaged_bad ($ᵗ Compression) _ _ _
      intro table
      apply oracle_change_distance_le_hit
      intro query hunmarked
      rw [← marksUnopened_combine positions sOpen sHidden] at hunmarked
      exact reprogram_agrees_outside permutation cache positions message
        (combineSalts positions sOpen sHidden) freshInit table query hunmarked
    refine hAvg.trans (ENNReal.toReal_mono (by finiteness) ?_)
    -- Convert `flaggedRun` to `traceCompression` and split trace into `tr1 ++ tr2`!
    have hTraceEq :
        𝒟[do let sHidden ← $ᵗ (Index → Salt)
             let freshInit ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             flaggedRun ⟨tableExtending cache table, permutation⟩ (marksUnopened positions sHidden)
               (evalHybridObserve positions message sOpen freshInit observe)] =
        𝒟[do let sHidden ← $ᵗ (Index → Salt)
             let freshInit ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
               (traceCompression (evalHybridTranscript positions message sOpen freshInit))
             let tr2 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
               (traceCompression (observe tr1.1.1 tr1.1.2))
             pure (tr2.1, (), tr1.2.any (inputHitsUnopened positions sHidden) ||
               tr2.2.any (inputHitsUnopened positions sHidden))] := by
      apply _root_.evalDist_bind_congr; intro sHidden
      apply _root_.evalDist_bind_congr; intro freshInit
      apply _root_.evalDist_bind_congr; intro table
      rw [marksUnopened, flagged_run_trace_pred, evalHybridObserve, trace_compression_bind,
        fixed_oracle_run_bind]
      simp only [Bool.false_or, map_bind, fixed_oracle_run_bind, map_pure, pure_bind,
        fixed_oracle_run_pure, List.any_append]
    rw [(EvalDistEq.of_evalDist_eq hTraceEq).prEvent_eq]
    -- Split `tr1.any || tr2.any` by union bound (`prEvent_or_le` via `tsum` / `prEvent_bind_le_prEvent_add`)
    have hSplit :
        prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
          (do let sHidden ← $ᵗ (Index → Salt)
              let freshInit ← $ᵗ (Index → Digest)
              let table ← $ᵗ Compression
              let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                (traceCompression (evalHybridTranscript positions message sOpen freshInit))
              let tr2 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                (traceCompression (observe tr1.1.1 tr1.1.2))
              pure (tr2.1, (), tr1.2.any (inputHitsUnopened positions sHidden) ||
                tr2.2.any (inputHitsUnopened positions sHidden)))) ≤
        prEvent ((fun res : ((Commitment × Proof) × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt) =>
            res.1.2.any (inputHitsUnopened positions res.2) = true) <$>
          (do let sHidden ← $ᵗ (Index → Salt)
              let freshInit ← $ᵗ (Index → Digest)
              let table ← $ᵗ Compression
              let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                (traceCompression (evalHybridTranscript positions message sOpen freshInit))
              pure (tr1, sHidden))) +
        prEvent ((fun res : (α × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt) =>
            res.1.2.any (inputHitsUnopened positions res.2) = true) <$>
          (do let freshInit ← $ᵗ (Index → Digest)
              let table ← $ᵗ Compression
              let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                (traceCompression (evalHybridTranscript positions message sOpen freshInit))
              let tr2 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                (traceCompression (observe tr1.1.1 tr1.1.2))
              let sHidden ← $ᵗ (Index → Salt)
              pure (tr2, sHidden))) := by
      -- Prove via `prEvent_bind_le_prEvent_add` on the joint distribution of `(tr1, tr2, sHidden)`.
      let joint : ProbComp (((Commitment × Proof) × List (BitVec COMPRESSION_INPUT_LENGTH)) ×
          (α × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt)) := do
        let sHidden ← $ᵗ (Index → Salt)
        let freshInit ← $ᵗ (Index → Digest)
        let table ← $ᵗ Compression
        let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
          (traceCompression (evalHybridTranscript positions message sOpen freshInit))
        let tr2 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
          (traceCompression (observe tr1.1.1 tr1.1.2))
        pure (tr1, tr2, sHidden)
      have hLHS :
          prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
            (do let sHidden ← $ᵗ (Index → Salt)
                let freshInit ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                  (traceCompression (evalHybridTranscript positions message sOpen freshInit))
                let tr2 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                  (traceCompression (observe tr1.1.1 tr1.1.2))
                pure (tr2.1, (), tr1.2.any (inputHitsUnopened positions sHidden) ||
                  tr2.2.any (inputHitsUnopened positions sHidden)))) =
          prEvent ((fun r => r.1.2.any (inputHitsUnopened positions r.2.2) = true ∨
              r.2.1.2.any (inputHitsUnopened positions r.2.2) = true) <$> joint) := by
        have hmap : 𝒟[(fun r => (r.2.1.1, (), r.1.2.any (inputHitsUnopened positions r.2.2) ||
            r.2.1.2.any (inputHitsUnopened positions r.2.2))) <$> joint] =
            𝒟[do let sHidden ← $ᵗ (Index → Salt)
                 let freshInit ← $ᵗ (Index → Digest)
                 let table ← $ᵗ Compression
                 let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                   (traceCompression (evalHybridTranscript positions message sOpen freshInit))
                 let tr2 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                   (traceCompression (observe tr1.1.1 tr1.1.2))
                 pure (tr2.1, (), tr1.2.any (inputHitsUnopened positions sHidden) ||
                   tr2.2.any (inputHitsUnopened positions sHidden))] := by
          simp only [joint, map_bind, map_pure]
        rw [← (EvalDistEq.of_evalDist_eq hmap).prEvent_eq]
        simp only [prEvent_map, Function.comp_def, Bool.or_eq_true]
      have hR1 :
          prEvent ((fun r => r.1.2.any (inputHitsUnopened positions r.2.2) = true) <$> joint) =
          prEvent ((fun res : ((Commitment × Proof) × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt) =>
              res.1.2.any (inputHitsUnopened positions res.2) = true) <$>
            (do let sHidden ← $ᵗ (Index → Salt)
                let freshInit ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                  (traceCompression (evalHybridTranscript positions message sOpen freshInit))
                pure (tr1, sHidden))) := by
        have hmap : 𝒟[(fun r => (r.1, r.2.2)) <$> joint] =
            𝒟[do let sHidden ← $ᵗ (Index → Salt)
                 let freshInit ← $ᵗ (Index → Digest)
                 let table ← $ᵗ Compression
                 let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                   (traceCompression (evalHybridTranscript positions message sOpen freshInit))
                 pure (tr1, sHidden)] := by
          simp only [joint, map_bind, map_pure]
          apply _root_.evalDist_bind_congr; intro sHidden
          apply _root_.evalDist_bind_congr; intro freshInit
          apply _root_.evalDist_bind_congr; intro table
          apply _root_.evalDist_bind_congr; intro tr1
          exact OracleComp.evalDist_bind_const _ _
        rw [← (EvalDistEq.of_evalDist_eq hmap).prEvent_eq]
        simp only [prEvent_map, Function.comp_def]
      have hR2 :
          prEvent ((fun r => r.2.1.2.any (inputHitsUnopened positions r.2.2) = true) <$> joint) =
          prEvent ((fun res : (α × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt) =>
              res.1.2.any (inputHitsUnopened positions res.2) = true) <$>
            (do let freshInit ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                  (traceCompression (evalHybridTranscript positions message sOpen freshInit))
                let tr2 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                  (traceCompression (observe tr1.1.1 tr1.1.2))
                let sHidden ← $ᵗ (Index → Salt)
                pure (tr2, sHidden))) := by
        have hmap : 𝒟[(fun r => (r.2.1, r.2.2)) <$> joint] =
            𝒟[do let freshInit ← $ᵗ (Index → Digest)
                 let table ← $ᵗ Compression
                 let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                   (traceCompression (evalHybridTranscript positions message sOpen freshInit))
                 let tr2 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                   (traceCompression (observe tr1.1.1 tr1.1.2))
                 let sHidden ← $ᵗ (Index → Salt)
                 pure (tr2, sHidden)] := by
          simp only [joint, map_bind, map_pure]
          let rest : ProbComp (α × List (BitVec COMPRESSION_INPUT_LENGTH)) := do
            let freshInit ← $ᵗ (Index → Digest)
            let table ← $ᵗ Compression
            let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
              (traceCompression (evalHybridTranscript positions message sOpen freshInit))
            fixedOracleRun ⟨tableExtending cache table, permutation⟩
              (traceCompression (observe tr1.1.1 tr1.1.2))
          have hcomm := distribution_bind_comm ($ᵗ (Index → Salt)) rest (fun sHidden tr2 => pure (tr2, sHidden))
          simpa only [rest, bind_assoc] using hcomm
        rw [← (EvalDistEq.of_evalDist_eq hmap).prEvent_eq]
        simp only [prEvent_map, Function.comp_def]
      rw [hLHS, ← hR1, ← hR2]
      rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite,
        ← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro r
      by_cases h1 : r.1.2.any (inputHitsUnopened positions r.2.2) = true <;>
        by_cases h2 : r.2.1.2.any (inputHitsUnopened positions r.2.2) = true <;> simp [h1, h2]
    -- Bound Phase 2 (`tr2` is independent of `sHidden`, length ≤ budget)
    have hPhase2 :
        prEvent ((fun res : (α × List (BitVec COMPRESSION_INPUT_LENGTH)) × (Index → Salt) =>
            res.1.2.any (inputHitsUnopened positions res.2) = true) <$>
          (do let freshInit ← $ᵗ (Index → Digest)
              let table ← $ᵗ Compression
              let tr1 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                (traceCompression (evalHybridTranscript positions message sOpen freshInit))
              let tr2 ← fixedOracleRun ⟨tableExtending cache table, permutation⟩
                (traceCompression (observe tr1.1.1 tr1.1.2))
              let sHidden ← $ᵗ (Index → Salt)
              pure (tr2, sHidden))) ≤ (budget : ENNReal) / 2 ^ 128 := by
      apply prEvent_bind_le_of_forall_le_of_support; intro freshInit _
      apply prEvent_bind_le_of_forall_le_of_support; intro table _
      apply prEvent_bind_le_of_forall_le_of_support; intro tr1 _
      apply prEvent_bind_le_of_forall_le_of_support; intro tr2 htr2
      rw [bind_pure_comp, prEvent_map]
      refine (list_input_hits_salt_bound positions tr2.2).trans ?_
      exact ENNReal.div_le_div_right (Nat.cast_le.mpr
        (trace_run_length _ (observe tr1.1.1 tr1.1.2) budget (bounded tr1.1.1 tr1.1.2) tr2 htr2)) _
    exact hSplit.trans (add_le_add (phase1_hit_bound permutation cache keys covered message positions sOpen) hPhase2)
  -- Step 4: Combine via triangle inequality!
  rw [measureTVDist_comm] at hHybridMid
  have htri : measureTVDist realJoint hybridJoint ≤
      ((keys.card : ENNReal) / 2 ^ 128).toReal +
      ((keys.card : ENNReal) / 2 ^ 128 + (6 * (LENGTH * LENGTH) : ENNReal) / 2 ^ 192 +
        (budget : ENNReal) / 2 ^ 128).toReal :=
    (measureTVDist_triangle realJoint midJoint hybridJoint).trans (add_le_add hRealMid hHybridMid)
  have hEqDist : measureTVDist
      (referenceObservation permutation cache message positions observe)
      (hybridObservation permutation cache message positions observe) =
      measureTVDist realJoint hybridJoint := by
    simp only [measureTVDist, hRealEq, hHybridEq]
  rw [hEqDist]
  refine htri.trans ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_mul]
  have hkeys : (keys.card : ℝ) ≤ budget := Nat.cast_le.mpr keysBound
  push_cast
  linarith

end CommitGolfCandidate
