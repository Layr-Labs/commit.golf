import CommitGolfCandidate.MoonImage
import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.Execution

/-! Complete adaptive position-binding reduction for the r=1 3-ary/binary tree with
domain-separated iterated hash chains on levels `L9..L16` (`c_l^2 * 2^{w_l} >= 2^238`).
Rather than re-implementing a proof parser for deduplicated cap openings, the collision detector
directly executes the submitted deterministic `check` image on both conflicting claims while
recording every `(input, answer)` compression query in `traceCompressionReplies`.
In the lazy compression ROM, an adaptive banked-credit survival-product induction charges
unchained binary inputs weight `1` and final-stage chain inputs of level `l ∈ [9..16]` weight
`c_l = levelChain l` (bounded by total cache cardinality via stage-parent injectivity), yielding
`Pr[Breaks ∧ calls ≤ q] ≤ q / 2^120` for every `1 ≤ q ≤ 2^120` with `M = q + 2^39` total queries. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Domain-Separation Predicates for Unchained Binary and Chained Stages -/

def isUnchainedBin (x : BitVec 768) : Prop :=
  x.extractLsb' 512 256 = 0#256

def isStage (l s : Nat) (x : BitVec 768) : Prop :=
  9 ≤ l ∧ l ≤ 16 ∧ 1 ≤ s ∧ s ≤ levelChain l ∧
  x.extractLsb' 576 192 = 0#192 ∧
  x.extractLsb' 512 64 = levelTag l s ∧
  (2 ≤ s → x.extractLsb' 256 256 = 0#256)

private theorem binaryInput_hi256 (l r : Digest) :
    (binaryInput l r).extractLsb' 512 256 = 0#256 := by
  unfold binaryInput
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512 - 256)]
  simpa using BitVec.extractLsb'_eq_self (x := (0#256))

private theorem isUnchainedBin_binaryInput (l r : Digest) :
    isUnchainedBin (binaryInput l r) :=
  binaryInput_hi256 l r

private theorem isUnchainedBin_tag_zero {x : BitVec 768} (hx : isUnchainedBin x) :
    x.extractLsb' 512 64 = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbit := congrArg (fun v : BitVec 256 => v.getLsbD i) hx
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show i < 256 by omega, BitVec.getLsbD_zero] at hbit ⊢
  exact hbit

private theorem levelTag_ne_zero {l s : Nat} (hl1 : 9 ≤ l) (hl2 : l ≤ 16)
    (hs1 : 1 ≤ s) (hs2 : s ≤ levelChain l) :
    levelTag l s ≠ 0#64 := by
  have hlt : 256 * l + s < 2 ^ 64 := by
    have : levelChain l ≤ 16 := by interval_cases l <;> decide
    omega
  intro h
  have hval := congrArg BitVec.toNat h
  simp only [levelTag, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt hlt] at hval
  omega

private theorem levelTag_inj {l1 s1 l2 s2 : Nat}
    (hl1a : 9 ≤ l1) (hl1b : l1 ≤ 16) (hs1a : 1 ≤ s1) (hs1b : s1 ≤ levelChain l1)
    (hl2a : 9 ≤ l2) (hl2b : l2 ≤ 16) (hs2a : 1 ≤ s2) (hs2b : s2 ≤ levelChain l2)
    (h : levelTag l1 s1 = levelTag l2 s2) : l1 = l2 ∧ s1 = s2 := by
  have hc1 : levelChain l1 ≤ 16 := by interval_cases l1 <;> decide
  have hc2 : levelChain l2 ≤ 16 := by interval_cases l2 <;> decide
  have h1 : 256 * l1 + s1 < 2 ^ 64 := by omega
  have h2 : 256 * l2 + s2 < 2 ^ 64 := by omega
  have hval := congrArg BitVec.toNat h
  simp only [levelTag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval
  omega

private theorem not_isUnchainedBin_of_isStage {l s : Nat} {x : BitVec 768}
    (hs : isStage l s x) : ¬ isUnchainedBin x := by
  intro hu
  have h0 := isUnchainedBin_tag_zero hu
  exact levelTag_ne_zero hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 (hs.2.2.2.2.2.1.symm.trans h0)

private theorem isStage_unique {l1 s1 l2 s2 : Nat} {x : BitVec 768}
    (h1 : isStage l1 s1 x) (h2 : isStage l2 s2 x) : l1 = l2 ∧ s1 = s2 := by
  obtain ⟨hl1a, hl1b, hs1a, hs1b, _, ht1, _⟩ := h1
  obtain ⟨hl2a, hl2b, hs2a, hs2b, _, ht2, _⟩ := h2
  exact levelTag_inj hl1a hl1b hs1a hs1b hl2a hl2b hs2a hs2b (ht1.symm.trans ht2)

private theorem isStage_eq_of_prev_eq {l s : Nat} {x y : BitVec 768}
    (hs : 2 ≤ s) (hx : isStage l s x) (hy : isStage l s y)
    (hprev : x.extractLsb' 0 256 = y.extractLsb' 0 256) : x = y := by
  have hmid : x.extractLsb' 256 256 = y.extractLsb' 256 256 :=
    (hx.2.2.2.2.2.2 hs).trans (hy.2.2.2.2.2.2 hs).symm
  have htag : x.extractLsb' 512 64 = y.extractLsb' 512 64 :=
    hx.2.2.2.2.2.1.trans hy.2.2.2.2.2.1.symm
  have hhi : x.extractLsb' 576 192 = y.extractLsb' 576 192 :=
    hx.2.2.2.2.1.trans hy.2.2.2.2.1.symm
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases c0 : i < 256
  · have := congrArg (fun v => v.getLsbD i) hprev
    simpa [BitVec.getLsbD_extractLsb', c0] using this
  · by_cases c1 : i < 512
    · have := congrArg (fun v => v.getLsbD (i - 256)) hmid
      simpa [BitVec.getLsbD_extractLsb', show i - 256 < 256 by omega,
        show 256 + (i - 256) = i by omega] using this
    · by_cases c2 : i < 576
      · have := congrArg (fun v => v.getLsbD (i - 512)) htag
        simpa [BitVec.getLsbD_extractLsb', show i - 512 < 64 by omega,
          show 512 + (i - 512) = i by omega] using this
      · have := congrArg (fun v => v.getLsbD (i - 576)) hhi
        simpa [BitVec.getLsbD_extractLsb', show i - 576 < 192 by omega,
          show 576 + (i - 576) = i by omega] using this

private theorem levelChain_ge_two {l : Nat} (hl1 : 9 ≤ l) (hl2 : l ≤ 16) : 2 ≤ levelChain l := by
  interval_cases l <;> decide

private theorem levelChain_le_16 {l : Nat} (hl1 : 9 ≤ l) (hl2 : l ≤ 16) : levelChain l ≤ 16 := by
  interval_cases l <;> decide

private theorem levelChain_eq_one_of_unchained {l : Nat} (hl1 : 2 ≤ l) (hl2 : l ≤ 24)
    (hnot : ¬ (9 ≤ l ∧ l ≤ 16)) : levelChain l = 1 := by
  interval_cases l <;> first | decide | omega

private theorem low238_maskLevel_unchained {l : Nat} (hl1 : 2 ≤ l) (hl2 : l ≤ 24)
    (hnot : ¬ (9 ≤ l ∧ l ≤ 16)) (d : Digest) :
    low238 (maskLevel l d) = low238 d := by
  have hw : 238 ≤ levelWidth l := by interval_cases l <;> first | decide | omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [low238, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add,
    maskLevel, maskWidth_getLsbD, show i < levelWidth l by omega]

/-! ### 2. Witness Paths and Domain-Separated Chain Collision Extraction -/

structure WitnessPath where
  index : Index
  value : Entry
  salt : Salt192
  l0Sib0 : Digest
  l0Sib1 : Digest
  binSib : Nat → Digest

def WitnessPath.l0Input (c : Comp96) (w : WitnessPath) : BitVec 768 :=
  let d0 := leafDigest c w.index w.salt w.value
  let r := w.index.val % 3
  if r = 0 then ternaryInput d0 w.l0Sib0 w.l0Sib1
  else if r = 1 then ternaryInput w.l0Sib0 d0 w.l0Sib1
  else ternaryInput w.l0Sib0 w.l0Sib1 d0

def WitnessPath.evalL1 (c : Comp96) (w : WitnessPath) : Digest :=
  if w.index.val / 3 = FULL_TRIPLETS then
    leafDigest c w.index w.salt w.value
  else
    c (w.l0Input c)

def WitnessPath.evalLevel (c : Comp96) (w : WitnessPath) : Nat → Digest
  | 0 => leafDigest c w.index w.salt w.value
  | 1 => w.evalL1 c
  | l + 2 =>
      let prev := l + 1
      let cur := w.evalLevel c prev
      let idx := (w.index.val / 3) >>> (prev - 1)
      if (idx ^^^ 1) < levelSize prev then
        if idx % 2 = 0 then chainHash c (l + 2) cur (w.binSib prev)
        else chainHash c (l + 2) (w.binSib prev) cur
      else if l + 2 < 9 then
        cur
      else
        chainHash c (l + 2) cur 0

def WitnessPath.evalRoot (c : Comp96) (w : WitnessPath) : Digest :=
  w.evalLevel c 24

def WitnessPath.leafInputs (c : Comp96) (w : WitnessPath) : List (BitVec 768) :=
  let iU := leafUInput w.value
  let u := c iU
  let iA := leafAInput u w.value
  let a := c iA
  let iB := leafBInput w.value
  let b := c iB
  let iF := leafFinalInput w.index a b w.salt
  [iU, iA, iB, iF]

def WitnessPath.levelInputs (c : Comp96) (w : WitnessPath) (prev : Nat) : List (BitVec 768) :=
  let lvl := prev + 1
  let cur := w.evalLevel c prev
  let idx := (w.index.val / 3) >>> (prev - 1)
  if (idx ^^^ 1) < levelSize prev then
    if idx % 2 = 0 then chainInputs c lvl cur (w.binSib prev)
    else chainInputs c lvl (w.binSib prev) cur
  else if lvl < 9 then
    []
  else
    chainInputs c lvl cur 0

def WitnessPath.pathInputs (c : Comp96) (w : WitnessPath) : List (BitVec 768) :=
  w.leafInputs c ++
  (if w.index.val / 3 = FULL_TRIPLETS then [] else [w.l0Input c]) ++
  (List.range 23).flatMap (fun k => w.levelInputs c (k + 1))

def InputValidStage (c : Comp96) (inputs : List (BitVec 768)) (l : Nat) : Nat → BitVec 768 → Prop
  | 0, _ => False
  | 1, x => isStage l 1 x ∧ x ∈ inputs
  | s + 2, x =>
      isStage l (s + 2) x ∧ x ∈ inputs ∧
      ∃ p, InputValidStage c inputs l (s + 1) p ∧ c p = x.extractLsb' 0 256

def HasChainCollision (c : Comp96) (inputs : List (BitVec 768)) : Prop :=
  (∃ x ∈ inputs, ∃ y ∈ inputs, x ≠ y ∧ c x = c y) ∨
  (∃ x ∈ inputs, ∃ y ∈ inputs, x ≠ y ∧ isUnchainedBin x ∧ isUnchainedBin y ∧
    low238 (c x) = low238 (c y)) ∨
  (∃ l, 9 ≤ l ∧ l ≤ 16 ∧ ∃ x y, x ≠ y ∧
    InputValidStage c inputs l (levelChain l) x ∧
    InputValidStage c inputs l (levelChain l) y ∧
    lowWidth (levelWidth l) (c x) = lowWidth (levelWidth l) (c y))

private theorem mem_pathInputs_leaf (c : Comp96) (w : WitnessPath) (x : BitVec 768)
    (hx : x ∈ w.leafInputs c) : x ∈ w.pathInputs c := by
  unfold WitnessPath.pathInputs; simp [hx]

private theorem mem_pathInputs_l0 (c : Comp96) (w : WitnessPath)
    (hfull : w.index.val / 3 ≠ FULL_TRIPLETS) : w.l0Input c ∈ w.pathInputs c := by
  unfold WitnessPath.pathInputs; simp [hfull]

private theorem mem_pathInputs_level (c : Comp96) (w : WitnessPath) (prev : Nat)
    (hp1 : 1 ≤ prev) (hp2 : prev ≤ 23) (x : BitVec 768) (hx : x ∈ w.levelInputs c prev) :
    x ∈ w.pathInputs c := by
  unfold WitnessPath.pathInputs
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨prev - 1, List.mem_range.mpr (by omega), by simpa [show prev - 1 + 1 = prev by omega] using hx⟩

private theorem bv_append_inj {m n : Nat} {a1 a2 : BitVec m} {b1 b2 : BitVec n}
    (h : a1 ++ b1 = a2 ++ b2) : a1 = a2 ∧ b1 = b2 := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hbit := congrArg (fun v : BitVec (m + n) => v.getLsbD (n + i)) h
    simp only [BitVec.getLsbD_append, show ¬ (n + i < n) by omega, decide_false,
      Bool.false_eq_true, ite_false, show n + i - n = i by omega] at hbit
    exact hbit
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hbit := congrArg (fun v : BitVec (m + n) => v.getLsbD i) h
    simp only [BitVec.getLsbD_append, hi, decide_true, ite_true] at hbit
    exact hbit

private theorem leaf_collision (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hne : w1.value ≠ w2.value)
    (hdig : leafDigest c w1.index w1.salt w1.value = leafDigest c w2.index w2.salt w2.value) :
    HasChainCollision c (w1.pathInputs c ++ w2.pathInputs c) := by
  left
  set iU₁ := leafUInput w1.value; set iU₂ := leafUInput w2.value
  set u₁ := c iU₁; set u₂ := c iU₂
  set iA₁ := leafAInput u₁ w1.value; set iA₂ := leafAInput u₂ w2.value
  set a₁ := c iA₁; set a₂ := c iA₂
  set iB₁ := leafBInput w1.value; set iB₂ := leafBInput w2.value
  set b₁ := c iB₁; set b₂ := c iB₂
  set iF₁ := leafFinalInput w1.index a₁ b₁ w1.salt
  set iF₂ := leafFinalInput w2.index a₂ b₂ w2.salt
  have hmem : ∀ x ∈ w1.leafInputs c, x ∈ w1.pathInputs c ++ w2.pathInputs c := fun x hx =>
    List.mem_append_left _ (mem_pathInputs_leaf c w1 x hx)
  have hmem2 : ∀ x ∈ w2.leafInputs c, x ∈ w1.pathInputs c ++ w2.pathInputs c := fun x hx =>
    List.mem_append_right _ (mem_pathInputs_leaf c w2 x hx)
  by_cases hF : iF₁ ≠ iF₂
  · exact ⟨iF₁, hmem _ (by simp [WitnessPath.leafInputs, iF₁, a₁, iA₁, u₁, iU₁, b₁, iB₁]),
      iF₂, hmem2 _ (by simp [WitnessPath.leafInputs, iF₂, a₂, iA₂, u₂, iU₂, b₂, iB₂]), hF, hdig⟩
  · push_neg at hF
    have hF' : leafFinalInput w2.index a₁ b₁ w1.salt = leafFinalInput w2.index a₂ b₂ w2.salt := by
      simpa [iF₁, iF₂, hidx] using hF
    obtain ⟨ha, hb, _⟩ := leafFinalInput_inj hF'
    by_cases hB : iB₁ ≠ iB₂
    · exact ⟨iB₁, hmem _ (by simp [WitnessPath.leafInputs, iB₁]),
        iB₂, hmem2 _ (by simp [WitnessPath.leafInputs, iB₂]), hB, hb⟩
    · push_neg at hB
      by_cases hA : iA₁ ≠ iA₂
      · exact ⟨iA₁, hmem _ (by simp [WitnessPath.leafInputs, iA₁, u₁, iU₁]),
          iA₂, hmem2 _ (by simp [WitnessPath.leafInputs, iA₂, u₂, iU₂]), hA, ha⟩
      · push_neg at hA
        obtain ⟨hvMid, hu⟩ := bv_append_inj (show w1.value.extractLsb' 768 512 ++ u₁ =
          w2.value.extractLsb' 768 512 ++ u₂ from hA)
        by_cases hU : iU₁ ≠ iU₂
        · exact ⟨iU₁, hmem _ (by simp [WitnessPath.leafInputs, iU₁]),
            iU₂, hmem2 _ (by simp [WitnessPath.leafInputs, iU₂]), hU, hu⟩
        · push_neg at hU
          exact (hne (entry_eq_of_late_slices w1.value w2.value hU hvMid hB)).elim

private theorem l1_step_collision (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (heq : w1.evalL1 c = w2.evalL1 c) :
    leafDigest c w1.index w1.salt w1.value = leafDigest c w2.index w2.salt w2.value ∨
    HasChainCollision c (w1.pathInputs c ++ w2.pathInputs c) := by
  unfold WitnessPath.evalL1 at heq
  rw [hidx] at heq
  by_cases hfull : w2.index.val / 3 = FULL_TRIPLETS
  · left
    simp only [hfull, ite_true] at heq
    simpa [hidx] using heq
  · simp only [hfull, ite_false] at heq
    by_cases hne : w1.l0Input c ≠ w2.l0Input c
    · right; left
      exact ⟨w1.l0Input c, List.mem_append_left _ (mem_pathInputs_l0 c w1 (by rw [hidx]; exact hfull)),
        w2.l0Input c, List.mem_append_right _ (mem_pathInputs_l0 c w2 hfull), hne, heq⟩
    · left
      push_neg at hne
      unfold WitnessPath.l0Input at hne
      rw [hidx] at hne
      dsimp only at hne
      split at hne
      · have := congrArg (fun v : BitVec 768 => v.extractLsb' 0 256) hne
        simpa [ternaryInput_d0, hidx] using this
      · split at hne
        · have := congrArg (fun v : BitVec 768 => v.extractLsb' 256 256) hne
          simpa [ternaryInput_d1, hidx] using this
        · have := congrArg (fun v : BitVec 768 => v.extractLsb' 512 256) hne
          simpa [ternaryInput_d2, hidx] using this

/-- The stage-`(k+1)` input inside `chainInputs c l left right`. -/
private def chainStageInput (c : Comp96) (l : Nat) (left right : Digest) : Nat → BitVec 768
  | 0 => binaryTaggedInput left right (levelTag l 1)
  | k + 1 =>
      let x1 := binaryTaggedInput left right (levelTag l 1)
      chainStepInput (chainIter c l k (c x1)) (levelTag l (k + 2))

private theorem chainStageInput_eval (c : Comp96) (l : Nat) (left right : Digest) (k : Nat) :
    c (chainStageInput c l left right k) =
      chainIter c l k (c (binaryTaggedInput left right (levelTag l 1))) := by
  cases k <;> rfl

private theorem chainStageInput_mem_iter (c : Comp96) (l : Nat) (left right : Digest)
    (m k : Nat) (hk : k < m) :
    chainStageInput c l left right (k + 1) ∈
      chainIterInputs c l m (c (binaryTaggedInput left right (levelTag l 1))) := by
  induction m with
  | zero => omega
  | succ m ih =>
    unfold chainIterInputs
    rw [List.mem_append]
    by_cases hkm : k < m
    · exact Or.inl (ih hkm)
    · have rflk : k = m := by omega
      subst rflk
      exact Or.inr (List.mem_singleton.mpr rfl)

private theorem chainStageInput_mem (c : Comp96) (l : Nat) (left right : Digest)
    (hl1 : 9 ≤ l) (hl2 : l ≤ 16) (k : Nat) (hk : k < levelChain l) :
    chainStageInput c l left right k ∈ chainInputs c l left right := by
  have hc2 : 2 ≤ levelChain l := levelChain_ge_two hl1 hl2
  have hnot : ¬ (levelChain l ≤ 1) := by omega
  unfold chainInputs
  rw [if_neg hnot]
  cases k with
  | zero => exact List.mem_cons_self
  | succ k' =>
    exact List.mem_cons_of_mem _ (chainStageInput_mem_iter c l left right (levelChain l - 1) k' (by omega))

private theorem chainStageInput_valid (c : Comp96) (inputs : List (BitVec 768))
    (l : Nat) (left right : Digest) (hl1 : 9 ≤ l) (hl2 : l ≤ 16)
    (hsub : ∀ z ∈ chainInputs c l left right, z ∈ inputs) :
    ∀ k, k < levelChain l →
      InputValidStage c inputs l (k + 1) (chainStageInput c l left right k) := by
  intro k hk
  induction k with
  | zero =>
    have hc2 : 2 ≤ levelChain l := levelChain_ge_two hl1 hl2
    refine ⟨⟨hl1, hl2, by omega, by omega, binaryTaggedInput_hi _ _ _,
      binaryTaggedInput_tag _ _ _, fun h => by omega⟩,
      hsub _ (chainStageInput_mem c l left right hl1 hl2 0 hk)⟩
  | succ k ih =>
    refine ⟨⟨hl1, hl2, by omega, by omega, chainStepInput_hi _ _, chainStepInput_tag _ _,
        fun _ => chainStepInput_mid _ _⟩,
      hsub _ (chainStageInput_mem c l left right hl1 hl2 (k + 1) hk),
      chainStageInput c l left right k, ih (by omega), ?_⟩
    rw [chainStageInput_eval c l left right k, chainStageInput, chainStepInput_prev]

private theorem chainHash_collision (c : Comp96) (inputs : List (BitVec 768))
    (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 24) (l1 r1 l2 r2 : Digest)
    (hsub1 : ∀ z ∈ chainInputs c l l1 r1, z ∈ inputs)
    (hsub2 : ∀ z ∈ chainInputs c l l2 r2, z ∈ inputs)
    (heq : chainHash c l l1 r1 = chainHash c l l2 r2) :
    (l1 = l2 ∧ r1 = r2) ∨ HasChainCollision c inputs := by
  by_cases hch : 9 ≤ l ∧ l ≤ 16
  · obtain ⟨hl9, hl16⟩ := hch
    have hc2 : 2 ≤ levelChain l := levelChain_ge_two hl9 hl16
    have hnot : ¬ (levelChain l ≤ 1) := by omega
    have hlow_top : lowWidth (levelWidth l) (c (chainStageInput c l l1 r1 (levelChain l - 1))) =
        lowWidth (levelWidth l) (c (chainStageInput c l l2 r2 (levelChain l - 1))) := by
      have hw := levelWidth_le_256 l
      have h1 : chainHash c l l1 r1 = maskWidth (levelWidth l) (c (chainStageInput c l l1 r1 (levelChain l - 1))) := by
        simp only [chainHash, chainEval, hnot, ite_false, maskLevel, chainStageInput_eval]
      have h2 : chainHash c l l2 r2 = maskWidth (levelWidth l) (c (chainStageInput c l l2 r2 (levelChain l - 1))) := by
        simp only [chainHash, chainEval, hnot, ite_false, maskLevel, chainStageInput_eval]
      rw [h1, h2, maskWidth_eq_iff _ hw] at heq
      exact heq
    have hdesc : ∀ k, k < levelChain l →
        chainStageInput c l l1 r1 k = chainStageInput c l l2 r2 k →
        (l1 = l2 ∧ r1 = r2) ∨ HasChainCollision c inputs := by
      intro k
      induction k with
      | zero =>
        intro _ h0
        left
        refine ⟨?_, ?_⟩
        · simpa [chainStageInput, binaryTaggedInput_left] using congrArg (fun v => v.extractLsb' 0 256) h0
        · simpa [chainStageInput, binaryTaggedInput_right] using congrArg (fun v => v.extractLsb' 256 256) h0
      | succ k ih =>
        intro hk hstep
        have hprev : c (chainStageInput c l l1 r1 k) = c (chainStageInput c l l2 r2 k) := by
          have h0 := congrArg (fun v => v.extractLsb' 0 256) hstep
          rw [chainStageInput_eval c l l1 r1 k, chainStageInput_eval c l l2 r2 k]
          simpa only [chainStageInput, chainStepInput_prev] using h0
        by_cases hne : chainStageInput c l l1 r1 k ≠ chainStageInput c l l2 r2 k
        · right; left
          exact ⟨_, hsub1 _ (chainStageInput_mem c l l1 r1 hl9 hl16 k (by omega)),
            _, hsub2 _ (chainStageInput_mem c l l2 r2 hl9 hl16 k (by omega)), hne, hprev⟩
        · push_neg at hne
          exact ih (by omega) hne
    by_cases hne : chainStageInput c l l1 r1 (levelChain l - 1) ≠
        chainStageInput c l l2 r2 (levelChain l - 1)
    · right; right; right
      have hv1 := chainStageInput_valid c inputs l l1 r1 hl9 hl16 hsub1 (levelChain l - 1) (by omega)
      have hv2 := chainStageInput_valid c inputs l l2 r2 hl9 hl16 hsub2 (levelChain l - 1) (by omega)
      rw [show levelChain l - 1 + 1 = levelChain l by omega] at hv1 hv2
      exact ⟨l, hl9, hl16, _, _, hne, hv1, hv2, hlow_top⟩
    · push_neg at hne
      exact hdesc (levelChain l - 1) (by omega) hne
  · have hc1 : levelChain l ≤ 1 := by rw [levelChain_eq_one_of_unchained hl1 hl2 hch]
    have hm1 : binaryInput l1 r1 ∈ inputs := hsub1 _ (by simp [chainInputs, hc1])
    have hm2 : binaryInput l2 r2 ∈ inputs := hsub2 _ (by simp [chainInputs, hc1])
    by_cases hne : binaryInput l1 r1 ≠ binaryInput l2 r2
    · right; right; left
      have hlow : low238 (c (binaryInput l1 r1)) = low238 (c (binaryInput l2 r2)) := by
        rw [chainHash_unchained c l hc1, chainHash_unchained c l hc1] at heq
        have h := congrArg low238 heq
        simpa only [low238_maskLevel_unchained hl1 hl2 hch] using h
      exact ⟨binaryInput l1 r1, hm1, binaryInput l2 r2, hm2, hne,
        isUnchainedBin_binaryInput l1 r1, isUnchainedBin_binaryInput l2 r2, hlow⟩
    · left
      push_neg at hne
      refine ⟨?_, ?_⟩
      · simpa [binaryInput_left] using congrArg (fun v => v.extractLsb' 0 256) hne
      · simpa [binaryInput_right] using congrArg (fun v => v.extractLsb' 256 256) hne

private theorem bin_step_collision (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (prev : Nat) (hp1 : 1 ≤ prev) (hp2 : prev ≤ 23)
    (heq : w1.evalLevel c (prev + 1) = w2.evalLevel c (prev + 1)) :
    w1.evalLevel c prev = w2.evalLevel c prev ∨
    HasChainCollision c (w1.pathInputs c ++ w2.pathInputs c) := by
  obtain ⟨m, rfl⟩ : ∃ m, prev = m + 1 := ⟨prev - 1, by omega⟩
  unfold WitnessPath.evalLevel at heq
  rw [hidx] at heq
  dsimp only at heq
  simp only [Nat.add_sub_cancel] at heq
  set idx := (w2.index.val / 3) >>> m
  have hsub1 : ∀ z ∈ w1.levelInputs c (m + 1), z ∈ w1.pathInputs c ++ w2.pathInputs c :=
    fun z hz => List.mem_append_left _ (mem_pathInputs_level c w1 (m + 1) (by omega) hp2 z hz)
  have hsub2 : ∀ z ∈ w2.levelInputs c (m + 1), z ∈ w1.pathInputs c ++ w2.pathInputs c :=
    fun z hz => List.mem_append_right _ (mem_pathInputs_level c w2 (m + 1) (by omega) hp2 z hz)
  by_cases hpair : (idx ^^^ 1) < levelSize (m + 1)
  · rw [if_pos hpair, if_pos hpair] at heq
    by_cases heven : idx % 2 = 0
    · rw [if_pos heven, if_pos heven] at heq
      have hs1 : ∀ z ∈ chainInputs c (m + 2) (w1.evalLevel c (m + 1)) (w1.binSib (m + 1)),
          z ∈ w1.pathInputs c ++ w2.pathInputs c := fun z hz => hsub1 z (by
            unfold WitnessPath.levelInputs; rw [hidx]; simp [idx, hpair, heven, hz])
      have hs2 : ∀ z ∈ chainInputs c (m + 2) (w2.evalLevel c (m + 1)) (w2.binSib (m + 1)),
          z ∈ w1.pathInputs c ++ w2.pathInputs c := fun z hz => hsub2 z (by
            unfold WitnessPath.levelInputs; simp [idx, hpair, heven, hz])
      rcases chainHash_collision c _ (m + 2) (by omega) (by omega) _ _ _ _ hs1 hs2 heq with ⟨hl, _⟩ | hcol
      · exact Or.inl hl
      · exact Or.inr hcol
    · rw [if_neg heven, if_neg heven] at heq
      have hs1 : ∀ z ∈ chainInputs c (m + 2) (w1.binSib (m + 1)) (w1.evalLevel c (m + 1)),
          z ∈ w1.pathInputs c ++ w2.pathInputs c := fun z hz => hsub1 z (by
            unfold WitnessPath.levelInputs; rw [hidx]; simp [idx, hpair, heven, hz])
      have hs2 : ∀ z ∈ chainInputs c (m + 2) (w2.binSib (m + 1)) (w2.evalLevel c (m + 1)),
          z ∈ w1.pathInputs c ++ w2.pathInputs c := fun z hz => hsub2 z (by
            unfold WitnessPath.levelInputs; simp [idx, hpair, heven, hz])
      rcases chainHash_collision c _ (m + 2) (by omega) (by omega) _ _ _ _ hs1 hs2 heq with ⟨_, hr⟩ | hcol
      · exact Or.inl hr
      · exact Or.inr hcol
  · rw [if_neg hpair, if_neg hpair] at heq
    by_cases hlt9 : m + 2 < 9
    · rw [if_pos hlt9, if_pos hlt9] at heq
      exact Or.inl heq
    · rw [if_neg hlt9, if_neg hlt9] at heq
      have hs1 : ∀ z ∈ chainInputs c (m + 2) (w1.evalLevel c (m + 1)) 0,
          z ∈ w1.pathInputs c ++ w2.pathInputs c := fun z hz => hsub1 z (by
            unfold WitnessPath.levelInputs; rw [hidx]; dsimp only
            simp only [Nat.add_sub_cancel]; rw [if_neg hpair, if_neg hlt9]; exact hz)
      have hs2 : ∀ z ∈ chainInputs c (m + 2) (w2.evalLevel c (m + 1)) 0,
          z ∈ w1.pathInputs c ++ w2.pathInputs c := fun z hz => hsub2 z (by
            unfold WitnessPath.levelInputs; dsimp only
            simp only [Nat.add_sub_cancel]; rw [if_neg hpair, if_neg hlt9]; exact hz)
      rcases chainHash_collision c _ (m + 2) (by omega) (by omega) _ _ _ _ hs1 hs2 heq with ⟨hl, _⟩ | hcol
      · exact Or.inl hl
      · exact Or.inr hcol

/-- Two conflicting witness paths reaching the same root witness a full 256-bit, unchained 238-bit,
or valid chained `levelWidth l`-bit compression collision. -/
theorem collision_of_paths (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hne : w1.value ≠ w2.value)
    (hroot : w1.evalRoot c = w2.evalRoot c) :
    HasChainCollision c (w1.pathInputs c ++ w2.pathInputs c) := by
  have descend : ∀ k ≤ 23,
      w1.evalLevel c (24 - k) = w2.evalLevel c (24 - k) ∨
      HasChainCollision c (w1.pathInputs c ++ w2.pathInputs c) := by
    intro k hk
    induction k with
    | zero => left; exact hroot
    | succ k ih =>
      rcases ih (by omega) with heq | hcol
      · have hstep : 24 - k = (24 - (k + 1)) + 1 := by omega
        rw [hstep] at heq
        exact bin_step_collision c w1 w2 hidx (24 - (k + 1)) (by omega) (by omega) heq
      · exact Or.inr hcol
  rcases descend 23 (by omega) with hl1 | hcol
  · rcases l1_step_collision c w1 w2 hidx hl1 with hleaf | hcol
    · exact leaf_collision c w1 w2 hidx hne hleaf
    · exact hcol
  · exact hcol

/-! ### 3. Adaptive Banked-Credit Lazy-ROM Survival-Product Bound -/

def cache768 (h768 : COMPRESSION_INPUT_LENGTH = 768) (cache : CompressionCache)
    (x : BitVec 768) : Option Digest :=
  cache (x.cast h768.symm)

private theorem cache768_cacheQuery_self (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (input : CompressionSpec.Domain) (ans : Digest) :
    cache768 h768 (cache.cacheQuery input ans) (input.cast h768) = some ans := by
  unfold cache768
  simp only [BitVec.cast_cast, BitVec.cast_eq]
  exact QueryCache.cacheQuery_self cache input ans

private theorem cache768_cacheQuery_of_ne (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (input : CompressionSpec.Domain) (ans : Digest)
    {x : BitVec 768} (hne : x ≠ input.cast h768) :
    cache768 h768 (cache.cacheQuery input ans) x = cache768 h768 cache x := by
  unfold cache768
  have hne' : x.cast h768.symm ≠ input := by
    intro h; apply hne
    have := congrArg (BitVec.cast h768) h
    simpa using this
  exact QueryCache.cacheQuery_of_ne cache ans hne'

def ValidStage (m : BitVec 768 → Option Digest) (l : Nat) : Nat → BitVec 768 → Prop
  | 0, _ => False
  | 1, x => isStage l 1 x ∧ (m x).isSome
  | s + 2, x =>
      isStage l (s + 2) x ∧ (m x).isSome ∧
      ∃ p, ValidStage m l (s + 1) p ∧ m p = some (x.extractLsb' 0 256)

def ReadyStage (m : BitVec 768 → Option Digest) (l : Nat) : Nat → BitVec 768 → Prop
  | 0, _ => False
  | 1, x => isStage l 1 x
  | s + 2, x =>
      isStage l (s + 2) x ∧
      ∃ p, ValidStage m l (s + 1) p ∧ m p = some (x.extractLsb' 0 256)

private theorem validStage_isStage {m : BitVec 768 → Option Digest} {l s : Nat} {x : BitVec 768}
    (h : ValidStage m l s x) : isStage l s x := by
  cases s with
  | zero => exact h.elim
  | succ s =>
    cases s with
    | zero => exact h.1
    | succ s => exact h.1

private theorem validStage_isSome {m : BitVec 768 → Option Digest} {l s : Nat} {x : BitVec 768}
    (h : ValidStage m l s x) : (m x).isSome := by
  cases s with
  | zero => exact h.elim
  | succ s =>
    cases s with
    | zero => exact h.2
    | succ s => exact h.2.1

private theorem readyStage_isStage {m : BitVec 768 → Option Digest} {l s : Nat} {x : BitVec 768}
    (h : ReadyStage m l s x) : isStage l s x := by
  cases s with
  | zero => exact h.elim
  | succ s =>
    cases s with
    | zero => exact h
    | succ s => exact h.1

private theorem validStage_mono {m m' : BitVec 768 → Option Digest}
    (hmono : ∀ x v, m x = some v → m' x = some v) {l s : Nat} {x : BitVec 768}
    (h : ValidStage m l s x) : ValidStage m' l s x := by
  induction s generalizing x with
  | zero => exact h.elim
  | succ s ih =>
    cases s with
    | zero =>
      obtain ⟨hs, hsome⟩ := h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨hs, by rw [hmono x v hv]; rfl⟩
    | succ s =>
      obtain ⟨hs, hsome, p, hp, hmp⟩ := h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨hs, by rw [hmono x v hv]; rfl, p, ih hp, hmono p _ hmp⟩

def CacheCol256 (cache : CompressionCache) : Prop :=
  ∃ x y vx vy, x ≠ y ∧ cache x = some vx ∧ cache y = some vy ∧ vx = vy

def CacheCol0 (h768 : COMPRESSION_INPUT_LENGTH = 768) (cache : CompressionCache) : Prop :=
  ∃ x y vx vy, x ≠ y ∧ isUnchainedBin x ∧ isUnchainedBin y ∧
    cache768 h768 cache x = some vx ∧ cache768 h768 cache y = some vy ∧
    low238 vx = low238 vy

def CacheColL (h768 : COMPRESSION_INPUT_LENGTH = 768) (cache : CompressionCache) (l : Nat) : Prop :=
  ∃ x y vx vy, x ≠ y ∧
    ValidStage (cache768 h768 cache) l (levelChain l) x ∧
    ValidStage (cache768 h768 cache) l (levelChain l) y ∧
    cache768 h768 cache x = some vx ∧ cache768 h768 cache y = some vy ∧
    lowWidth (levelWidth l) vx = lowWidth (levelWidth l) vy

def CacheBad (h768 : COMPRESSION_INPUT_LENGTH = 768) (cache : CompressionCache) : Prop :=
  CacheCol256 cache ∨ CacheCol0 h768 cache ∨ ∃ l, 9 ≤ l ∧ l ≤ 16 ∧ CacheColL h768 cache l

def FreshBad256 (h768 : COMPRESSION_INPUT_LENGTH = 768) (cache : CompressionCache)
    (input : CompressionSpec.Domain) (ans : Digest) : Prop :=
  (∃ k v, cache k = some v ∧ v = ans) ∨
  (∃ k, cache k ≠ none ∧ (k.cast h768).extractLsb' 0 256 = ans) ∨
  ((input.cast h768).extractLsb' 0 256 = ans)

private theorem validStage_cacheQuery_of_ne (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (input : CompressionSpec.Domain) (ans : Digest)
    (hnone : cache input = none) (hsafe : ¬ FreshBad256 h768 cache input ans)
    (l s : Nat) :
    ∀ x, x ≠ input.cast h768 →
      (ValidStage (cache768 h768 (cache.cacheQuery input ans)) l s x ↔
       ValidStage (cache768 h768 cache) l s x) := by
  have hmono : ∀ z v, cache768 h768 cache z = some v →
      cache768 h768 (cache.cacheQuery input ans) z = some v := by
    intro z v hz
    by_cases hzi : z = input.cast h768
    · subst hzi
      unfold cache768 at hz
      simp only [BitVec.cast_cast, BitVec.cast_eq] at hz
      rw [hnone] at hz; cases hz
    · rw [cache768_cacheQuery_of_ne h768 cache input ans hzi]; exact hz
  induction s with
  | zero => intro _ _; exact Iff.rfl
  | succ s ih =>
    intro x hne
    constructor
    · intro hv
      cases s with
      | zero =>
        obtain ⟨hs, hsome⟩ := hv
        rw [cache768_cacheQuery_of_ne h768 cache input ans hne] at hsome
        exact ⟨hs, hsome⟩
      | succ s =>
        obtain ⟨hs, hsome, p, hp, hmp⟩ := hv
        rw [cache768_cacheQuery_of_ne h768 cache input ans hne] at hsome
        have hpne : p ≠ input.cast h768 := by
          intro hpeq
          subst hpeq
          rw [cache768_cacheQuery_self] at hmp
          cases hmp
          apply hsafe
          right; left
          refine ⟨x.cast h768.symm, ?_, by simp⟩
          intro hxn
          have h1 : cache768 h768 cache x = none := hxn
          rw [h1] at hsome
          cases hsome
        rw [cache768_cacheQuery_of_ne h768 cache input ans hpne] at hmp
        exact ⟨hs, hsome, p, (ih p hpne).mp hp, hmp⟩
    · exact validStage_mono hmono

private theorem validStage_cacheQuery_self (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (input : CompressionSpec.Domain) (ans : Digest)
    (hnone : cache input = none) (hsafe : ¬ FreshBad256 h768 cache input ans)
    (l s : Nat) :
    ValidStage (cache768 h768 (cache.cacheQuery input ans)) l s (input.cast h768) ↔
    ReadyStage (cache768 h768 cache) l s (input.cast h768) := by
  have hmono : ∀ z v, cache768 h768 cache z = some v →
      cache768 h768 (cache.cacheQuery input ans) z = some v := by
    intro z v hz
    by_cases hzi : z = input.cast h768
    · subst hzi
      unfold cache768 at hz
      simp only [BitVec.cast_cast, BitVec.cast_eq] at hz
      rw [hnone] at hz; cases hz
    · rw [cache768_cacheQuery_of_ne h768 cache input ans hzi]; exact hz
  cases s with
  | zero => exact Iff.rfl
  | succ s =>
    cases s with
    | zero =>
      simp only [ValidStage, ReadyStage, cache768_cacheQuery_self, Option.isSome_some, and_true]
    | succ s =>
      constructor
      · rintro ⟨hs, _, p, hp, hmp⟩
        have hpne : p ≠ input.cast h768 := by
          intro hpeq; subst hpeq
          rw [cache768_cacheQuery_self] at hmp
          cases hmp
          exact hsafe (Or.inr (Or.inr rfl))
        rw [cache768_cacheQuery_of_ne h768 cache input ans hpne] at hmp
        exact ⟨hs, p, (validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l (s + 1) p hpne).mp hp, hmp⟩
      · rintro ⟨hs, p, hp, hmp⟩
        exact ⟨hs, by rw [cache768_cacheQuery_self]; rfl, p, validStage_mono hmono hp, hmono p _ hmp⟩

noncomputable def unchainedSet (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (keys : Finset CompressionSpec.Domain) : Finset CompressionSpec.Domain :=
  letI := Classical.decPred (fun k : CompressionSpec.Domain => isUnchainedBin (k.cast h768))
  keys.filter (fun k => isUnchainedBin (k.cast h768))

noncomputable def stageSet (h768 : COMPRESSION_INPUT_LENGTH = 768) (cache : CompressionCache)
    (keys : Finset CompressionSpec.Domain) (l s : Nat) : Finset CompressionSpec.Domain :=
  letI := Classical.decPred (fun k : CompressionSpec.Domain => ValidStage (cache768 h768 cache) l s (k.cast h768))
  keys.filter (fun k => ValidStage (cache768 h768 cache) l s (k.cast h768))

noncomputable def cacheWeight (h768 : COMPRESSION_INPUT_LENGTH = 768) (cache : CompressionCache)
    (keys : Finset CompressionSpec.Domain) : Nat :=
  (unchainedSet h768 keys).card +
  ∑ l ∈ Finset.Icc 9 16, levelChain l * (stageSet h768 cache keys l (levelChain l)).card

private theorem mem_unchainedSet {h768 : COMPRESSION_INPUT_LENGTH = 768}
    {keys : Finset CompressionSpec.Domain} {k : CompressionSpec.Domain} :
    k ∈ unchainedSet h768 keys ↔ k ∈ keys ∧ isUnchainedBin (k.cast h768) := by
  classical
  simp [unchainedSet]

private theorem mem_stageSet {h768 : COMPRESSION_INPUT_LENGTH = 768} {cache : CompressionCache}
    {keys : Finset CompressionSpec.Domain} {l s : Nat} {k : CompressionSpec.Domain} :
    k ∈ stageSet h768 cache keys l s ↔ k ∈ keys ∧ ValidStage (cache768 h768 cache) l s (k.cast h768) := by
  classical
  simp [stageSet]

/-- Stage-parent injectivity: for every `l ∈ [9..16]` and `s ≥ 1`, each valid stage-`(s+1)`
input uniquely determines its valid stage-`s` parent in the exact cache domain. -/
private theorem stageSet_card_succ_le (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (keys : Finset CompressionSpec.Domain)
    (hexact : ∀ k, k ∈ keys ↔ cache k ≠ none) (l s : Nat) (hs : 1 ≤ s) :
    (stageSet h768 cache keys l (s + 1)).card ≤ (stageSet h768 cache keys l s).card := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  have hpar : ∀ k ∈ stageSet h768 cache keys l (r + 2),
      ∃ p : CompressionSpec.Domain, p ∈ stageSet h768 cache keys l (r + 1) ∧
        cache p = some ((k.cast h768).extractLsb' 0 256) := by
    intro k hk
    obtain ⟨_, _, _, p, hp, hmp⟩ := mem_stageSet.mp hk
    refine ⟨p.cast h768.symm, mem_stageSet.mpr ⟨?_, by simpa using hp⟩, hmp⟩
    rw [hexact]
    intro hnone
    have hs' := validStage_isSome hp
    have h1 : cache768 h768 cache p = none := hnone
    rw [h1] at hs'
    cases hs'
  let f : CompressionSpec.Domain → CompressionSpec.Domain := fun k =>
    if h : k ∈ stageSet h768 cache keys l (r + 2) then Classical.choose (hpar k h) else k
  have hmaps : Set.MapsTo f (stageSet h768 cache keys l (r + 2) : Set CompressionSpec.Domain)
      (stageSet h768 cache keys l (r + 1) : Set CompressionSpec.Domain) := by
    intro k hk
    have hk' : k ∈ stageSet h768 cache keys l (r + 2) := hk
    change f k ∈ stageSet h768 cache keys l (r + 1)
    simp only [f, dif_pos hk']
    exact (Classical.choose_spec (hpar k hk')).1
  have hinj : Set.InjOn f (stageSet h768 cache keys l (r + 2) : Set CompressionSpec.Domain) := by
    intro k1 hk1 k2 hk2 hfeq
    have hk1' : k1 ∈ stageSet h768 cache keys l (r + 2) := hk1
    have hk2' : k2 ∈ stageSet h768 cache keys l (r + 2) := hk2
    have hsp1 := (Classical.choose_spec (hpar k1 hk1')).2
    have hsp2 := (Classical.choose_spec (hpar k2 hk2')).2
    simp only [f, dif_pos hk1', dif_pos hk2'] at hfeq
    rw [hfeq] at hsp1
    have hprev : (k1.cast h768).extractLsb' 0 256 = (k2.cast h768).extractLsb' 0 256 := by
      have := hsp1.symm.trans hsp2
      exact Option.some.inj this
    have hcast : k1.cast h768 = k2.cast h768 :=
      isStage_eq_of_prev_eq (by omega)
        (validStage_isStage (mem_stageSet.mp hk1').2)
        (validStage_isStage (mem_stageSet.mp hk2').2) hprev
    have := congrArg (BitVec.cast h768.symm) hcast
    simpa using this
  exact Finset.card_le_card_of_injOn f hmaps hinj

private theorem stageSet_card_ge_final (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (keys : Finset CompressionSpec.Domain)
    (hexact : ∀ k, k ∈ keys ↔ cache k ≠ none) (l s : Nat) (hs1 : 1 ≤ s)
    (hs2 : s ≤ levelChain l) :
    (stageSet h768 cache keys l (levelChain l)).card ≤ (stageSet h768 cache keys l s).card := by
  obtain ⟨d, hd⟩ : ∃ d, levelChain l = s + d := ⟨levelChain l - s, by omega⟩
  rw [hd]
  clear hd hs2
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    rw [show s + (d + 1) = (s + d) + 1 by omega]
    exact (stageSet_card_succ_le h768 cache keys hexact l (s + d) (by omega)).trans ih

private theorem stageSet_biUnion_card_le (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (keys : Finset CompressionSpec.Domain)
    (pairs : Finset (Nat × Nat)) :
    (unchainedSet h768 keys).card +
      ∑ p ∈ pairs, (stageSet h768 cache keys p.1 p.2).card ≤ keys.card := by
  classical
  have hdisj_pairs : Set.PairwiseDisjoint (pairs : Set (Nat × Nat))
      (fun p => stageSet h768 cache keys p.1 p.2) := by
    intro p1 _ p2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have hv1 := validStage_isStage (mem_stageSet.mp hk1).2
    have hv2 := validStage_isStage (mem_stageSet.mp hk2).2
    obtain ⟨hl, hs⟩ := isStage_unique hv1 hv2
    exact hne (Prod.ext hl hs)
  have hcard_biUnion :
      ∑ p ∈ pairs, (stageSet h768 cache keys p.1 p.2).card =
      (pairs.biUnion (fun p => stageSet h768 cache keys p.1 p.2)).card :=
    (Finset.card_biUnion hdisj_pairs).symm
  have hdisj_u : Disjoint (unchainedSet h768 keys)
      (pairs.biUnion (fun p => stageSet h768 cache keys p.1 p.2)) := by
    rw [Finset.disjoint_left]
    intro k hku hks
    obtain ⟨p, _, hkp⟩ := Finset.mem_biUnion.mp hks
    exact not_isUnchainedBin_of_isStage (validStage_isStage (mem_stageSet.mp hkp).2)
      (mem_unchainedSet.mp hku).2
  have hsub : unchainedSet h768 keys ∪ pairs.biUnion (fun p => stageSet h768 cache keys p.1 p.2) ⊆ keys := by
    intro k hk
    rcases Finset.mem_union.mp hk with hku | hks
    · exact (mem_unchainedSet.mp hku).1
    · obtain ⟨p, _, hkp⟩ := Finset.mem_biUnion.mp hks
      exact (mem_stageSet.mp hkp).1
  rw [hcard_biUnion, ← Finset.card_union_of_disjoint hdisj_u]
  exact Finset.card_le_card hsub

/-- Core banked-credit invariant: the weighted output count NEVER exceeds total cache cardinality. -/
private theorem cacheWeight_le_card (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (keys : Finset CompressionSpec.Domain)
    (hexact : ∀ k, k ∈ keys ↔ cache k ≠ none) :
    cacheWeight h768 cache keys ≤ keys.card := by
  classical
  have hchain_le : ∀ l ∈ Finset.Icc 9 16,
      levelChain l * (stageSet h768 cache keys l (levelChain l)).card ≤
      ∑ s ∈ Finset.Icc 1 (levelChain l), (stageSet h768 cache keys l s).card := by
    intro l hl
    calc
      levelChain l * (stageSet h768 cache keys l (levelChain l)).card
        = ∑ _s ∈ Finset.Icc 1 (levelChain l), (stageSet h768 cache keys l (levelChain l)).card := by
          rw [Finset.sum_const, Nat.card_Icc, show levelChain l + 1 - 1 = levelChain l by omega, smul_eq_mul]
      _ ≤ ∑ s ∈ Finset.Icc 1 (levelChain l), (stageSet h768 cache keys l s).card := by
          apply Finset.sum_le_sum
          intro s hs
          have hs' := Finset.mem_Icc.mp hs
          exact stageSet_card_ge_final h768 cache keys hexact l s hs'.1 hs'.2
  let pairs : Finset (Nat × Nat) :=
    (Finset.Icc 9 16).biUnion (fun l => (Finset.Icc 1 (levelChain l)).image (fun s => (l, s)))
  have hsum_pairs :
      ∑ l ∈ Finset.Icc 9 16, ∑ s ∈ Finset.Icc 1 (levelChain l), (stageSet h768 cache keys l s).card =
      ∑ p ∈ pairs, (stageSet h768 cache keys p.1 p.2).card := by
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_image]
      intro s1 _ s2 _ h; exact (Prod.mk.inj h).2
    · intro l1 _ l2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp1
      obtain ⟨_, _, h2⟩ := Finset.mem_image.mp hp2
      exact hne (Prod.mk.inj h2).1.symm
  calc
    cacheWeight h768 cache keys
      ≤ (unchainedSet h768 keys).card +
        ∑ l ∈ Finset.Icc 9 16, ∑ s ∈ Finset.Icc 1 (levelChain l), (stageSet h768 cache keys l s).card :=
          Nat.add_le_add_left (Finset.sum_le_sum hchain_le) _
    _ = (unchainedSet h768 keys).card + ∑ p ∈ pairs, (stageSet h768 cache keys p.1 p.2).card := by
          rw [hsum_pairs]
    _ ≤ keys.card := stageSet_biUnion_card_le h768 cache keys pairs

/-- Exact weight delta on a safe (`¬ FreshBad256`) fresh query. -/
private theorem cacheWeight_insert_of_safe (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (keys : Finset CompressionSpec.Domain)
    (hexact : ∀ k, k ∈ keys ↔ cache k ≠ none)
    (input : CompressionSpec.Domain) (ans : Digest)
    (hnone : cache input = none) (hsafe : ¬ FreshBad256 h768 cache input ans) :
    let cache' := cache.cacheQuery input ans
    let keys' := insert input keys
    (isUnchainedBin (input.cast h768) →
      cacheWeight h768 cache' keys' = cacheWeight h768 cache keys + 1) ∧
    (∀ l, 9 ≤ l → l ≤ 16 → ReadyStage (cache768 h768 cache) l (levelChain l) (input.cast h768) →
      cacheWeight h768 cache' keys' = cacheWeight h768 cache keys + levelChain l) ∧
    (¬ isUnchainedBin (input.cast h768) →
      (∀ l, 9 ≤ l → l ≤ 16 → ¬ ReadyStage (cache768 h768 cache) l (levelChain l) (input.cast h768)) →
      cacheWeight h768 cache' keys' = cacheWeight h768 cache keys) := by
  classical
  dsimp only
  have hnotmem : input ∉ keys := fun h => (hexact input).mp h hnone
  have hstage_eq : ∀ l, 9 ≤ l → l ≤ 16 →
      (¬ ReadyStage (cache768 h768 cache) l (levelChain l) (input.cast h768)) →
      stageSet h768 (cache.cacheQuery input ans) (insert input keys) l (levelChain l) =
      stageSet h768 cache keys l (levelChain l) := by
    intro l _ _ hnr
    ext k
    simp only [mem_stageSet, Finset.mem_insert]
    by_cases hki : k = input
    · subst hki
      simp only [hnotmem, false_and, iff_false, not_and]
      intro _ hv
      exact hnr ((validStage_cacheQuery_self h768 cache k ans hnone hsafe l (levelChain l)).mp hv)
    · have hne : k.cast h768 ≠ input.cast h768 := fun h => hki (by simpa using congrArg (BitVec.cast h768.symm) h)
      simp only [hki, false_or, validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l (levelChain l) _ hne]
  have hstage_ins : ∀ l, 9 ≤ l → l ≤ 16 →
      ReadyStage (cache768 h768 cache) l (levelChain l) (input.cast h768) →
      stageSet h768 (cache.cacheQuery input ans) (insert input keys) l (levelChain l) =
      insert input (stageSet h768 cache keys l (levelChain l)) := by
    intro l _ _ hr
    ext k
    simp only [mem_stageSet, Finset.mem_insert]
    by_cases hki : k = input
    · subst hki
      simp only [true_or, true_and, iff_true]
      exact (validStage_cacheQuery_self h768 cache k ans hnone hsafe l (levelChain l)).mpr hr
    · have hne : k.cast h768 ≠ input.cast h768 := fun h => hki (by simpa using congrArg (BitVec.cast h768.symm) h)
      simp only [hki, false_or, validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l (levelChain l) _ hne]
  refine ⟨?_, ?_, ?_⟩
  · intro hu
    have hu_eq : unchainedSet h768 (insert input keys) = insert input (unchainedSet h768 keys) := by
      ext k; simp only [mem_unchainedSet, Finset.mem_insert]
      by_cases hki : k = input
      · subst hki; simp [hu]
      · simp [hki]
    have hnotu : input ∉ unchainedSet h768 keys := fun h => hnotmem (mem_unchainedSet.mp h).1
    have hsum : ∑ l ∈ Finset.Icc 9 16,
        levelChain l * (stageSet h768 (cache.cacheQuery input ans) (insert input keys) l (levelChain l)).card =
        ∑ l ∈ Finset.Icc 9 16, levelChain l * (stageSet h768 cache keys l (levelChain l)).card := by
      apply Finset.sum_congr rfl
      intro l hl
      have hl' := Finset.mem_Icc.mp hl
      rw [hstage_eq l hl'.1 hl'.2 (fun hr => not_isUnchainedBin_of_isStage (readyStage_isStage hr) hu)]
    unfold cacheWeight
    rw [hu_eq, Finset.card_insert_of_notMem hnotu, hsum]
    omega
  · intro l hl1 hl2 hr
    have hu_eq : unchainedSet h768 (insert input keys) = unchainedSet h768 keys := by
      ext k; simp only [mem_unchainedSet, Finset.mem_insert]
      by_cases hki : k = input
      · subst hki
        simp [hnotmem, not_isUnchainedBin_of_isStage (readyStage_isStage hr)]
      · simp [hki]
    have hlmem : l ∈ Finset.Icc 9 16 := Finset.mem_Icc.mpr ⟨hl1, hl2⟩
    have hnots : input ∉ stageSet h768 cache keys l (levelChain l) := fun h => hnotmem (mem_stageSet.mp h).1
    have hsum : ∑ j ∈ Finset.Icc 9 16,
        levelChain j * (stageSet h768 (cache.cacheQuery input ans) (insert input keys) j (levelChain j)).card =
        (∑ j ∈ Finset.Icc 9 16, levelChain j * (stageSet h768 cache keys j (levelChain j)).card) + levelChain l := by
      rw [← Finset.add_sum_erase _ _ hlmem, ← Finset.add_sum_erase _ _ hlmem]
      rw [hstage_ins l hl1 hl2 hr, Finset.card_insert_of_notMem hnots, Nat.mul_add, Nat.mul_one]
      have hrest : ∑ j ∈ (Finset.Icc 9 16).erase l,
          levelChain j * (stageSet h768 (cache.cacheQuery input ans) (insert input keys) j (levelChain j)).card =
          ∑ j ∈ (Finset.Icc 9 16).erase l, levelChain j * (stageSet h768 cache keys j (levelChain j)).card := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjl : j ≠ l := (Finset.mem_erase.mp hj).1
        have hj' := Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2
        rw [hstage_eq j hj'.1 hj'.2 (fun hrj => hjl (isStage_unique (readyStage_isStage hrj) (readyStage_isStage hr)).1)]
      rw [hrest]; omega
    unfold cacheWeight
    rw [hu_eq, hsum]; omega
  · intro hnu hnr
    have hu_eq : unchainedSet h768 (insert input keys) = unchainedSet h768 keys := by
      ext k; simp only [mem_unchainedSet, Finset.mem_insert]
      by_cases hki : k = input
      · subst hki; simp [hnotmem, hnu]
      · simp [hki]
    have hsum : ∑ l ∈ Finset.Icc 9 16,
        levelChain l * (stageSet h768 (cache.cacheQuery input ans) (insert input keys) l (levelChain l)).card =
        ∑ l ∈ Finset.Icc 9 16, levelChain l * (stageSet h768 cache keys l (levelChain l)).card := by
      apply Finset.sum_congr rfl
      intro l hl
      have hl' := Finset.mem_Icc.mp hl
      rw [hstage_eq l hl'.1 hl'.2 (hnr l hl'.1 hl'.2)]
    unfold cacheWeight
    rw [hu_eq, hsum]

private theorem card_lowWidth_preimage (w : Nat) (hw : w ≤ 256) (targets : Finset (BitVec w))
    [DecidablePred (fun ans : Digest => lowWidth w ans ∈ targets)] :
    (Finset.univ.filter (fun ans : Digest => lowWidth w ans ∈ targets)).card ≤
      2 ^ (256 - w) * targets.card := by
  have hinj : Set.InjOn (fun ans : Digest => (ans.extractLsb' w (256 - w), lowWidth w ans))
      (Finset.univ.filter (fun ans : Digest => lowWidth w ans ∈ targets) : Set Digest) := by
    intro a _ b _ h
    have hhi : a.extractLsb' w (256 - w) = b.extractLsb' w (256 - w) := congrArg Prod.fst h
    have hlo : lowWidth w a = lowWidth w b := congrArg Prod.snd h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hlt : i < w
    · have := congrArg (fun v : BitVec w => v.getLsbD i) hlo
      simpa only [lowWidth, BitVec.getLsbD_extractLsb', hlt, decide_true, Bool.true_and, Nat.zero_add] using this
    · have hi' : i - w < 256 - w := by omega
      have := congrArg (fun v : BitVec (256 - w) => v.getLsbD (i - w)) hhi
      simpa only [BitVec.getLsbD_extractLsb', hi', decide_true, Bool.true_and,
        show w + (i - w) = i by omega] using this
  have hmaps : Set.MapsTo (fun ans : Digest => (ans.extractLsb' w (256 - w), lowWidth w ans))
      (Finset.univ.filter (fun ans : Digest => lowWidth w ans ∈ targets) : Set Digest)
      ((Finset.univ ×ˢ targets : Finset (BitVec (256 - w) × BitVec w)) : Set (BitVec (256 - w) × BitVec w)) := by
    intro ans hans
    rw [Finset.mem_coe, Finset.mem_filter] at hans
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨Finset.mem_univ _, hans.2⟩
  calc
    (Finset.univ.filter (fun ans : Digest => lowWidth w ans ∈ targets)).card
      ≤ (Finset.univ ×ˢ targets : Finset (BitVec (256 - w) × BitVec w)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (Finset.univ : Finset (BitVec (256 - w))).card * targets.card := Finset.card_product _ _
    _ = 2 ^ (256 - w) * targets.card := by rw [Finset.card_univ, Fintype.card_bitVec]

private theorem card_freshBad256_le (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (keys : Finset CompressionSpec.Domain)
    (hexact : ∀ k, k ∈ keys ↔ cache k ≠ none) (input : CompressionSpec.Domain)
    [DecidablePred (FreshBad256 h768 cache input)] :
    (Finset.univ.filter (FreshBad256 h768 cache input)).card ≤ 2 * keys.card + 1 := by
  classical
  let s1 : Finset Digest := keys.biUnion (fun k => match (cache k : Option Digest) with | some v => {v} | none => ∅)
  let s2 : Finset Digest := keys.image (fun k => (k.cast h768).extractLsb' 0 256)
  let s3 : Finset Digest := {(input.cast h768).extractLsb' 0 256}
  have hsub : Finset.univ.filter (FreshBad256 h768 cache input) ⊆ s1 ∪ s2 ∪ s3 := by
    intro ans hans
    have hb := (Finset.mem_filter.mp hans).2
    rcases hb with ⟨k, v, hkv, rfl⟩ | ⟨k, hkn, rfl⟩ | rfl
    · apply Finset.mem_union_left; apply Finset.mem_union_left
      have hkv' : (cache k : Option Digest) = some v := hkv
      exact Finset.mem_biUnion.mpr ⟨k, (hexact k).mpr (by intro hnone; rw [hnone] at hkv; cases hkv),
        by rw [hkv']; exact Finset.mem_singleton_self v⟩
    · apply Finset.mem_union_left; apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨k, (hexact k).mpr hkn, rfl⟩
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hs1 : s1.card ≤ keys.card := by
    calc
      s1.card ≤ ∑ k ∈ keys, (match (cache k : Option Digest) with | some v => ({v} : Finset Digest) | none => ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ keys, 1 := by
          apply Finset.sum_le_sum; intro k _
          cases (cache k : Option Digest) with
          | none => simp
          | some v => exact (Finset.card_singleton v).le
      _ = keys.card := by simp
  have hs2 : s2.card ≤ keys.card := Finset.card_image_le
  have hs3 : s3.card = 1 := Finset.card_singleton _
  calc
    (Finset.univ.filter (FreshBad256 h768 cache input)).card
      ≤ (s1 ∪ s2 ∪ s3).card := Finset.card_le_card hsub
    _ ≤ (s1 ∪ s2).card + s3.card := Finset.card_union_le _ _
    _ ≤ s1.card + s2.card + s3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 2 * keys.card + 1 := by omega

/-- Existence of a safe answer implies `cacheWeight + c ≤ keys.card + 1` in Case 2. -/
private theorem exists_safe_ans (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (keys : Finset CompressionSpec.Domain)
    (hexact : ∀ k, k ∈ keys ↔ cache k ≠ none) (input : CompressionSpec.Domain)
    (hsmall : 2 * keys.card + 1 < 2 ^ 256) :
    ∃ ans : Digest, ¬ FreshBad256 h768 cache input ans := by
  classical
  have hbad := card_freshBad256_le h768 cache keys hexact input
  have hlt : (Finset.univ.filter (FreshBad256 h768 cache input)).card < (Finset.univ : Finset Digest).card := by
    rw [Finset.card_univ, Fintype.card_bitVec]; omega
  by_contra hall
  push_neg at hall
  have heq : Finset.univ.filter (FreshBad256 h768 cache input) = Finset.univ := by
    ext ans; simp [hall ans]
  rw [heq] at hlt
  exact lt_irrefl _ hlt

noncomputable def survFactor (k : Nat) : ENNReal :=
  ((2 ^ 238 - k : Nat) : ENNReal) / 2 ^ 238

private theorem survFactor_le_one (k : Nat) : survFactor k ≤ 1 := by
  unfold survFactor
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by positivity)) (Or.inl (by finiteness)), one_mul]
  exact_mod_cast Nat.sub_le (2 ^ 238) k

private theorem survFactor_anti {a b : Nat} (h : a ≤ b) : survFactor b ≤ survFactor a := by
  unfold survFactor
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.sub_le_sub_left h _)) _

private theorem one_le_survFactor_add (k : Nat) (hk : k ≤ 2 ^ 238) :
    (1 : ENNReal) ≤ survFactor k + (k : ENNReal) / 2 ^ 238 := by
  unfold survFactor
  rw [← ENNReal.add_div, ← Nat.cast_add, Nat.sub_add_cancel hk, Nat.cast_pow, Nat.cast_ofNat]
  exact (ENNReal.div_self (by positivity) (by finiteness)).ge

/-- Core 6-line `Nat` chain survival inequality: shifting `survFactor` by `+ 4096` absorbs
the second-order `(1 - y)^c` term for every `W ≤ 2^121` and `1 ≤ c ≤ 16`. -/
private theorem nat_chain_surv_pow (W c : Nat) (hW : W ≤ 2 ^ 121) (hc1 : 1 ≤ c) (hc2 : c ≤ 16) :
    (2 ^ 238 - (W + 4096)) ^ c + c * W * (2 ^ 238) ^ (c - 1) ≤ (2 ^ 238) ^ c := by
  set N := 2 ^ 238
  set a := W + 4096
  have ha_le : a ≤ N := by
    have : 2 ^ 121 + 4096 ≤ 2 ^ 238 := by decide
    omega
  have hquad : ∀ k, k ≤ 15 → k * W * a ≤ 4096 * N := by
    intro k hk
    have h1 : k * W * a ≤ 15 * 2 ^ 121 * (2 ^ 121 + 4096) :=
      Nat.mul_le_mul (Nat.mul_le_mul hk hW) (by omega)
    have h2 : 15 * 2 ^ 121 * (2 ^ 121 + 4096) ≤ 4096 * 2 ^ 238 := by decide
    exact h1.trans h2
  have hind : ∀ k, 1 ≤ k → k ≤ 16 → (N - a) ^ k + k * W * N ^ (k - 1) ≤ N ^ k := by
    intro k hk1 hk2
    induction k with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simp only [Nat.zero_add, Nat.sub_self, pow_one, pow_zero, mul_one, one_mul]; omega
      | succ k' =>
        have hih := ih (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hih
        have hmul := Nat.mul_le_mul_right (N - a) hih
        rw [Nat.add_mul, ← pow_succ] at hmul
        have hsplit1 : (k' + 1) * W * N ^ k' * (N - a) + (k' + 1) * W * a * N ^ k' =
            (k' + 1) * W * N ^ (k' + 1) := by
          have : (k' + 1) * W * N ^ k' * (N - a) + (k' + 1) * W * N ^ k' * a =
              (k' + 1) * W * N ^ k' * N := by
            rw [← Nat.mul_add, Nat.sub_add_cancel ha_le]
          calc
            (k' + 1) * W * N ^ k' * (N - a) + (k' + 1) * W * a * N ^ k'
              = (k' + 1) * W * N ^ k' * (N - a) + (k' + 1) * W * N ^ k' * a := by ring
            _ = (k' + 1) * W * N ^ k' * N := this
            _ = (k' + 1) * W * N ^ (k' + 1) := by rw [pow_succ]; ring
        have hsplit2 : N ^ (k' + 1) * (N - a) + a * N ^ (k' + 1) = N ^ (k' + 2) := by
          calc
            N ^ (k' + 1) * (N - a) + a * N ^ (k' + 1)
              = N ^ (k' + 1) * (N - a) + N ^ (k' + 1) * a := by ring
            _ = N ^ (k' + 1) * N := by rw [← Nat.mul_add, Nat.sub_add_cancel ha_le]
            _ = N ^ (k' + 2) := (pow_succ N (k' + 1)).symm
        have hq := Nat.mul_le_mul_right (N ^ k') (hquad (k' + 1) (by omega))
        have hq' : (k' + 1) * W * a * N ^ k' ≤ 4096 * N ^ (k' + 1) := by
          calc
            (k' + 1) * W * a * N ^ k' ≤ 4096 * N * N ^ k' := hq
            _ = 4096 * N ^ (k' + 1) := by rw [pow_succ]; ring
        have hcomb : (N - a) ^ (k' + 2) + (k' + 1) * W * N ^ (k' + 1) + W * N ^ (k' + 1) ≤
            N ^ (k' + 1) * (N - a) + a * N ^ (k' + 1) := by
          have hadd := Nat.add_le_add (Nat.add_le_add hmul hq') (le_refl (W * N ^ (k' + 1)))
          have hL : (N - a) ^ (k' + 2) + (k' + 1) * W * N ^ k' * (N - a) +
              (k' + 1) * W * a * N ^ k' + W * N ^ (k' + 1) =
              (N - a) ^ (k' + 2) + (k' + 1) * W * N ^ (k' + 1) + W * N ^ (k' + 1) := by
            have := hsplit1; omega
          have hR : N ^ (k' + 1) * (N - a) + 4096 * N ^ (k' + 1) + W * N ^ (k' + 1) =
              N ^ (k' + 1) * (N - a) + a * N ^ (k' + 1) := by
            dsimp only [a]; ring
          linarith
        have hL2 : (N - a) ^ (k' + 2) + (k' + 2) * W * N ^ (k' + 1) =
            (N - a) ^ (k' + 2) + (k' + 1) * W * N ^ (k' + 1) + W * N ^ (k' + 1) := by ring
        change (N - a) ^ (k' + 2) + (k' + 2) * W * N ^ (k' + 1) ≤ N ^ (k' + 2)
        rw [hL2]; exact hcomb.trans_eq hsplit2
  exact hind c hc1 hc2

private theorem prod_survFactor_le_chain_surv (W c w m_l : Nat)
    (hW : W ≤ 2 ^ 121) (hc1 : 1 ≤ c) (hc2 : c ≤ 16) (hw : w ≤ 256)
    (hsec : 2 ^ 238 ≤ c ^ 2 * 2 ^ w) (hcm : c * m_l ≤ W) :
    (∏ j ∈ Finset.range c, survFactor (W + j + 4096)) ≤
      ((2 ^ 256 - 2 ^ (256 - w) * m_l : Nat) : ENNReal) / 2 ^ 256 := by
  have hprod_le : (∏ j ∈ Finset.range c, survFactor (W + j + 4096)) ≤ (survFactor (W + 4096)) ^ c := by
    calc
      (∏ j ∈ Finset.range c, survFactor (W + j + 4096))
        ≤ ∏ _j ∈ Finset.range c, survFactor (W + 4096) :=
          Finset.prod_le_prod' fun j _ => survFactor_anti (by omega)
      _ = (survFactor (W + 4096)) ^ c := by rw [Finset.prod_const, Finset.card_range]
  have hcw_le : c * W ≤ 2 ^ 238 := by
    have : 16 * 2 ^ 121 ≤ 2 ^ 238 := by decide
    exact (Nat.mul_le_mul hc2 hW).trans this
  have hml_le : 2 ^ (256 - w) * m_l ≤ 2 ^ 18 * (c * W) := by
    have h1 : 2 ^ 238 * m_l ≤ c ^ 2 * 2 ^ w * m_l := Nat.mul_le_mul_right m_l hsec
    have h2 : c ^ 2 * 2 ^ w * m_l = 2 ^ w * (c * (c * m_l)) := by ring
    have h3 : 2 ^ w * (c * (c * m_l)) ≤ 2 ^ w * (c * W) :=
      Nat.mul_le_mul_left (2 ^ w) (Nat.mul_le_mul_left c hcm)
    have h4 : 2 ^ 256 * m_l ≤ 2 ^ w * (2 ^ 18 * (c * W)) := by
      calc
        2 ^ 256 * m_l = 2 ^ 18 * (2 ^ 238 * m_l) := by rw [← Nat.mul_assoc, ← pow_add]
        _ ≤ 2 ^ 18 * (2 ^ w * (c * W)) := Nat.mul_le_mul_left _ (h1.trans (h2 ▸ h3))
        _ = 2 ^ w * (2 ^ 18 * (c * W)) := by ring
    have h5 : 2 ^ w * (2 ^ (256 - w) * m_l) = 2 ^ 256 * m_l := by
      rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le hw]
    exact Nat.le_of_mul_le_mul_left (h5.symm ▸ h4) (by positivity)
  have hpow_nat : (2 ^ 238 - (W + 4096)) ^ c ≤ (2 ^ 238 - c * W) * (2 ^ 238) ^ (c - 1) := by
    have hbase := nat_chain_surv_pow W c hW hc1 hc2
    have hsub : (2 ^ 238 - c * W) * (2 ^ 238) ^ (c - 1) + c * W * (2 ^ 238) ^ (c - 1) = (2 ^ 238) ^ c := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hcw_le, ← pow_succ', show c - 1 + 1 = c by omega]
    omega
  have hpow_enn : (survFactor (W + 4096)) ^ c ≤ survFactor (c * W) := by
    unfold survFactor
    rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
    have hden : ((2 : ENNReal) ^ 238) ^ c = (2 : ENNReal) ^ 238 * ((2 : ENNReal) ^ 238) ^ (c - 1) := by
      rw [← pow_succ', show c - 1 + 1 = c by omega]
    calc
      (((2 ^ 238 - (W + 4096) : Nat) : ENNReal) ^ c) / ((2 : ENNReal) ^ 238) ^ c
        = (((2 ^ 238 - (W + 4096)) ^ c : Nat) : ENNReal) / ((2 : ENNReal) ^ 238) ^ c := by
            rw [Nat.cast_pow]
      _ ≤ ((((2 ^ 238 - c * W) * (2 ^ 238) ^ (c - 1) : Nat)) : ENNReal) / ((2 : ENNReal) ^ 238) ^ c :=
            ENNReal.div_le_div_right (Nat.cast_le.mpr hpow_nat) _
      _ = (((2 ^ 238 - c * W : Nat) : ENNReal) * ((2 : ENNReal) ^ 238) ^ (c - 1)) /
            ((2 : ENNReal) ^ 238 * ((2 : ENNReal) ^ 238) ^ (c - 1)) := by
            rw [hden, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
      _ = ((2 ^ 238 - c * W : Nat) : ENNReal) / 2 ^ 238 :=
            ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)
  have hsurv_le : survFactor (c * W) ≤ ((2 ^ 256 - 2 ^ (256 - w) * m_l : Nat) : ENNReal) / 2 ^ 256 := by
    unfold survFactor
    have hmul : 2 ^ 18 * (2 ^ 238 - c * W) = 2 ^ 256 - 2 ^ 18 * (c * W) := by
      rw [Nat.mul_sub_left_distrib, show 2 ^ 18 * 2 ^ 238 = 2 ^ 256 by decide]
    calc
      ((2 ^ 238 - c * W : Nat) : ENNReal) / 2 ^ 238
        = ((2 ^ 18 * (2 ^ 238 - c * W) : Nat) : ENNReal) / 2 ^ 256 := by
            simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            rw [show (2 : ENNReal) ^ 256 = 2 ^ 18 * 2 ^ 238 by rw [← pow_add]]
            exact (ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)).symm
      _ ≤ ((2 ^ 256 - 2 ^ (256 - w) * m_l : Nat) : ENNReal) / 2 ^ 256 := by
            apply ENNReal.div_le_div_right
            rw [hmul]
            exact Nat.cast_le.mpr (Nat.sub_le_sub_left hml_le _)
  exact hprod_le.trans (hpow_enn.trans hsurv_le)

/-- Single fresh-query survival bound: classifies `input` into Case 1 (unchained binary, cost 1),
Case 2 (final stage of level `l ∈ [9..16]`, cost `c_l`), or Case 3 (other, cost 0). -/
private theorem fresh_step_bound (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache : CompressionCache) (keys : Finset CompressionSpec.Domain)
    (hexact : ∀ k, k ∈ keys ↔ cache k ≠ none)
    (noBad : ¬ CacheBad h768 cache) (input : CompressionSpec.Domain)
    (hnone : cache input = none) (hW : cacheWeight h768 cache keys ≤ 2 ^ 121)
    (hksmall : 2 * keys.card + 1 < 2 ^ 256) :
    ∃ stepCost : Nat,
      cacheWeight h768 cache keys + stepCost ≤ keys.card + 1 ∧
      (∀ ans : Digest, ¬ FreshBad256 h768 cache input ans →
        cacheWeight h768 (cache.cacheQuery input ans) (insert input keys) =
          cacheWeight h768 cache keys + stepCost) ∧
      (∏ j ∈ Finset.range stepCost, survFactor (cacheWeight h768 cache keys + j + 4096)) ≤
        prEvent ((fun ans => ¬ CacheBad h768 (cache.cacheQuery input ans) ∧
            ¬ FreshBad256 h768 cache input ans) <$> ($ᵗ CompressionSpec.Range input)) +
        ((2 * keys.card + 1 : Nat) : ENNReal) / 2 ^ 256 := by
  classical
  set W := cacheWeight h768 cache keys
  have hcol256_safe : ∀ ans, ¬ FreshBad256 h768 cache input ans →
      ¬ CacheCol256 (cache.cacheQuery input ans) := by
    intro ans hsafe ⟨x, y, vx, vy, hne, hx, hy, hv⟩
    by_cases hxi : x = input
    · subst hxi
      erw [QueryCache.cacheQuery_self cache x ans] at hx
      erw [QueryCache.cacheQuery_of_ne cache ans (Ne.symm hne)] at hy
      cases hx
      exact hsafe (Or.inl ⟨y, vy, hy, hv.symm⟩)
    · by_cases hyi : y = input
      · subst hyi
        erw [QueryCache.cacheQuery_of_ne cache ans hxi] at hx
        erw [QueryCache.cacheQuery_self cache y ans] at hy
        cases hy
        exact hsafe (Or.inl ⟨x, vx, hx, hv⟩)
      · erw [QueryCache.cacheQuery_of_ne cache ans hxi] at hx
        erw [QueryCache.cacheQuery_of_ne cache ans hyi] at hy
        exact noBad (Or.inl ⟨x, y, vx, vy, hne, hx, hy, hv⟩)
  have hgood_of_card : ∀ (B : Nat) (hB : B ≤ 2 ^ 256),
      (Finset.univ.filter (fun ans : Digest =>
        CacheBad h768 (cache.cacheQuery input ans) ∨ FreshBad256 h768 cache input ans)).card ≤
        B + (2 * keys.card + 1) →
      ((2 ^ 256 - B : Nat) : ENNReal) / 2 ^ 256 ≤
        prEvent ((fun ans => ¬ CacheBad h768 (cache.cacheQuery input ans) ∧
            ¬ FreshBad256 h768 cache input ans) <$> ($ᵗ CompressionSpec.Range input)) +
        ((2 * keys.card + 1 : Nat) : ENNReal) / 2 ^ 256 := by
    intro B hB hcard_bad
    have hpart :
        (Finset.univ.filter (fun ans : Digest =>
          CacheBad h768 (cache.cacheQuery input ans) ∨ FreshBad256 h768 cache input ans)).card +
        (Finset.univ.filter (fun ans : Digest =>
          ¬ CacheBad h768 (cache.cacheQuery input ans) ∧ ¬ FreshBad256 h768 cache input ans)).card =
        2 ^ 256 := by
      rw [← Finset.card_union_of_disjoint]
      · have : Finset.univ.filter (fun ans : Digest =>
            CacheBad h768 (cache.cacheQuery input ans) ∨ FreshBad256 h768 cache input ans) ∪
          Finset.univ.filter (fun ans : Digest =>
            ¬ CacheBad h768 (cache.cacheQuery input ans) ∧ ¬ FreshBad256 h768 cache input ans) =
          Finset.univ := by
          ext ans; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          by_cases h1 : CacheBad h768 (cache.cacheQuery input ans) <;>
            by_cases h2 : FreshBad256 h768 cache input ans <;> simp [h1, h2]
        rw [this, Finset.card_univ, Fintype.card_bitVec]
      · rw [Finset.disjoint_left]; intro a ha1 ha2
        have h1 := (Finset.mem_filter.mp ha1).2
        have h2 := (Finset.mem_filter.mp ha2).2
        rcases h1 with hc | hf
        · exact h2.1 hc
        · exact h2.2 hf
    have hnat : 2 ^ 256 - B ≤
        (Finset.univ.filter (fun ans : Digest =>
          ¬ CacheBad h768 (cache.cacheQuery input ans) ∧ ¬ FreshBad256 h768 cache input ans)).card +
        (2 * keys.card + 1) := by omega
    change ((2 ^ 256 - B : Nat) : ENNReal) / 2 ^ 256 ≤
      prEvent ((fun ans : Digest => ¬ CacheBad h768 (cache.cacheQuery input ans) ∧
          ¬ FreshBad256 h768 cache input ans) <$> ($ᵗ Digest)) + _
    rw [SampleableType.prEvent_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat,
      ← ENNReal.add_div, ← Nat.cast_add]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr hnat) _
  by_cases hu : isUnchainedBin (input.cast h768)
  · refine ⟨1, ?_, ?_, ?_⟩
    · exact Nat.add_le_add_right (cacheWeight_le_card h768 cache keys hexact) 1
    · intro ans hsafe
      exact (cacheWeight_insert_of_safe h768 cache keys hexact input ans hnone hsafe).1 hu
    · simp only [Finset.prod_range_one, Nat.add_zero]
      let targets : Finset (BitVec 238) :=
        (unchainedSet h768 keys).biUnion (fun k => match (cache k : Option Digest) with | some v => {low238 v} | none => ∅)
      have htargets_le : targets.card ≤ W := by
        have ht : targets.card ≤ (unchainedSet h768 keys).card := by
          calc
            targets.card ≤ ∑ k ∈ unchainedSet h768 keys,
                (match (cache k : Option Digest) with | some v => ({low238 v} : Finset (BitVec 238)) | none => ∅).card :=
              Finset.card_biUnion_le
            _ ≤ ∑ _k ∈ unchainedSet h768 keys, 1 := by
                apply Finset.sum_le_sum; intro k _; cases (cache k : Option Digest) <;> simp
            _ = (unchainedSet h768 keys).card := by simp
        exact ht.trans (Nat.le_add_right _ _)
      have hsub : Finset.univ.filter (fun ans : Digest =>
            CacheBad h768 (cache.cacheQuery input ans) ∨ FreshBad256 h768 cache input ans) ⊆
          Finset.univ.filter (fun ans : Digest => lowWidth 238 ans ∈ targets) ∪
          Finset.univ.filter (FreshBad256 h768 cache input) := by
        intro ans hans
        have hba := (Finset.mem_filter.mp hans).2
        by_cases hsafe : FreshBad256 h768 cache input ans
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsafe⟩)
        · apply Finset.mem_union_left
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hcb : CacheBad h768 (cache.cacheQuery input ans) := hba.resolve_right hsafe
          rcases hcb with h256 | h0 | ⟨l, hl1, hl2, hcl⟩
          · exact (hcol256_safe ans hsafe h256).elim
          · obtain ⟨x, y, vx, vy, hne, hux, huy, hx, hy, hlow⟩ := h0
            by_cases hxi : x = input.cast h768
            · subst hxi
              rw [cache768_cacheQuery_self] at hx; cases hx
              rw [cache768_cacheQuery_of_ne h768 cache input ans (Ne.symm hne)] at hy
              have hy' : cache (y.cast h768.symm) = some vy := hy
              have hyk : y.cast h768.symm ∈ unchainedSet h768 keys :=
                mem_unchainedSet.mpr ⟨(hexact _).mpr (by intro hnone; rw [hnone] at hy'; cases hy'), by simpa using huy⟩
              exact Finset.mem_biUnion.mpr ⟨y.cast h768.symm, hyk, by rw [hy']; exact Finset.mem_singleton.mpr hlow⟩
            · by_cases hyi : y = input.cast h768
              · subst hyi
                rw [cache768_cacheQuery_of_ne h768 cache input ans hxi] at hx
                rw [cache768_cacheQuery_self] at hy; cases hy
                have hx' : cache (x.cast h768.symm) = some vx := hx
                have hxk : x.cast h768.symm ∈ unchainedSet h768 keys :=
                  mem_unchainedSet.mpr ⟨(hexact _).mpr (by intro hnone; rw [hnone] at hx'; cases hx'), by simpa using hux⟩
                exact Finset.mem_biUnion.mpr ⟨x.cast h768.symm, hxk, by rw [hx']; exact Finset.mem_singleton.mpr hlow.symm⟩
              · rw [cache768_cacheQuery_of_ne h768 cache input ans hxi] at hx
                rw [cache768_cacheQuery_of_ne h768 cache input ans hyi] at hy
                exact (noBad (Or.inr (Or.inl ⟨x, y, vx, vy, hne, hux, huy, hx, hy, hlow⟩))).elim
          · obtain ⟨x, y, vx, vy, hne, hvx, hvy, hx, hy, hlow⟩ := hcl
            have hxi : x ≠ input.cast h768 := fun heq =>
              not_isUnchainedBin_of_isStage (validStage_isStage hvx) (heq ▸ hu)
            have hyi : y ≠ input.cast h768 := fun heq =>
              not_isUnchainedBin_of_isStage (validStage_isStage hvy) (heq ▸ hu)
            rw [cache768_cacheQuery_of_ne h768 cache input ans hxi] at hx
            rw [cache768_cacheQuery_of_ne h768 cache input ans hyi] at hy
            have hvx' := (validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l (levelChain l) x hxi).mp hvx
            have hvy' := (validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l (levelChain l) y hyi).mp hvy
            exact (noBad (Or.inr (Or.inr ⟨l, hl1, hl2, x, y, vx, vy, hne, hvx', hvy', hx, hy, hlow⟩))).elim
      have hcard_bad :
          (Finset.univ.filter (fun ans : Digest =>
            CacheBad h768 (cache.cacheQuery input ans) ∨ FreshBad256 h768 cache input ans)).card ≤
          2 ^ 18 * W + (2 * keys.card + 1) := by
        calc
          _ ≤ (Finset.univ.filter (fun ans : Digest => lowWidth 238 ans ∈ targets)).card +
              (Finset.univ.filter (FreshBad256 h768 cache input)).card :=
                (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
          _ ≤ 2 ^ 18 * W + (2 * keys.card + 1) :=
                Nat.add_le_add
                  ((card_lowWidth_preimage 238 (by decide) targets).trans (Nat.mul_le_mul_left _ htargets_le))
                  (card_freshBad256_le h768 cache keys hexact input)
      have hB : 2 ^ 18 * W ≤ 2 ^ 256 := by
        have : 2 ^ 18 * 2 ^ 121 ≤ 2 ^ 256 := by decide
        exact (Nat.mul_le_mul_left _ hW).trans this
      have hsurv : survFactor (W + 4096) ≤ ((2 ^ 256 - 2 ^ 18 * W : Nat) : ENNReal) / 2 ^ 256 := by
        have h1 : survFactor (W + 4096) ≤ survFactor W := survFactor_anti (by omega)
        have h2 : survFactor W = ((2 ^ 256 - 2 ^ 18 * W : Nat) : ENNReal) / 2 ^ 256 := by
          unfold survFactor
          have hmul : 2 ^ 18 * (2 ^ 238 - W) = 2 ^ 256 - 2 ^ 18 * W := by
            rw [Nat.mul_sub_left_distrib, show 2 ^ 18 * 2 ^ 238 = 2 ^ 256 by decide]
          rw [← hmul]
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          rw [show (2 : ENNReal) ^ 256 = 2 ^ 18 * 2 ^ 238 by rw [← pow_add]]
          exact (ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)).symm
        exact h1.trans_eq h2
      exact hsurv.trans (hgood_of_card (2 ^ 18 * W) hB hcard_bad)
  · by_cases hch : ∃ l, 9 ≤ l ∧ l ≤ 16 ∧ ReadyStage (cache768 h768 cache) l (levelChain l) (input.cast h768)
    · obtain ⟨l, hl1, hl2, hready⟩ := hch
      refine ⟨levelChain l, ?_, ?_, ?_⟩
      · obtain ⟨ans0, hsafe0⟩ := exists_safe_ans h768 cache keys hexact input hksmall
        have hweq := (cacheWeight_insert_of_safe h768 cache keys hexact input ans0 hnone hsafe0).2.1 l hl1 hl2 hready
        have hexact' : ∀ k, k ∈ insert input keys ↔ (cache.cacheQuery input ans0) k ≠ none := by
          intro k
          by_cases hki : k = input
          · subst hki
            simp only [Finset.mem_insert_self, true_iff]
            erw [QueryCache.cacheQuery_self]; simp
          · simp only [Finset.mem_insert, hki, false_or]
            erw [QueryCache.cacheQuery_of_ne cache ans0 hki]
            exact hexact k
        have hle := cacheWeight_le_card h768 (cache.cacheQuery input ans0) (insert input keys) hexact'
        rw [hweq] at hle
        exact hle.trans (Finset.card_insert_le _ _)
      · intro ans hsafe
        exact (cacheWeight_insert_of_safe h768 cache keys hexact input ans hnone hsafe).2.1 l hl1 hl2 hready
      · set c := levelChain l
        set w := levelWidth l
        let S := stageSet h768 cache keys l c
        let targets : Finset (BitVec w) :=
          S.biUnion (fun k => match (cache k : Option Digest) with | some v => {lowWidth w v} | none => ∅)
        have htargets_le : targets.card ≤ S.card := by
          calc
            targets.card ≤ ∑ k ∈ S,
                (match (cache k : Option Digest) with | some v => ({lowWidth w v} : Finset (BitVec w)) | none => ∅).card :=
              Finset.card_biUnion_le
            _ ≤ ∑ _k ∈ S, 1 := by
                apply Finset.sum_le_sum; intro k _; cases (cache k : Option Digest) <;> simp
            _ = S.card := by simp
        have hcm : c * S.card ≤ W := by
          have hlmem : l ∈ Finset.Icc 9 16 := Finset.mem_Icc.mpr ⟨hl1, hl2⟩
          have hsingle : c * S.card ≤ ∑ j ∈ Finset.Icc 9 16,
              levelChain j * (stageSet h768 cache keys j (levelChain j)).card :=
            Finset.single_le_sum (f := fun j => levelChain j * (stageSet h768 cache keys j (levelChain j)).card)
              (fun _ _ => Nat.zero_le _) hlmem
          exact hsingle.trans (Nat.le_add_left _ _)
        have hsub : Finset.univ.filter (fun ans : Digest =>
              CacheBad h768 (cache.cacheQuery input ans) ∨ FreshBad256 h768 cache input ans) ⊆
            Finset.univ.filter (fun ans : Digest => lowWidth w ans ∈ targets) ∪
            Finset.univ.filter (FreshBad256 h768 cache input) := by
          intro ans hans
          have hba := (Finset.mem_filter.mp hans).2
          by_cases hsafe : FreshBad256 h768 cache input ans
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsafe⟩)
          · apply Finset.mem_union_left
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            have hcb : CacheBad h768 (cache.cacheQuery input ans) := hba.resolve_right hsafe
            rcases hcb with h256 | h0 | ⟨l', hl1', hl2', hcl⟩
            · exact (hcol256_safe ans hsafe h256).elim
            · obtain ⟨x, y, vx, vy, hne, hux, huy, hx, hy, hlow⟩ := h0
              have hxi : x ≠ input.cast h768 := fun heq => hu (heq ▸ hux)
              have hyi : y ≠ input.cast h768 := fun heq => hu (heq ▸ huy)
              rw [cache768_cacheQuery_of_ne h768 cache input ans hxi] at hx
              rw [cache768_cacheQuery_of_ne h768 cache input ans hyi] at hy
              exact (noBad (Or.inr (Or.inl ⟨x, y, vx, vy, hne, hux, huy, hx, hy, hlow⟩))).elim
            · obtain ⟨x, y, vx, vy, hne, hvx, hvy, hx, hy, hlow⟩ := hcl
              by_cases hxi : x = input.cast h768
              · subst hxi
                have hl_eq : l' = l := (isStage_unique (validStage_isStage hvx) (readyStage_isStage hready)).1
                subst hl_eq
                rw [cache768_cacheQuery_self] at hx; cases hx
                rw [cache768_cacheQuery_of_ne h768 cache input ans (Ne.symm hne)] at hy
                have hvy' := (validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l' c y (Ne.symm hne)).mp hvy
                have hy' : cache (y.cast h768.symm) = some vy := hy
                have hyk : y.cast h768.symm ∈ S :=
                  mem_stageSet.mpr ⟨(hexact _).mpr (by intro hnone; rw [hnone] at hy'; cases hy'), by simpa using hvy'⟩
                exact Finset.mem_biUnion.mpr ⟨y.cast h768.symm, hyk, by rw [hy']; exact Finset.mem_singleton.mpr hlow⟩
              · by_cases hyi : y = input.cast h768
                · subst hyi
                  have hl_eq : l' = l := (isStage_unique (validStage_isStage hvy) (readyStage_isStage hready)).1
                  subst hl_eq
                  rw [cache768_cacheQuery_of_ne h768 cache input ans hxi] at hx
                  rw [cache768_cacheQuery_self] at hy; cases hy
                  have hvx' := (validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l' c x hxi).mp hvx
                  have hx' : cache (x.cast h768.symm) = some vx := hx
                  have hxk : x.cast h768.symm ∈ S :=
                    mem_stageSet.mpr ⟨(hexact _).mpr (by intro hnone; rw [hnone] at hx'; cases hx'), by simpa using hvx'⟩
                  exact Finset.mem_biUnion.mpr ⟨x.cast h768.symm, hxk, by rw [hx']; exact Finset.mem_singleton.mpr hlow.symm⟩
                · rw [cache768_cacheQuery_of_ne h768 cache input ans hxi] at hx
                  rw [cache768_cacheQuery_of_ne h768 cache input ans hyi] at hy
                  have hvx' := (validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l' (levelChain l') x hxi).mp hvx
                  have hvy' := (validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l' (levelChain l') y hyi).mp hvy
                  exact (noBad (Or.inr (Or.inr ⟨l', hl1', hl2', x, y, vx, vy, hne, hvx', hvy', hx, hy, hlow⟩))).elim
        have hcard_bad :
            (Finset.univ.filter (fun ans : Digest =>
              CacheBad h768 (cache.cacheQuery input ans) ∨ FreshBad256 h768 cache input ans)).card ≤
            2 ^ (256 - w) * S.card + (2 * keys.card + 1) := by
          calc
            _ ≤ (Finset.univ.filter (fun ans : Digest => lowWidth w ans ∈ targets)).card +
                (Finset.univ.filter (FreshBad256 h768 cache input)).card :=
                  (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
            _ ≤ 2 ^ (256 - w) * S.card + (2 * keys.card + 1) :=
                  Nat.add_le_add
                    ((card_lowWidth_preimage w (levelWidth_le_256 l) targets).trans
                      (Nat.mul_le_mul_left _ htargets_le))
                    (card_freshBad256_le h768 cache keys hexact input)
        have hB : 2 ^ (256 - w) * S.card ≤ 2 ^ 256 := by
          have hw_lo : 230 ≤ levelWidth l := by interval_cases l <;> decide
          have h1 : 2 ^ (256 - w) ≤ 2 ^ 26 := Nat.pow_le_pow_right (by decide) (by omega)
          have h2 : S.card ≤ 2 ^ 121 := (Nat.le_mul_of_pos_left S.card (by have := levelChain_ge_two hl1 hl2; omega)).trans (hcm.trans hW)
          have h3 : 2 ^ 26 * 2 ^ 121 ≤ 2 ^ 256 := by decide
          exact (Nat.mul_le_mul h1 h2).trans h3
        have hchain_bound := prod_survFactor_le_chain_surv W c w S.card hW
          (by have := levelChain_ge_two hl1 hl2; omega) (levelChain_le_16 hl1 hl2)
          (levelWidth_le_256 l) (levelChain_security l (by omega)) hcm
        exact hchain_bound.trans (hgood_of_card (2 ^ (256 - w) * S.card) hB hcard_bad)
    · push_neg at hch
      refine ⟨0, ?_, ?_, ?_⟩
      · exact (cacheWeight_le_card h768 cache keys hexact).trans (Nat.le_succ _)
      · intro ans hsafe
        exact (cacheWeight_insert_of_safe h768 cache keys hexact input ans hnone hsafe).2.2 hu hch
      · simp only [Finset.prod_range_zero]
        have hsub : Finset.univ.filter (fun ans : Digest =>
              CacheBad h768 (cache.cacheQuery input ans) ∨ FreshBad256 h768 cache input ans) ⊆
            Finset.univ.filter (FreshBad256 h768 cache input) := by
          intro ans hans
          have hba := (Finset.mem_filter.mp hans).2
          by_cases hsafe : FreshBad256 h768 cache input ans
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsafe⟩
          · exfalso
            have hcb : CacheBad h768 (cache.cacheQuery input ans) := hba.resolve_right hsafe
            rcases hcb with h256 | h0 | ⟨l, hl1, hl2, hcl⟩
            · exact hcol256_safe ans hsafe h256
            · obtain ⟨x, y, vx, vy, hne, hux, huy, hx, hy, hlow⟩ := h0
              have hxi : x ≠ input.cast h768 := fun heq => hu (heq ▸ hux)
              have hyi : y ≠ input.cast h768 := fun heq => hu (heq ▸ huy)
              rw [cache768_cacheQuery_of_ne h768 cache input ans hxi] at hx
              rw [cache768_cacheQuery_of_ne h768 cache input ans hyi] at hy
              exact noBad (Or.inr (Or.inl ⟨x, y, vx, vy, hne, hux, huy, hx, hy, hlow⟩))
            · obtain ⟨x, y, vx, vy, hne, hvx, hvy, hx, hy, hlow⟩ := hcl
              have hxi : x ≠ input.cast h768 := fun heq =>
                hch l hl1 hl2 ((validStage_cacheQuery_self h768 cache input ans hnone hsafe l (levelChain l)).mp (heq ▸ hvx))
              have hyi : y ≠ input.cast h768 := fun heq =>
                hch l hl1 hl2 ((validStage_cacheQuery_self h768 cache input ans hnone hsafe l (levelChain l)).mp (heq ▸ hvy))
              rw [cache768_cacheQuery_of_ne h768 cache input ans hxi] at hx
              rw [cache768_cacheQuery_of_ne h768 cache input ans hyi] at hy
              have hvx' := (validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l (levelChain l) x hxi).mp hvx
              have hvy' := (validStage_cacheQuery_of_ne h768 cache input ans hnone hsafe l (levelChain l) y hyi).mp hvy
              exact noBad (Or.inr (Or.inr ⟨l, hl1, hl2, x, y, vx, vy, hne, hvx', hvy', hx, hy, hlow⟩))
        have hcard_bad :
            (Finset.univ.filter (fun ans : Digest =>
              CacheBad h768 (cache.cacheQuery input ans) ∨ FreshBad256 h768 cache input ans)).card ≤
            0 + (2 * keys.card + 1) := by
          rw [Nat.zero_add]
          exact (Finset.card_le_card hsub).trans (card_freshBad256_le h768 cache keys hexact input)
        have h0 := hgood_of_card 0 (Nat.zero_le _) hcard_bad
        have h1 : ((2 ^ 256 - 0 : Nat) : ENNReal) / 2 ^ 256 = 1 := by
          simp only [Nat.sub_zero, Nat.cast_pow, Nat.cast_ofNat]
          exact ENNReal.div_self (by positivity) (by finiteness)
        exact h1.symm.trans_le h0

private theorem prEvent_mul_le_prEvent_bind_add {α β : Type}
    (mx : ProbComp α) (f : α → ProbComp β) (p : α → Prop) (q : β → Prop)
    (F R eps1 eps2 : ENNReal) (hR : R ≤ 1)
    (hF : F ≤ prEvent (p <$> mx) + eps1)
    (hcont : ∀ a ∈ support mx, p a → R ≤ prEvent (q <$> f a) + eps2) :
    F * R ≤ prEvent (q <$> (mx >>= f)) + (eps1 + eps2) := by
  classical
  have h1 : F * R ≤ prEvent (p <$> mx) * R + eps1 := by
    calc
      F * R ≤ (prEvent (p <$> mx) + eps1) * R := mul_le_mul' hF le_rfl
      _ = prEvent (p <$> mx) * R + eps1 * R := add_mul _ _ _
      _ ≤ prEvent (p <$> mx) * R + eps1 := add_le_add le_rfl (mul_le_of_le_one_right zero_le hR)
  have hmap : prEvent (p <$> mx) =
      prEvent ((fun a => p a.1) <$> MonadAttach.attach mx) := by
    conv_lhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
    rw [Functor.map_map]
  have h2 : prEvent (p <$> mx) * R ≤ prEvent (q <$> (mx >>= f)) + eps2 := by
    have heps2 : eps2 = prEvent ((fun _ => True) <$> MonadAttach.attach mx) * eps2 := by
      rw [OracleComp.prEvent_true_eq_one, one_mul]
    rw [bind_eq_attach_bind mx f, hmap, heps2, prEvent_bind_eq_tsum]
    have htsum_p := OracleComp.prEvent_eq_tsum_ite (MonadAttach.attach mx) (fun a => p a.1)
    have htsum_t := OracleComp.prEvent_eq_tsum_ite (MonadAttach.attach mx) (fun _ => True)
    rw [htsum_p, htsum_t, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro a
    by_cases hp : p a.1
    · simp only [hp, ite_true]
      calc
        _ ≤ _ * (prEvent (q <$> f a.1) + eps2) := mul_le_mul' le_rfl (hcont a.1 a.2 hp)
        _ = _ := mul_add _ _ _
    · simp only [hp, ite_false, zero_mul]
      exact zero_le
  calc
    F * R ≤ prEvent (p <$> mx) * R + eps1 := h1
    _ ≤ (prEvent (q <$> (mx >>= f)) + eps2) + eps1 := add_le_add h2 le_rfl
    _ = prEvent (q <$> (mx >>= f)) + (eps1 + eps2) := by
      rw [add_assoc, add_comm eps2 eps1]

/-- Adaptive banked-credit lazy-ROM induction with zero `ENNReal` subtraction. -/
theorem compression_noBad_bound_from_cache (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) {α : Type} (computation : OracleComp World α)
    (budget total : Nat) (bounded : PublicQueryBound computation budget)
    (cache : CompressionCache) (keys : Finset CompressionSpec.Domain)
    (hexact : ∀ k, k ∈ keys ↔ cache k ≠ none)
    (noBad : ¬ CacheBad h768 cache)
    (htot : keys.card + budget ≤ total) (htot_cap : total ≤ 2 ^ 121) :
    (∏ i ∈ Finset.Ico (cacheWeight h768 cache keys) total, survFactor (i + 4096)) ≤
      prEvent ((fun result => ¬ CacheBad h768 result.2) <$> (compressionRun permutation computation cache)) +
      ((budget * (2 * keys.card + budget) : Nat) : ENNReal) / 2 ^ 256 := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget cache keys with
  | pure value =>
    rw [compression_run_pure]
    simp only [prEvent_pure, noBad, not_false_eq_true, ite_true]
    exact (Finset.prod_le_one (fun _ _ => survFactor_le_one _)).trans (le_add_right le_rfl)
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      set R := ∏ i ∈ Finset.Ico (cacheWeight h768 cache keys) total, survFactor (i + 4096)
      set eps := ((budget * (2 * keys.card + budget) : Nat) : ENNReal) / 2 ^ 256
      have hbind : (1 : ENNReal) * R ≤
          prEvent ((fun result => ¬ CacheBad h768 result.2) <$>
            ((liftM (unifSpec.query coins) : ProbComp _) >>= fun answer =>
              compressionRun permutation (next answer) cache)) + (0 + eps) :=
        prEvent_mul_le_prEvent_bind_add
          (liftM (unifSpec.query coins) : ProbComp _)
          (fun answer => compressionRun permutation (next answer) cache)
          (fun _ => True) (fun result => ¬ CacheBad h768 result.2)
          1 R 0 eps
          (Finset.prod_le_one (fun _ _ => survFactor_le_one _))
          (by rw [OracleComp.prEvent_true_eq_one, add_zero])
          (fun answer _ _ => ih answer budget
            (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
            cache keys hexact noBad htot)
      simpa only [one_mul, zero_add] using hbind
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      have hstep_eps_le : ((budget - 1) * (2 * keys.card + (budget - 1))) ≤
          budget * (2 * keys.card + budget) :=
        Nat.mul_le_mul (Nat.sub_le budget 1) (Nat.add_le_add_left (Nat.sub_le budget 1) _)
      have hsame : ∀ answer,
          (∏ i ∈ Finset.Ico (cacheWeight h768 cache keys) total, survFactor (i + 4096)) ≤
            prEvent ((fun result => ¬ CacheBad h768 result.2) <$>
              (compressionRun permutation (next answer) cache)) +
            ((budget * (2 * keys.card + budget) : Nat) : ENNReal) / 2 ^ 256 := fun answer =>
        (ih answer (budget - 1) (tails answer) cache keys hexact noBad (by omega)).trans
          (add_le_add le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr hstep_eps_le) _))
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer => exact hsame answer
        | none =>
          have hW_le_cap : cacheWeight h768 cache keys ≤ 2 ^ 121 :=
            (cacheWeight_le_card h768 cache keys hexact).trans (by omega)
          have hksmall : 2 * keys.card + 1 < 2 ^ 256 := by
            have : 2 * 2 ^ 121 + 1 < 2 ^ 256 := by decide
            omega
          obtain ⟨stepCost, hWstep_le, hWstep_eq, hfresh⟩ :=
            fresh_step_bound h768 cache keys hexact noBad input cached hW_le_cap hksmall
          set W := cacheWeight h768 cache keys
          have hWstep_tot : W + stepCost ≤ total := hWstep_le.trans (by omega)
          have hnotmem : input ∉ keys := fun h => (hexact input).mp h cached
          have hcard_ins : (insert input keys).card = keys.card + 1 := Finset.card_insert_of_notMem hnotmem
          have hleft_eq :
              (∏ i ∈ Finset.Ico W (W + stepCost), survFactor (i + 4096)) =
              (∏ j ∈ Finset.range stepCost, survFactor (W + j + 4096)) := by
            have h1 : ∏ i ∈ Finset.Ico W (W + stepCost), survFactor (i + 4096) =
                ∏ i ∈ Finset.Ico (0 + W) (stepCost + W), survFactor (i + 4096) := by
              rw [Nat.zero_add, Nat.add_comm]
            rw [h1, ← Finset.prod_Ico_add (fun i => survFactor (i + 4096)) 0 stepCost W, Nat.Ico_zero_eq_range]
          have hprod_split :
              (∏ i ∈ Finset.Ico W total, survFactor (i + 4096)) =
                (∏ j ∈ Finset.range stepCost, survFactor (W + j + 4096)) *
                (∏ i ∈ Finset.Ico (W + stepCost) total, survFactor (i + 4096)) := by
            rw [← Finset.prod_Ico_consecutive (fun i => survFactor (i + 4096)) (Nat.le_add_right W stepCost) hWstep_tot,
              hleft_eq]
          set F := ∏ j ∈ Finset.range stepCost, survFactor (W + j + 4096)
          set R := ∏ i ∈ Finset.Ico (W + stepCost) total, survFactor (i + 4096)
          set eps1 := ((2 * keys.card + 1 : Nat) : ENNReal) / 2 ^ 256
          set eps2 := (((budget - 1) * (2 * (keys.card + 1) + (budget - 1)) : Nat) : ENNReal) / 2 ^ 256
          have hcont : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              (¬ CacheBad h768 (cache.cacheQuery input answer) ∧ ¬ FreshBad256 h768 cache input answer) →
              R ≤ prEvent ((fun result => ¬ CacheBad h768 result.2) <$>
                  (compressionRun permutation (next answer) (cache.cacheQuery input answer))) + eps2 := by
            intro answer _ ⟨hnb', hsafe⟩
            have hexact' : ∀ k, k ∈ insert input keys ↔ (cache.cacheQuery input answer) k ≠ none := by
              intro k
              by_cases hki : k = input
              · subst hki
                simp only [Finset.mem_insert_self, true_iff]
                erw [QueryCache.cacheQuery_self]; simp
              · simp only [Finset.mem_insert, hki, false_or]
                erw [QueryCache.cacheQuery_of_ne cache answer hki]
                exact hexact k
            have hih := ih answer (budget - 1) (tails answer)
              (cache.cacheQuery input answer) (insert input keys) hexact' hnb' (by rw [hcard_ins]; omega)
            rw [hWstep_eq answer hsafe, hcard_ins] at hih
            exact hih
          have heps_nat : (2 * keys.card + 1) + (budget - 1) * (2 * (keys.card + 1) + (budget - 1)) =
              budget * (2 * keys.card + budget) := by
            obtain ⟨b', rfl⟩ : ∃ b', budget = b' + 1 := ⟨budget - 1, by omega⟩
            simp only [Nat.add_sub_cancel]
            ring
          have heps_eq : eps1 + eps2 = ((budget * (2 * keys.card + budget) : Nat) : ENNReal) / 2 ^ 256 := by
            dsimp only [eps1, eps2]
            rw [← ENNReal.add_div, ← Nat.cast_add, heps_nat]
          rw [hprod_split, ← heps_eq]
          exact prEvent_mul_le_prEvent_bind_add
            ($ᵗ CompressionSpec.Range input)
            (fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
            (fun answer => ¬ CacheBad h768 (cache.cacheQuery input answer) ∧ ¬ FreshBad256 h768 cache input answer)
            (fun result => ¬ CacheBad h768 result.2)
            F R eps1 eps2
            (Finset.prod_le_one (fun _ _ => survFactor_le_one _))
            hfresh hcont
      · rcases permQuery with input | input
        · rw [compression_run_permute]; exact hsame _
        · rw [compression_run_inverse]; exact hsame _

theorem compression_noBad_bound (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) {α : Type} (computation : OracleComp World α)
    (budget : Nat) (bounded : PublicQueryBound computation budget)
    (hcap : budget ≤ 2 ^ 121) :
    (∏ i ∈ Finset.range (budget + 4096), survFactor i) ≤
      prEvent ((fun result => ¬ CacheBad h768 result.2) <$> (compressionRun permutation computation ∅)) +
      ((budget ^ 2 : Nat) : ENNReal) / 2 ^ 256 := by
  have hnoBad : ¬ CacheBad h768 ∅ := by
    rintro (⟨_, _, _, _, _, h, _, _⟩ | ⟨_, _, _, _, _, _, _, h, _, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, h, _, _⟩)
    · simp at h
    · unfold cache768 at h; simp at h
    · unfold cache768 at h; simp at h
  have hW0 : cacheWeight h768 ∅ ∅ = 0 := by
    unfold cacheWeight unchainedSet stageSet; simp
  have hest := compression_noBad_bound_from_cache h768 permutation computation budget budget bounded
    ∅ ∅ (by intro k; simp) hnoBad (by simp) hcap
  rw [hW0, Finset.card_empty, Nat.mul_zero, Nat.zero_add, ← sq] at hest
  have hshift : (∏ i ∈ Finset.range (budget + 4096), survFactor i) ≤
      ∏ i ∈ Finset.Ico 0 budget, survFactor (i + 4096) := by
    rw [← Nat.Ico_zero_eq_range,
      ← Finset.prod_Ico_consecutive survFactor (Nat.zero_le 4096) (Nat.le_add_left 4096 budget)]
    calc
      (∏ i ∈ Finset.Ico 0 4096, survFactor i) * (∏ i ∈ Finset.Ico 4096 (budget + 4096), survFactor i)
        ≤ 1 * (∏ i ∈ Finset.Ico 4096 (budget + 4096), survFactor i) :=
          mul_le_mul' (Finset.prod_le_one (fun _ _ => survFactor_le_one _)) le_rfl
      _ = ∏ i ∈ Finset.Ico 4096 (budget + 4096), survFactor i := one_mul _
      _ = ∏ i ∈ Finset.Ico 0 budget, survFactor (i + 4096) := by
          have h1 : ∏ i ∈ Finset.Ico 4096 (budget + 4096), survFactor i =
              ∏ i ∈ Finset.Ico (0 + 4096) (budget + 4096), survFactor i := by
            rw [Nat.zero_add]
          rw [h1, ← Finset.prod_Ico_add survFactor 0 budget 4096]
          apply Finset.prod_congr rfl; intro i _; rw [Nat.add_comm]
  exact hshift.trans hest

/-! ### 4. Query-Answer Tracing and Direct Checker Binding Reduction -/

abbrev CompressionReplies := List (BitVec COMPRESSION_INPUT_LENGTH × Digest)

def ReplyValidStage (h768 : COMPRESSION_INPUT_LENGTH = 768) (replies : CompressionReplies)
    (l : Nat) : Nat → BitVec 768 → Digest → Prop
  | 0, _, _ => False
  | 1, x, v => isStage l 1 x ∧ (x.cast h768.symm, v) ∈ replies
  | s + 2, x, v =>
      isStage l (s + 2) x ∧ (x.cast h768.symm, v) ∈ replies ∧
      ∃ p, ReplyValidStage h768 replies l (s + 1) p (x.extractLsb' 0 256)

def ReplyBad (h768 : COMPRESSION_INPUT_LENGTH = 768) (replies : CompressionReplies) : Prop :=
  (∃ a ∈ replies, ∃ b ∈ replies, a.1 ≠ b.1 ∧ a.2 = b.2) ∨
  (∃ a ∈ replies, ∃ b ∈ replies, a.1 ≠ b.1 ∧
    isUnchainedBin (a.1.cast h768) ∧ isUnchainedBin (b.1.cast h768) ∧ low238 a.2 = low238 b.2) ∨
  (∃ l, 9 ≤ l ∧ l ≤ 16 ∧ ∃ x y vx vy, x ≠ y ∧
    ReplyValidStage h768 replies l (levelChain l) x vx ∧
    ReplyValidStage h768 replies l (levelChain l) y vy ∧
    lowWidth (levelWidth l) vx = lowWidth (levelWidth l) vy)

private theorem inputValidStage_to_reply (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (c : Comp96) (inputs : List (BitVec 768)) (replies : CompressionReplies)
    (hmem : ∀ z ∈ inputs, (z.cast h768.symm, c z) ∈ replies) (l s : Nat) :
    ∀ x, InputValidStage c inputs l s x → ReplyValidStage h768 replies l s x (c x) := by
  induction s with
  | zero => intro _ h; exact h.elim
  | succ s ih =>
    intro x hx
    cases s with
    | zero => exact ⟨hx.1, hmem x hx.2⟩
    | succ s =>
      obtain ⟨hs, hxin, p, hp, hcp⟩ := hx
      exact ⟨hs, hmem x hxin, p, hcp ▸ ih p hp⟩

private theorem replyValidStage_to_cache (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (replies : CompressionReplies) (cache : CompressionCache)
    (hcache : ∀ p ∈ replies, cache p.1 = some p.2) (l s : Nat) :
    ∀ x v, ReplyValidStage h768 replies l s x v →
      ValidStage (cache768 h768 cache) l s x ∧ cache768 h768 cache x = some v := by
  induction s with
  | zero => intro _ _ h; exact h.elim
  | succ s ih =>
    intro x v hx
    cases s with
    | zero =>
      have hc : cache768 h768 cache x = some v := hcache _ hx.2
      exact ⟨⟨hx.1, by rw [hc]; rfl⟩, hc⟩
    | succ s =>
      obtain ⟨hs, hxin, p, hp⟩ := hx
      have hc : cache768 h768 cache x = some v := hcache _ hxin
      obtain ⟨hvp, hcp⟩ := ih p (x.extractLsb' 0 256) hp
      exact ⟨⟨hs, by rw [hc]; rfl, p, hvp, hcp⟩, hc⟩

def traceCompressionReplies {α : Type} (computation : OracleComp World α) :
    OracleComp World (α × CompressionReplies) :=
  OracleComp.recOn computation
    (fun value => pure (value, []))
    (fun query _ next =>
      match query, next with
      | .inr (.inl input), next => do
          let answer ← (liftM (World.query (.inr (.inl input))) : OracleComp World _)
          let (value, trace) ← next answer
          pure (value, (input, answer) :: trace)
      | q, next => do
          let answer ← (liftM (World.query q) : OracleComp World _)
          next answer)

private theorem public_query_bound_pure {α : Type} (x : α) (n : Nat) :
    PublicQueryBound (pure x : OracleComp World α) n := trivial

private theorem public_query_bound_coins {α : Type} (coins : ProbComp α) :
    PublicQueryBound (liftM coins : OracleComp World α) 0 := by
  induction coins using OracleComp.inductionOn with
  | pure _ => exact public_query_bound_pure _ 0
  | query_bind query _ ih =>
    exact ⟨Nat.zero_le _, fun answer => ih answer⟩

theorem traceReplies_bound {α : Type} (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    PublicQueryBound (traceCompressionReplies computation) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure _ => exact public_query_bound_pure _ _
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩
    · rcases publicQuery with input | permQuery
      · refine ⟨bounded.1, fun answer => ?_⟩
        have htail := ih answer (budget - 1) (bounded.2 answer)
        refine (public_query_bound_bind (second := 0) htail
          (fun p => public_query_bound_pure (p.1, (input, answer) :: p.2) 0)).mono ?_
        change budget - 1 + 0 ≤ budget - 1
        omega
      · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

theorem traceReplies_compressionRun_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (cache : CompressionCache)
    (result : (α × CompressionReplies) × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (traceCompressionReplies computation) cache)) :
    (∀ k v, cache k = some v → result.2 k = some v) ∧
    (∀ pair ∈ result.1.2, result.2 pair.1 = some pair.2) := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    change result ∈ support (compressionRun permutation (pure (value, [])) cache) at reached
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨fun _ _ h => h, by simp⟩
  | query_bind query next ih =>
    rcases query with coins | publicQuery
    · change result ∈ support (compressionRun permutation
        ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun answer =>
          traceCompressionReplies (next answer)) cache) at reached
      rw [compression_run_private] at reached
      obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      exact ih answer cache result reached
    · rcases publicQuery with input | permQuery
      · change result ∈ support (compressionRun permutation
          ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= fun answer =>
            traceCompressionReplies (next answer) >>= fun (value, trace) =>
              pure (value, (input, answer) :: trace)) cache) at reached
        rw [compression_run_compress] at reached
        cases hcached : cache input with
        | some answer =>
          rw [hcached] at reached
          dsimp only at reached
          rw [compression_run_bind] at reached
          obtain ⟨⟨⟨v, tr⟩, c'⟩, hreach, hrest⟩ := (mem_support_bind_iff _ _ _).mp reached
          dsimp only at hrest
          rw [compression_run_pure] at hrest
          erw [support_pure, Set.mem_singleton_iff] at hrest
          subst result
          obtain ⟨hpres, hmem⟩ := ih answer cache ((v, tr), c') hreach
          refine ⟨hpres, ?_⟩
          intro pair hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hpres input answer hcached
          · exact hmem pair hp
        | none =>
          rw [hcached] at reached
          dsimp only at reached
          obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
          rw [compression_run_bind] at reached
          obtain ⟨⟨⟨v, tr⟩, c'⟩, hreach, hrest⟩ := (mem_support_bind_iff _ _ _).mp reached
          dsimp only at hrest
          rw [compression_run_pure] at hrest
          erw [support_pure, Set.mem_singleton_iff] at hrest
          subst result
          obtain ⟨hpres, hmem⟩ := ih answer (cache.cacheQuery input answer) ((v, tr), c') hreach
          refine ⟨?_, ?_⟩
          · intro k v' hkv
            apply hpres
            by_cases hk : k = input
            · subst hk; rw [hcached] at hkv; cases hkv
            · erw [QueryCache.cacheQuery_of_ne cache answer hk]; exact hkv
          · intro pair hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact hpres input answer (QueryCache.cacheQuery_self cache input answer)
            · exact hmem pair hp
      · rcases permQuery with input | input
        · change result ∈ support (compressionRun permutation
            ((liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World _) >>= fun answer =>
              traceCompressionReplies (next answer)) cache) at reached
          rw [compression_run_permute] at reached
          exact ih _ cache result reached
        · change result ∈ support (compressionRun permutation
            ((liftM (World.query (.inr (.inr (.inr input)))) : OracleComp World _) >>= fun answer =>
              traceCompressionReplies (next answer)) cache) at reached
          rw [compression_run_inverse] at reached
          exact ih _ cache result reached

theorem execute_public_query_bound (image : Image) (steps : Nat) (state : MachineState)
    (allowCoins : Bool) :
    PublicQueryBound (execute image steps state allowCoins) steps := by
  induction steps generalizing state with
  | zero => exact public_query_bound_pure _ _
  | succ steps ih =>
    simp only [execute]
    split
    · exact public_query_bound_pure _ _
    · split
      · split
        · exact public_query_bound_pure _ _
        · change Oracle.callCost (.inr _) ≤ steps + 1 ∧ _
          refine ⟨by change 1 ≤ steps + 1; omega, fun answer => ?_⟩
          refine (public_query_bound_bind (second := 0) (ih _)
            (fun _ => public_query_bound_pure _ 0)).mono ?_
          change steps + 0 ≤ steps + 1 - 1
          omega
      · split
        · exact public_query_bound_pure _ _
        · split
          · have hcoins := public_query_bound_coins ($ᵗ BitVec (8 * (state.getReg .x11).toNat))
            refine (public_query_bound_bind (first := 0) (second := steps + 1) hcoins (fun answer =>
              (public_query_bound_bind (second := 0)
                (ih (writeBits state (state.getReg .x10) answer))
                (fun _ => public_query_bound_pure _ 0)).mono (by omega))).mono (by omega)
          · exact public_query_bound_pure _ _
    · split
      · exact public_query_bound_pure _ _
      · refine (public_query_bound_bind (second := 0) (ih _)
          (fun _ => public_query_bound_pure _ 0)).mono (by omega)

theorem run_check_public_query_bound (input : CheckInput) :
    PublicQueryBound (submission.run .check input) (submission.steps .check) := by
  unfold Submission.run
  dsimp only
  split
  · exact execute_public_query_bound _ _ _ _
  · trivial

/-- Soundness contract satisfied by our submitted deterministic `check` image (proved in `MoonCheckRef`). -/
def CheckSound (h768 : COMPRESSION_INPUT_LENGTH = 768) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true →
    ∃ exec trace,
      fixedOracleRun oracle (traceCompressionReplies (submission.run .check input)) = pure (exec, trace) ∧
      ∀ (i : Index) (hi : i ∈ input.positions),
        ∃ w : WitnessPath,
          w.index = i ∧
          w.value = input.values ⟨i, hi⟩ ∧
          w.evalRoot (fun x => oracle.compression (x.cast h768.symm)) = input.commitment ∧
          ∀ x ∈ w.pathInputs (fun x => oracle.compression (x.cast h768.symm)),
            (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ trace

def boundedCollisionSearch (adversary : Scheme.Adversary) (budget : Nat) :
    OracleComp World CompressionReplies := do
  let res ← limitPublicQueries adversary budget
  match res with
  | none => pure []
  | some claim => do
      let (_, t0) ← traceCompressionReplies
        (submission.run .check ⟨claim.root, claim.positions₀, claim.values₀, claim.proof₀⟩)
      let (_, t1) ← traceCompressionReplies
        (submission.run .check ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩)
      pure (t0 ++ t1)

theorem boundedCollisionSearch_bound (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (boundedCollisionSearch adversary budget) (budget + 2 ^ 39) := by
  unfold boundedCollisionSearch
  apply public_query_bound_bind (limit_public_bound adversary budget)
  intro res
  cases res with
  | none => trivial
  | some claim =>
    have hstep : submission.steps .check + submission.steps .check = 2 ^ 39 := by
      change 274877906944 + 274877906944 = 2 ^ 39; decide
    rw [← hstep]
    apply public_query_bound_bind (traceReplies_bound _ _ (run_check_public_query_bound _))
    intro _
    have h2 := traceReplies_bound _ _ (run_check_public_query_bound
      ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩)
    simpa only [Nat.add_zero] using public_query_bound_bind (second := 0) h2 (fun _ => public_query_bound_pure _ 0)

theorem search_replyBad_in_cache (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (adversary : Scheme.Adversary) (budget : Nat)
    (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (boundedCollisionSearch adversary budget) ∅))
    (hbad : ReplyBad h768 result.1) :
    CacheBad h768 result.2 := by
  unfold boundedCollisionSearch at reached
  rw [compression_run_bind] at reached
  obtain ⟨⟨res, c1⟩, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
  dsimp only at reached
  cases res with
  | none =>
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    rcases hbad with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, _, _, _, _, _, hv, _, _⟩
    · simp at h
    · simp at h
    · have : False := by
        cases hc : levelChain _ with
        | zero => rw [hc] at hv; exact hv
        | succ k =>
          cases k with
          | zero => rw [hc] at hv; simp [ReplyValidStage] at hv
          | succ k => rw [hc] at hv; simp [ReplyValidStage] at hv
      exact this.elim
  | some claim =>
    rw [compression_run_bind] at reached
    obtain ⟨⟨⟨_, t0⟩, c2⟩, hreach0, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
    dsimp only at reached
    rw [compression_run_bind] at reached
    obtain ⟨⟨⟨_, t1⟩, c3⟩, hreach1, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
    dsimp only at reached
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    have h0 := (traceReplies_compressionRun_cache permutation _ c1 _ hreach0).2
    obtain ⟨hpres1, h1⟩ := traceReplies_compressionRun_cache permutation _ c2 _ hreach1
    have hboth : ∀ p ∈ t0 ++ t1, c3 p.1 = some p.2 := by
      intro p hp
      rcases List.mem_append.mp hp with hp0 | hp1
      · exact hpres1 p.1 p.2 (h0 p hp0)
      · exact h1 p hp1
    rcases hbad with ⟨a, ha, b, hb, hne, hv⟩ | ⟨a, ha, b, hb, hne, hua, hub, hlow⟩ |
        ⟨l, hl1, hl2, x, y, vx, vy, hne, hvx, hvy, hlow⟩
    · exact Or.inl ⟨a.1, b.1, a.2, b.2, hne, hboth a ha, hboth b hb, hv⟩
    · right; left
      refine ⟨a.1.cast h768, b.1.cast h768, a.2, b.2,
        fun h => hne (by simpa using congrArg (BitVec.cast h768.symm) h), hua, hub, ?_, ?_, hlow⟩
      · change c3 ((a.1.cast h768).cast h768.symm) = some a.2
        rw [BitVec.cast_cast, BitVec.cast_eq]
        exact hboth a ha
      · change c3 ((b.1.cast h768).cast h768.symm) = some b.2
        rw [BitVec.cast_cast, BitVec.cast_eq]
        exact hboth b hb
    · right; right
      obtain ⟨hvx', hcx⟩ := replyValidStage_to_cache h768 (t0 ++ t1) c3 hboth l (levelChain l) x vx hvx
      obtain ⟨hvy', hcy⟩ := replyValidStage_to_cache h768 (t0 ++ t1) c3 hboth l (levelChain l) y vy hvy
      exact ⟨l, hl1, hl2, x, y, vx, vy, hne, hvx', hvy', hcx, hcy, hlow⟩

/-! ### 5. Elementary 5-Block Weierstrass Survival-Product Arithmetic (`238` bits + `256`-bit tail) -/

private theorem one_le_prod_add_sum {ι : Type*} (s : Finset ι) (f g : ι → ENNReal)
    (hf : ∀ i ∈ s, f i ≤ 1) (hfg : ∀ i ∈ s, 1 ≤ f i + g i) :
    (1 : ENNReal) ≤ (∏ i ∈ s, f i) + (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : f a ≤ 1 := hf a (Finset.mem_insert_self a s)
    have h1a : 1 ≤ f a + g a := hfg a (Finset.mem_insert_self a s)
    have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
                   (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    calc
      (1 : ENNReal) ≤ f a + g a := h1a
      _ = f a * 1 + g a := by rw [mul_one]
      _ ≤ f a * ((∏ i ∈ s, f i) + (∑ i ∈ s, g i)) + g a :=
        add_le_add (mul_le_mul' le_rfl hih) le_rfl
      _ = f a * (∏ i ∈ s, f i) + f a * (∑ i ∈ s, g i) + g a := by rw [mul_add, add_assoc]
      _ ≤ f a * (∏ i ∈ s, f i) + 1 * (∑ i ∈ s, g i) + g a :=
        add_le_add (add_le_add le_rfl (mul_le_mul' hfa le_rfl)) le_rfl
      _ = f a * (∏ i ∈ s, f i) + (g a + ∑ i ∈ s, g i) := by
        rw [one_mul]; ac_rfl

private theorem two_mul_sum_Ico_le (a b : Nat) (hab : a ≤ b) :
    2 * (∑ i ∈ Finset.Ico a b, i) + a ^ 2 ≤ b ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show a + (d + 1) = (a + d) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
    nlinarith

private theorem block_prod_lower (a b c v : Nat) (hab : a ≤ b) (hb : b ≤ 2 ^ 238)
    (hcv : c * v ^ 2 ≤ 2 ^ 20) (hbound : b ^ 2 ≤ a ^ 2 + c * v ^ 2 * 2 ^ 219) :
    (((2 ^ 20 - c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) ≤
      ∏ i ∈ Finset.Ico a b, survFactor i := by
  have hweier := one_le_prod_add_sum (Finset.Ico a b) survFactor (fun i => (i : ENNReal) / 2 ^ 238)
    (fun i _ => survFactor_le_one i)
    (fun i hi => one_le_survFactor_add i (by have := (Finset.mem_Ico.mp hi).2; exact (Nat.le_of_lt this).trans hb))
  have hsum_nat : 2 * (∑ i ∈ Finset.Ico a b, i) ≤ c * v ^ 2 * 2 ^ 219 := by
    have h2 := two_mul_sum_Ico_le a b hab
    exact Nat.le_of_add_le_add_right (h2.trans (by rw [add_comm]; exact hbound))
  have hsum : (∑ i ∈ Finset.Ico a b, (i : ENNReal) / 2 ^ 238) ≤ ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, ← div_eq_mul_inv]
    have hcast : ((2 * (∑ i ∈ Finset.Ico a b, i) : Nat) : ENNReal) ≤ ((c * v ^ 2 * 2 ^ 219 : Nat) : ENNReal) :=
      Nat.cast_le.mpr hsum_nat
    calc
      ((∑ i ∈ Finset.Ico a b, i : Nat) : ENNReal) / 2 ^ 238
        = ((2 : ENNReal) * ((∑ i ∈ Finset.Ico a b, i : Nat) : ENNReal)) / (2 * 2 ^ 238) :=
          (ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)).symm
      _ ≤ ((c * v ^ 2 * 2 ^ 219 : Nat) : ENNReal) / (2 * 2 ^ 238) := by
          apply ENNReal.div_le_div_right
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcast
      _ = ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 := by
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          rw [show (2 : ENNReal) * 2 ^ 238 = 2 ^ 20 * 2 ^ 219 by rw [← pow_succ', ← pow_add]]
          exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)
  have h1 : (((2 ^ 20 - c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) + ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 = 1 := by
    rw [← ENNReal.add_div, ← Nat.cast_add, Nat.sub_add_cancel hcv, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_self (by positivity) (by finiteness)
  have hcomb : (((2 ^ 20 - c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) + ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 ≤
      (∏ i ∈ Finset.Ico a b, survFactor i) + ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 :=
    h1.le.trans (hweier.trans (add_le_add le_rfl hsum))
  exact (ENNReal.add_le_add_iff_right (by finiteness)).mp hcomb

private theorem prod_range_split5 (f : Nat → ENNReal) (m1 m2 m3 m4 M : Nat)
    (h1 : m1 ≤ m2) (h2 : m2 ≤ m3) (h3 : m3 ≤ m4) (h4 : m4 ≤ M) :
    ∏ i ∈ Finset.range M, f i =
      (∏ i ∈ Finset.Ico 0 m1, f i) *
      (∏ i ∈ Finset.Ico m1 m2, f i) *
      (∏ i ∈ Finset.Ico m2 m3, f i) *
      (∏ i ∈ Finset.Ico m3 m4, f i) *
      (∏ i ∈ Finset.Ico m4 M, f i) := by
  symm
  rw [Finset.prod_Ico_consecutive f (Nat.zero_le m1) h1,
      Finset.prod_Ico_consecutive f (Nat.zero_le m2) h2,
      Finset.prod_Ico_consecutive f (Nat.zero_le m3) h3,
      Finset.prod_Ico_consecutive f (Nat.zero_le m4) h4,
      Nat.Ico_zero_eq_range]

private def survivalGrid : List (Nat × Nat) :=
  [(16, 23), (23, 29), (29, 33), (33, 36), (36, 39), (39, 41), (41, 43), (43, 44),
   (44, 45), (45, 46), (46, 47), (47, 48), (48, 49), (49, 50), (50, 51), (51, 52),
   (52, 53), (53, 54), (54, 55), (55, 57), (57, 59), (59, 63), (63, 64)]

private def gridCellOk (p : Nat × Nat) : Bool :=
  let u := p.1
  let v := p.2
  decide (16 ≤ u ∧ u < v ∧ v ≤ 64 ∧
    (64 - u) * 2 ^ 94 + 2 ^ 85 ≤
      (2 ^ 20 - 129 * v ^ 2) * (2 ^ 20 - 73 * v ^ 2) *
      (2 ^ 20 - 89 * v ^ 2) * (2 ^ 20 - 105 * v ^ 2) *
      (2 ^ 20 - 121 * v ^ 2))

private theorem survivalGrid_ok : survivalGrid.all gridCellOk = true := by decide

private theorem survivalGrid_covers :
    (List.range 48).all (fun i =>
      let k := i + 16
      survivalGrid.any (fun p => decide (p.1 ≤ k ∧ k + 1 ≤ p.2))) = true := by decide

private theorem five_block_nat_bound (M v coeff c : Nat)
    (hvlo : 17 ≤ v) (hvhi : v ≤ 64) (hM : M ≤ v * 2 ^ 114 + 2 ^ 40)
    (hcoeff : coeff ≤ 16) (hc : c = 8 * coeff + 1) :
    coeff * M ^ 2 + 98 * M + 49 ≤ 64 * c * (v ^ 2 * 2 ^ 219) := by
  have hM2 : M ^ 2 ≤ (v * 2 ^ 114 + 2 ^ 40) ^ 2 := Nat.pow_le_pow_left hM 2
  have hexp : (v * 2 ^ 114 + 2 ^ 40) ^ 2 =
      v ^ 2 * 2 ^ 228 + 2 * v * 2 ^ 154 + 2 ^ 80 := by ring
  have hmain : coeff * (v ^ 2 * 2 ^ 228) = 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) := by ring
  have hconst : 16 * (2 * 64 * 2 ^ 154 + 2 ^ 80) + 98 * (64 * 2 ^ 114 + 2 ^ 40) + 49 ≤
      64 * 17 ^ 2 * 2 ^ 219 := by decide
  have hv2 : 17 ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left hvlo 2
  have herr1 : coeff * (2 * v * 2 ^ 154 + 2 ^ 80) ≤ 16 * (2 * 64 * 2 ^ 154 + 2 ^ 80) :=
    Nat.mul_le_mul hcoeff (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hvhi)) _)
  have herr2 : 98 * M ≤ 98 * (64 * 2 ^ 114 + 2 ^ 40) :=
    Nat.mul_le_mul_left 98 (hM.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hvhi) _))
  have hrhs_err : 64 * 17 ^ 2 * 2 ^ 219 ≤ 64 * (v ^ 2 * 2 ^ 219) := by
    rw [show 64 * 17 ^ 2 * 2 ^ 219 = 64 * (17 ^ 2 * 2 ^ 219) by ring]
    exact Nat.mul_le_mul_left 64 (Nat.mul_le_mul_right _ hv2)
  have hsplit : 64 * c * (v ^ 2 * 2 ^ 219) =
      64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) + 64 * (v ^ 2 * 2 ^ 219) := by
    rw [hc]; ring
  have hcm : coeff * M ^ 2 ≤ coeff * (v ^ 2 * 2 ^ 228) + coeff * (2 * v * 2 ^ 154 + 2 ^ 80) := by
    calc
      coeff * M ^ 2 ≤ coeff * (v * 2 ^ 114 + 2 ^ 40) ^ 2 := Nat.mul_le_mul_left coeff hM2
      _ = coeff * (v ^ 2 * 2 ^ 228) + coeff * (2 * v * 2 ^ 154 + 2 ^ 80) := by rw [hexp]; ring
  calc
    coeff * M ^ 2 + 98 * M + 49
      ≤ (coeff * (v ^ 2 * 2 ^ 228) + coeff * (2 * v * 2 ^ 154 + 2 ^ 80)) +
        98 * (64 * 2 ^ 114 + 2 ^ 40) + 49 :=
          Nat.add_le_add_right (Nat.add_le_add hcm herr2) 49
    _ = 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) +
        (coeff * (2 * v * 2 ^ 154 + 2 ^ 80) + 98 * (64 * 2 ^ 114 + 2 ^ 40) + 49) := by
          rw [hmain]; ring
    _ ≤ 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) +
        (16 * (2 * 64 * 2 ^ 154 + 2 ^ 80) + 98 * (64 * 2 ^ 114 + 2 ^ 40) + 49) :=
          Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right herr1 _) 49) _
    _ ≤ 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) + 64 * 17 ^ 2 * 2 ^ 219 :=
          Nat.add_le_add_left hconst _
    _ ≤ 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) + 64 * (v ^ 2 * 2 ^ 219) :=
          Nat.add_le_add_left hrhs_err _
    _ = 64 * c * (v ^ 2 * 2 ^ 219) := hsplit.symm

private theorem five_block_sq_step (M R : Nat)
    (hnb0 : 16 * M ^ 2 + 98 * M + 49 ≤ 64 * 129 * R)
    (hnb1 : 9 * M ^ 2 + 98 * M + 49 ≤ 64 * 73 * R)
    (hnb2 : 11 * M ^ 2 + 98 * M + 49 ≤ 64 * 89 * R)
    (hnb3 : 13 * M ^ 2 + 98 * M + 49 ≤ 64 * 105 * R)
    (hnb4 : 15 * M ^ 2 + 98 * M + 49 ≤ 64 * 121 * R) :
    let m1 := M / 2
    let m2 := 5 * M / 8
    let m3 := 3 * M / 4
    let m4 := 7 * M / 8
    m1 ≤ m2 ∧ m2 ≤ m3 ∧ m3 ≤ m4 ∧ m4 ≤ M ∧
    m1 ^ 2 ≤ 0 ^ 2 + 129 * R ∧
    m2 ^ 2 ≤ m1 ^ 2 + 73 * R ∧
    m3 ^ 2 ≤ m2 ^ 2 + 89 * R ∧
    m4 ^ 2 ≤ m3 ^ 2 + 105 * R ∧
    M ^ 2 ≤ m4 ^ 2 + 121 * R := by
  dsimp only
  set m1 := M / 2 with hm1_def
  set m2 := 5 * M / 8 with hm2_def
  set m3 := 3 * M / 4 with hm3_def
  set m4 := 7 * M / 8 with hm4_def
  have hm1_le : 2 * m1 ≤ M := Nat.mul_div_le M 2
  have hm1_ge : M ≤ 2 * m1 + 1 := by
    have hlt := Nat.lt_div_mul_add (a := M) (b := 2) (by decide)
    rw [← hm1_def] at hlt; linarith
  have hm2_le : 8 * m2 ≤ 5 * M := Nat.mul_div_le (5 * M) 8
  have hm2_ge : 5 * M ≤ 8 * m2 + 7 := by
    have hlt := Nat.lt_div_mul_add (a := 5 * M) (b := 8) (by decide)
    rw [← hm2_def] at hlt; linarith
  have hm3_le : 4 * m3 ≤ 3 * M := Nat.mul_div_le (3 * M) 4
  have hm3_ge : 3 * M ≤ 4 * m3 + 3 := by
    have hlt := Nat.lt_div_mul_add (a := 3 * M) (b := 4) (by decide)
    rw [← hm3_def] at hlt; linarith
  have hm4_le : 8 * m4 ≤ 7 * M := Nat.mul_div_le (7 * M) 8
  have hm4_ge : 7 * M ≤ 8 * m4 + 7 := by
    have hlt := Nat.lt_div_mul_add (a := 7 * M) (b := 8) (by decide)
    rw [← hm4_def] at hlt; linarith
  have hm12 : m1 ≤ m2 := by rw [hm1_def, hm2_def]; omega
  have hm23 : m2 ≤ m3 := by rw [hm2_def, hm3_def]; omega
  have hm34 : m3 ≤ m4 := by rw [hm3_def, hm4_def]; omega
  have hm4M : m4 ≤ M := by rw [hm4_def]; omega
  have div64 : ∀ a b : Nat, 64 * a ≤ 64 * b → a ≤ b := fun a b h =>
    Nat.le_of_mul_le_mul_left h (by decide)
  refine ⟨hm12, hm23, hm34, hm4M, ?_, ?_, ?_, ?_, ?_⟩
  · apply div64
    have h1 : 64 * m1 ^ 2 ≤ 16 * M ^ 2 := by nlinarith only [hm1_le]
    have h2 : 16 * M ^ 2 ≤ 64 * (0 ^ 2 + 129 * R) := by linarith only [hnb0]
    exact h1.trans h2
  · apply div64
    have h1 : 64 * m2 ^ 2 ≤ 25 * M ^ 2 := by nlinarith only [hm2_le]
    have h2 : 16 * M ^ 2 ≤ 64 * m1 ^ 2 + 32 * M + 16 := by nlinarith only [hm1_le, hm1_ge]
    have h3 : 25 * M ^ 2 ≤ 64 * m1 ^ 2 + (9 * M ^ 2 + 98 * M + 49) := by linarith only [h2]
    have h4 : 64 * m1 ^ 2 + (9 * M ^ 2 + 98 * M + 49) ≤ 64 * (m1 ^ 2 + 73 * R) := by linarith only [hnb1]
    exact h1.trans (h3.trans h4)
  · apply div64
    have h1 : 64 * m3 ^ 2 ≤ 36 * M ^ 2 := by nlinarith only [hm3_le]
    have h2 : 25 * M ^ 2 ≤ 64 * m2 ^ 2 + 70 * M + 49 := by nlinarith only [hm2_le, hm2_ge]
    have h3 : 36 * M ^ 2 ≤ 64 * m2 ^ 2 + (11 * M ^ 2 + 98 * M + 49) := by linarith only [h2]
    have h4 : 64 * m2 ^ 2 + (11 * M ^ 2 + 98 * M + 49) ≤ 64 * (m2 ^ 2 + 89 * R) := by linarith only [hnb2]
    exact h1.trans (h3.trans h4)
  · apply div64
    have h1 : 64 * m4 ^ 2 ≤ 49 * M ^ 2 := by nlinarith only [hm4_le]
    have h2 : 36 * M ^ 2 ≤ 64 * m3 ^ 2 + 72 * M + 36 := by nlinarith only [hm3_le, hm3_ge]
    have h3 : 49 * M ^ 2 ≤ 64 * m3 ^ 2 + (13 * M ^ 2 + 98 * M + 49) := by linarith only [h2]
    have h4 : 64 * m3 ^ 2 + (13 * M ^ 2 + 98 * M + 49) ≤ 64 * (m3 ^ 2 + 105 * R) := by linarith only [hnb3]
    exact h1.trans (h3.trans h4)
  · apply div64
    have h2 : 49 * M ^ 2 ≤ 64 * m4 ^ 2 + 98 * M + 49 := by nlinarith only [hm4_le, hm4_ge]
    have h3 : 64 * M ^ 2 ≤ 64 * m4 ^ 2 + (15 * M ^ 2 + 98 * M + 49) := by linarith only [h2]
    have h4 : 64 * m4 ^ 2 + (15 * M ^ 2 + 98 * M + 49) ≤ 64 * (m4 ^ 2 + 121 * R) := by linarith only [hnb4]
    exact h3.trans h4

theorem one_add_tail_le_budget_add_prod_survFactor (budget : Nat)
    (hpos : 1 ≤ budget) (hsmall : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (1 : ENNReal) + (((budget + 2 ^ 39) ^ 2 : Nat) : ENNReal) / 2 ^ 256 ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS +
      ∏ i ∈ Finset.range (budget + 2 ^ 39 + 4096), survFactor i := by
  change budget ≤ 2 ^ 120 at hsmall
  change (1 : ENNReal) + (((budget + 2 ^ 39) ^ 2 : Nat) : ENNReal) / 2 ^ 256 ≤
    (budget : ENNReal) / 2 ^ 120 +
    ∏ i ∈ Finset.range (budget + 2 ^ 39 + 4096), survFactor i
  set M := budget + 2 ^ 39
  set M' := budget + 2 ^ 39 + 4096
  have hM_le_M' : M ≤ M' := Nat.le_add_right _ _
  have hM'_le_q40 : M' ≤ budget + 2 ^ 40 := by
    have : 2 ^ 39 + 4096 ≤ 2 ^ 40 := by decide
    omega
  have hM'_lt : M' ≤ 2 ^ 238 :=
    (hM'_le_q40.trans (Nat.add_le_add_right hsmall (2 ^ 40))).trans (by decide)
  by_cases hmid : budget ≤ 2 ^ 118
  · have hweier := one_le_prod_add_sum (Finset.range M') survFactor (fun i => (i : ENNReal) / 2 ^ 238)
      (fun i _ => survFactor_le_one i)
      (fun i hi => one_le_survFactor_add i ((Nat.le_of_lt (Finset.mem_range.mp hi)).trans hM'_lt))
    have hsum_nat : M ^ 2 + 2 ^ 18 * (∑ i ∈ Finset.range M', i) ≤ budget * 2 ^ 136 := by
      have h2 : 2 * (∑ i ∈ Finset.range M', i) ≤ M' ^ 2 := by
        simpa [Nat.Ico_zero_eq_range] using two_mul_sum_Ico_le 0 M' (Nat.zero_le M')
      have hMsq : M ^ 2 ≤ M' ^ 2 := Nat.pow_le_pow_left hM_le_M' 2
      have hcomb : M ^ 2 + 2 ^ 18 * (∑ i ∈ Finset.range M', i) ≤ (2 ^ 17 + 1) * M' ^ 2 := by
        have h18 : 2 ^ 18 * (∑ i ∈ Finset.range M', i) = 2 ^ 17 * (2 * (∑ i ∈ Finset.range M', i)) := by ring
        have hmul := Nat.mul_le_mul_left (2 ^ 17) h2
        rw [← h18] at hmul
        calc
          M ^ 2 + 2 ^ 18 * (∑ i ∈ Finset.range M', i)
            ≤ M' ^ 2 + 2 ^ 17 * M' ^ 2 := Nat.add_le_add hMsq hmul
          _ = (2 ^ 17 + 1) * M' ^ 2 := by ring
      have hM'sq : M' ^ 2 ≤ budget * (2 ^ 118 + 2 * 2 ^ 40 + 2 ^ 80) := by
        have h1 : M' ^ 2 ≤ (budget + 2 ^ 40) ^ 2 := Nat.pow_le_pow_left hM'_le_q40 2
        have h2' : (budget + 2 ^ 40) ^ 2 = budget * budget + 2 * 2 ^ 40 * budget + 2 ^ 80 := by ring
        have hq2 : budget * budget ≤ budget * 2 ^ 118 := Nat.mul_le_mul_left budget hmid
        have h80 : 2 ^ 80 ≤ budget * 2 ^ 80 := Nat.le_mul_of_pos_left _ hpos
        calc
          M' ^ 2 ≤ budget * budget + 2 * 2 ^ 40 * budget + 2 ^ 80 := h2' ▸ h1
          _ ≤ budget * 2 ^ 118 + budget * (2 * 2 ^ 40) + budget * 2 ^ 80 :=
            Nat.add_le_add (Nat.add_le_add hq2 (by rw [mul_comm])) h80
          _ = budget * (2 ^ 118 + 2 * 2 ^ 40 + 2 ^ 80) := by ring
      have hconst : (2 ^ 17 + 1) * (2 ^ 118 + 2 * 2 ^ 40 + 2 ^ 80) ≤ 2 ^ 136 := by decide
      calc
        M ^ 2 + 2 ^ 18 * (∑ i ∈ Finset.range M', i)
          ≤ (2 ^ 17 + 1) * M' ^ 2 := hcomb
        _ ≤ (2 ^ 17 + 1) * (budget * (2 ^ 118 + 2 * 2 ^ 40 + 2 ^ 80)) :=
            Nat.mul_le_mul_left _ hM'sq
        _ = budget * ((2 ^ 17 + 1) * (2 ^ 118 + 2 * 2 ^ 40 + 2 ^ 80)) := by ring
        _ ≤ budget * 2 ^ 136 := Nat.mul_le_mul_left budget hconst
    have hsum : ((M ^ 2 : Nat) : ENNReal) / 2 ^ 256 +
        (∑ i ∈ Finset.range M', (i : ENNReal) / 2 ^ 238) ≤ (budget : ENNReal) / 2 ^ 120 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Nat.cast_sum, ← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv]
      have hrew : ((∑ i ∈ Finset.range M', i : Nat) : ENNReal) / 2 ^ 238 =
          ((2 ^ 18 * (∑ i ∈ Finset.range M', i) : Nat) : ENNReal) / 2 ^ 256 := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (2 : ENNReal) ^ 256 = 2 ^ 18 * 2 ^ 238 by rw [← pow_add]]
        exact (ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)).symm
      rw [hrew, ← ENNReal.add_div, ← Nat.cast_add]
      calc
        ((M ^ 2 + 2 ^ 18 * (∑ i ∈ Finset.range M', i) : Nat) : ENNReal) / 2 ^ 256
          ≤ ((budget * 2 ^ 136 : Nat) : ENNReal) / 2 ^ 256 :=
            ENNReal.div_le_div_right (Nat.cast_le.mpr hsum_nat) _
        _ = (budget : ENNReal) / 2 ^ 120 := by
            simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            rw [show (2 : ENNReal) ^ 256 = 2 ^ 120 * 2 ^ 136 by rw [← pow_add]]
            exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)
    calc
      (1 : ENNReal) + ((M ^ 2 : Nat) : ENNReal) / 2 ^ 256
        ≤ ((∏ i ∈ Finset.range M', survFactor i) + (∑ i ∈ Finset.range M', (i : ENNReal) / 2 ^ 238)) +
          ((M ^ 2 : Nat) : ENNReal) / 2 ^ 256 := add_le_add hweier le_rfl
      _ = (((M ^ 2 : Nat) : ENNReal) / 2 ^ 256 + (∑ i ∈ Finset.range M', (i : ENNReal) / 2 ^ 238)) +
          ∏ i ∈ Finset.range M', survFactor i := by
          rw [add_assoc, add_comm (∑ i ∈ Finset.range M', (i : ENNReal) / 2 ^ 238), add_comm (∏ i ∈ Finset.range M', survFactor i)]
      _ ≤ (budget : ENNReal) / 2 ^ 120 + ∏ i ∈ Finset.range M', survFactor i :=
          add_le_add hsum le_rfl
  · have hqlo : 16 * 2 ^ 114 < budget := by
      rw [show 16 * 2 ^ 114 = 2 ^ 118 by decide]
      exact Nat.lt_of_not_le hmid
    have hqhi : budget ≤ 64 * 2 ^ 114 := by
      rw [show 64 * 2 ^ 114 = 2 ^ 120 by decide]
      exact hsmall
    set k := (budget - 1) / 2 ^ 114 with hk_def
    have hk_lo : 16 ≤ k :=
      (Nat.le_div_iff_mul_le (by decide)).mpr (Nat.le_sub_one_of_lt hqlo)
    have hk_hi : k < 64 :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr ((Nat.sub_lt hpos Nat.one_pos).trans_le hqhi)
    have hi_mem : k - 16 ∈ List.range 48 := List.mem_range.mpr (by omega)
    have hcov := List.all_eq_true.mp survivalGrid_covers (k - 16) hi_mem
    obtain ⟨⟨u, v⟩, hp_mem, hp_cov⟩ := List.any_eq_true.mp hcov
    have hp_cov' : u ≤ k ∧ k + 1 ≤ v := by
      have hk_eq : k - 16 + 16 = k := by omega
      simpa only [hk_eq, decide_eq_true_eq] using hp_cov
    have hp_ok : 16 ≤ u ∧ u < v ∧ v ≤ 64 ∧
        (64 - u) * 2 ^ 94 + 2 ^ 85 ≤
          (2 ^ 20 - 129 * v ^ 2) * (2 ^ 20 - 73 * v ^ 2) *
          (2 ^ 20 - 89 * v ^ 2) * (2 ^ 20 - 105 * v ^ 2) *
          (2 ^ 20 - 121 * v ^ 2) := by
      have h := List.all_eq_true.mp survivalGrid_ok (u, v) hp_mem
      simpa only [gridCellOk, decide_eq_true_eq] using h
    obtain ⟨hu16, huv, hv64, hgrid⟩ := hp_ok
    have hv17 : 17 ≤ v := Nat.succ_le_of_lt (hu16.trans_lt huv)
    have huq : u * 2 ^ 114 ≤ budget := by
      have hk1 : k * 2 ^ 114 ≤ budget - 1 := by
        rw [hk_def]; exact Nat.div_mul_le_self _ _
      have hk2 : u * 2 ^ 114 ≤ k * 2 ^ 114 := Nat.mul_le_mul_right _ hp_cov'.1
      exact (hk2.trans hk1).trans (Nat.sub_le budget 1)
    have hqv : budget ≤ v * 2 ^ 114 := by
      have hk1 : budget - 1 < k * 2 ^ 114 + 2 ^ 114 := by
        rw [hk_def]; exact Nat.lt_div_mul_add (a := budget - 1) (b := 2 ^ 114) (by decide)
      have hk2 : budget ≤ (k + 1) * 2 ^ 114 := by
        rw [Nat.add_mul, one_mul]; exact Nat.le_of_pred_lt hk1
      have hk3 : (k + 1) * 2 ^ 114 ≤ v * 2 ^ 114 := Nat.mul_le_mul_right _ hp_cov'.2
      exact hk2.trans hk3
    have hM'_le : M' ≤ v * 2 ^ 114 + 2 ^ 40 := hM'_le_q40.trans (Nat.add_le_add_right hqv (2 ^ 40))
    obtain ⟨hm12, hm23, hm34, hm4M, hb0', hb1', hb2', hb3', hb4'⟩ :=
      five_block_sq_step M' (v ^ 2 * 2 ^ 219)
        (five_block_nat_bound M' v 16 129 hv17 hv64 hM'_le (by decide) rfl)
        (five_block_nat_bound M' v 9 73 hv17 hv64 hM'_le (by decide) rfl)
        (five_block_nat_bound M' v 11 89 hv17 hv64 hM'_le (by decide) rfl)
        (five_block_nat_bound M' v 13 105 hv17 hv64 hM'_le (by decide) rfl)
        (five_block_nat_bound M' v 15 121 hv17 hv64 hM'_le (by decide) rfl)
    have hb0 : (M' / 2) ^ 2 ≤ 0 ^ 2 + 129 * v ^ 2 * 2 ^ 219 := by simpa only [Nat.mul_assoc] using hb0'
    have hb1 : (5 * M' / 8) ^ 2 ≤ (M' / 2) ^ 2 + 73 * v ^ 2 * 2 ^ 219 := by simpa only [Nat.mul_assoc] using hb1'
    have hb2 : (3 * M' / 4) ^ 2 ≤ (5 * M' / 8) ^ 2 + 89 * v ^ 2 * 2 ^ 219 := by simpa only [Nat.mul_assoc] using hb2'
    have hb3 : (7 * M' / 8) ^ 2 ≤ (3 * M' / 4) ^ 2 + 105 * v ^ 2 * 2 ^ 219 := by simpa only [Nat.mul_assoc] using hb3'
    have hb4 : M' ^ 2 ≤ (7 * M' / 8) ^ 2 + 121 * v ^ 2 * 2 ^ 219 := by simpa only [Nat.mul_assoc] using hb4'
    set m1 := M' / 2; set m2 := 5 * M' / 8; set m3 := 3 * M' / 4; set m4 := 7 * M' / 8
    have hm01 : 0 ≤ m1 := Nat.zero_le _
    have hm4_lt : m4 ≤ 2 ^ 238 := hm4M.trans hM'_lt
    have hm3_lt : m3 ≤ 2 ^ 238 := hm34.trans hm4_lt
    have hm2_lt : m2 ≤ 2 ^ 238 := hm23.trans hm3_lt
    have hm1_lt : m1 ≤ 2 ^ 238 := hm12.trans hm2_lt
    have hvsq : v ^ 2 ≤ 64 ^ 2 := Nat.pow_le_pow_left hv64 2
    have hcv0 : 129 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 129 hvsq).trans (by decide)
    have hcv1 : 73 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 73 hvsq).trans (by decide)
    have hcv2 : 89 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 89 hvsq).trans (by decide)
    have hcv3 : 105 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 105 hvsq).trans (by decide)
    have hcv4 : 121 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 121 hvsq).trans (by decide)
    have hp0 := block_prod_lower 0 m1 129 v hm01 hm1_lt hcv0 hb0
    have hp1 := block_prod_lower m1 m2 73 v hm12 hm2_lt hcv1 hb1
    have hp2 := block_prod_lower m2 m3 89 v hm23 hm3_lt hcv2 hb2
    have hp3 := block_prod_lower m3 m4 105 v hm34 hm4_lt hcv3 hb3
    have hp4 := block_prod_lower m4 M' 121 v hm4M hM'_lt hcv4 hb4
    have hmul5 := mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' hp0 hp1) hp2) hp3) hp4
    rw [← prod_range_split5 survFactor m1 m2 m3 m4 M' hm12 hm23 hm34 hm4M] at hmul5
    have hprod_ge : ((64 - u : Nat) : ENNReal) / 64 + ((2 ^ 85 : Nat) : ENNReal) / 2 ^ 100 ≤
        ∏ i ∈ Finset.range M', survFactor i := by
      have hcast_grid : (((64 - u) * 2 ^ 94 + 2 ^ 85 : Nat) : ENNReal) ≤
          ((((2 ^ 20 - 129 * v ^ 2) * (2 ^ 20 - 73 * v ^ 2) *
             (2 ^ 20 - 89 * v ^ 2) * (2 ^ 20 - 105 * v ^ 2) *
             (2 ^ 20 - 121 * v ^ 2) : Nat)) : ENNReal) :=
        Nat.cast_le.mpr hgrid
      calc
        ((64 - u : Nat) : ENNReal) / 64 + ((2 ^ 85 : Nat) : ENNReal) / 2 ^ 100
          = (((64 - u) * 2 ^ 94 : Nat) : ENNReal) / 2 ^ 100 + ((2 ^ 85 : Nat) : ENNReal) / 2 ^ 100 := by
            congr 1
            simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            rw [show (2 : ENNReal) ^ 100 = 64 * 2 ^ 94 by
              rw [show (64 : ENNReal) = 2 ^ 6 by norm_num, ← pow_add]]
            exact (ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)).symm
        _ = (((64 - u) * 2 ^ 94 + 2 ^ 85 : Nat) : ENNReal) / 2 ^ 100 := by
            rw [← ENNReal.add_div, ← Nat.cast_add]
        _ ≤ ((((2 ^ 20 - 129 * v ^ 2) * (2 ^ 20 - 73 * v ^ 2) *
               (2 ^ 20 - 89 * v ^ 2) * (2 ^ 20 - 105 * v ^ 2) *
               (2 ^ 20 - 121 * v ^ 2) : Nat)) : ENNReal) / 2 ^ 100 :=
            ENNReal.div_le_div_right hcast_grid _
        _ = (((2 ^ 20 - 129 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) *
            (((2 ^ 20 - 73 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) *
            (((2 ^ 20 - 89 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) *
            (((2 ^ 20 - 105 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) *
            (((2 ^ 20 - 121 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) := by
            simp only [Nat.cast_mul, div_eq_mul_inv]
            have hinv : ((2 : ENNReal) ^ 100)⁻¹ = ((2 : ENNReal) ^ 20)⁻¹ ^ 5 := by
              rw [← ENNReal.inv_pow, ← pow_mul]
            rw [hinv]; ring
        _ ≤ ∏ i ∈ Finset.range M', survFactor i := hmul5
    have htail_le : ((M ^ 2 : Nat) : ENNReal) / 2 ^ 256 ≤ ((2 ^ 85 : Nat) : ENNReal) / 2 ^ 100 := by
      have hM2_nat : M ^ 2 ≤ 2 ^ 241 := by
        have h1 : M ≤ 2 ^ 120 + 2 ^ 39 := Nat.add_le_add_right hsmall _
        have h2 : (2 ^ 120 + 2 ^ 39) ^ 2 ≤ 2 ^ 241 := by decide
        exact (Nat.pow_le_pow_left h1 2).trans h2
      calc
        ((M ^ 2 : Nat) : ENNReal) / 2 ^ 256
          ≤ ((2 ^ 241 : Nat) : ENNReal) / 2 ^ 256 := ENNReal.div_le_div_right (Nat.cast_le.mpr hM2_nat) _
        _ = ((2 ^ 85 : Nat) : ENNReal) / 2 ^ 100 := by
            simp only [Nat.cast_pow, Nat.cast_ofNat]
            rw [show (2 : ENNReal) ^ 241 = 2 ^ 85 * 2 ^ 156 by rw [← pow_add],
                show (2 : ENNReal) ^ 256 = 2 ^ 100 * 2 ^ 156 by rw [← pow_add]]
            exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)
    have hu_le : (u : ENNReal) / 64 ≤ (budget : ENNReal) / 2 ^ 120 := by
      calc
        (u : ENNReal) / 64
          = ((u * 2 ^ 114 : Nat) : ENNReal) / 2 ^ 120 := by
            simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            rw [show (2 : ENNReal) ^ 120 = 64 * 2 ^ 114 by
              rw [show (64 : ENNReal) = 2 ^ 6 by norm_num, ← pow_add]]
            exact (ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)).symm
        _ ≤ (budget : ENNReal) / 2 ^ 120 := ENNReal.div_le_div_right (Nat.cast_le.mpr huq) _
    have h1 : (1 : ENNReal) = (u : ENNReal) / 64 + ((64 - u : Nat) : ENNReal) / 64 := by
      rw [← ENNReal.add_div, ← Nat.cast_add, Nat.add_sub_of_le (huv.le.trans hv64), Nat.cast_ofNat]
      exact (ENNReal.div_self (by positivity) (by finiteness)).symm
    calc
      (1 : ENNReal) + ((M ^ 2 : Nat) : ENNReal) / 2 ^ 256
        = (u : ENNReal) / 64 + (((64 - u : Nat) : ENNReal) / 64 + ((M ^ 2 : Nat) : ENNReal) / 2 ^ 256) := by
          rw [h1, add_assoc]
      _ ≤ (u : ENNReal) / 64 + (((64 - u : Nat) : ENNReal) / 64 + ((2 ^ 85 : Nat) : ENNReal) / 2 ^ 100) :=
          add_le_add le_rfl (add_le_add le_rfl htail_le)
      _ ≤ (budget : ENNReal) / 2 ^ 120 + ∏ i ∈ Finset.range M', survFactor i :=
          add_le_add hu_le hprod_ge

/-! ### 6. Master Binding Theorem -/

private theorem binding_fixed_le_search (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (hsound : CheckSound h768) (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((fun result => submission.scheme.Breaks oracle result.1 ∧ result.2 ≤ budget) <$>
      (oracle.run adversary))) ≤
    (prEvent ((ReplyBad h768) <$> (fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) := by
  classical
  rw [← limit_public_probability oracle adversary budget (submission.scheme.Breaks oracle)]
  unfold boundedCollisionSearch
  rw [fixed_oracle_run_bind]
  have hmap : fixedOracleRun oracle (limitPublicQueries adversary budget) =
      Prod.fst <$> oracle.run (limitPublicQueries adversary budget) := rfl
  rw [hmap, bind_map_left, prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨res, calls⟩
  cases res with
  | none =>
    simp [fixed_oracle_run_pure]
  | some claim =>
    by_cases hwin : submission.scheme.Breaks oracle claim
    · simp only [Option.some.injEq, exists_eq_left', hwin, ite_true]
      obtain ⟨⟨i, hi0, hi1, hvalne⟩, hacc0, hacc1⟩ := hwin
      obtain ⟨e0, t0, hrun0, hw0⟩ := hsound oracle
        ⟨claim.root, claim.positions₀, claim.values₀, claim.proof₀⟩ hacc0
      obtain ⟨e1, t1, hrun1, hw1⟩ := hsound oracle
        ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩ hacc1
      obtain ⟨w0, hidx0, hv0, hrt0, htr0⟩ := hw0 i hi0
      obtain ⟨w1, hidx1, hv1, hrt1, htr1⟩ := hw1 i hi1
      let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
      have hcol := collision_of_paths c96 w0 w1
        (hidx0.trans hidx1.symm) (by rw [hv0, hv1]; exact hvalne) (hrt0.trans hrt1.symm)
      have hmem : ∀ z ∈ w0.pathInputs c96 ++ w1.pathInputs c96, (z.cast h768.symm, c96 z) ∈ t0 ++ t1 := by
        intro z hz
        rcases List.mem_append.mp hz with hz0 | hz1
        · exact List.mem_append_left _ (htr0 z hz0)
        · exact List.mem_append_right _ (htr1 z hz1)
      have hrb : ReplyBad h768 (t0 ++ t1) := by
        rcases hcol with ⟨x, hx, y, hy, hxy, heq⟩ | ⟨x, hx, y, hy, hxy, hux, huy, hlow⟩ |
            ⟨l, hl1, hl2, x, y, hxy, hvx, hvy, hlow⟩
        · left
          exact ⟨_, hmem x hx, _, hmem y hy, fun h => hxy (by simpa using congrArg (BitVec.cast h768) h), heq⟩
        · right; left
          exact ⟨_, hmem x hx, _, hmem y hy, fun h => hxy (by simpa using congrArg (BitVec.cast h768) h),
            by simpa using hux, by simpa using huy, hlow⟩
        · right; right
          exact ⟨l, hl1, hl2, x, y, c96 x, c96 y, hxy,
            inputValidStage_to_reply h768 c96 _ _ hmem l (levelChain l) x hvx,
            inputValidStage_to_reply h768 c96 _ _ hmem l (levelChain l) y hvy, hlow⟩
      rw [fixed_oracle_run_bind, hrun0, pure_bind, fixed_oracle_run_bind, hrun1, pure_bind,
        fixed_oracle_run_pure, prEvent_pure, ite_eq_left_iff.mpr (fun hn => (hn hrb).elim), mul_one]
    · simp [hwin]

/-- Master Binding Theorem: `CheckSound` implies the challenge's full adaptive `Binding` guarantee. -/
theorem binding_of_check_sound (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (hsound : CheckSound h768) : submission.scheme.Binding := by
  intro adversary budget hpos
  by_cases hlarge : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · have hone : (1 : ENNReal) ≤ (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness)), one_mul]
      exact_mod_cast hlarge
    exact (prEvent_le_one _).trans hone
  · have hsmall : budget ≤ 2 ^ BINDING_SECURITY_BITS := by omega
    have hred :
        (prEvent ((fun (oracle, claim, calls) => submission.scheme.Breaks oracle claim ∧ calls ≤ budget) <$>
          (Scheme.bindingGame adversary))) ≤
        (prEvent ((ReplyBad h768) <$> (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul' le_rfl
      simpa only [prEvent_map, Function.comp_def] using binding_fixed_le_search h768 hsound oracle adversary budget
    have hperm : ∀ permutation : Perm,
        (prEvent ((ReplyBad h768) <$> (($ᵗ Compression) >>= fun compression =>
          fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget)))) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      intro permutation
      have heq := (EvalDistEq.of_evalDist_eq
        (compression_sampling_empty permutation (boundedCollisionSearch adversary budget))).prEvent_eq
          (ReplyBad h768)
      simp only [prEvent_map] at heq
      rw [← heq]
      let run := compressionRun permutation (boundedCollisionSearch adversary budget) ∅
      have hdet : prEvent ((fun result => ReplyBad h768 result.1) <$> run) ≤
          prEvent ((fun result => CacheBad h768 result.2) <$> run) :=
        prEvent_mono_of_support _ _ _ fun result reached hbad =>
          search_replyBad_in_cache h768 permutation adversary budget result reached hbad
      have hcap : budget + 2 ^ 39 ≤ 2 ^ 121 := by
        have : 2 ^ 120 + 2 ^ 39 ≤ 2 ^ 121 := by decide
        have hb : budget ≤ 2 ^ 120 := hsmall
        omega
      have hsurv : (∏ i ∈ Finset.range (budget + 2 ^ 39 + 4096), survFactor i) ≤
          prEvent ((fun result => ¬ CacheBad h768 result.2) <$> run) +
          (((budget + 2 ^ 39) ^ 2 : Nat) : ENNReal) / 2 ^ 256 :=
        compression_noBad_bound h768 permutation (boundedCollisionSearch adversary budget)
          (budget + 2 ^ 39) (boundedCollisionSearch_bound adversary budget) hcap
      have hpart : prEvent ((fun result => CacheBad h768 result.2) <$> run) +
          prEvent ((fun result => ¬ CacheBad h768 result.2) <$> run) = 1 :=
        (prEvent_add_prEvent_not_eq_prEvent_true run (fun result => CacheBad h768 result.2)).trans
          (OracleComp.prEvent_true_eq_one run)
      have h1 := one_add_tail_le_budget_add_prod_survFactor budget hpos hsmall
      have hfin : (∏ i ∈ Finset.range (budget + 2 ^ 39 + 4096), survFactor i) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (Finset.prod_le_one (fun _ _ => survFactor_le_one _))
      have hcol_le : prEvent ((fun result => CacheBad h768 result.2) <$> run) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
        have hcomb : prEvent ((fun result => CacheBad h768 result.2) <$> run) +
            (∏ i ∈ Finset.range (budget + 2 ^ 39 + 4096), survFactor i) ≤
            (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS +
            (∏ i ∈ Finset.range (budget + 2 ^ 39 + 4096), survFactor i) := by
          calc
            prEvent ((fun result => CacheBad h768 result.2) <$> run) +
                (∏ i ∈ Finset.range (budget + 2 ^ 39 + 4096), survFactor i)
              ≤ prEvent ((fun result => CacheBad h768 result.2) <$> run) +
                (prEvent ((fun result => ¬ CacheBad h768 result.2) <$> run) +
                 (((budget + 2 ^ 39) ^ 2 : Nat) : ENNReal) / 2 ^ 256) := add_le_add le_rfl hsurv
            _ = (prEvent ((fun result => CacheBad h768 result.2) <$> run) +
                 prEvent ((fun result => ¬ CacheBad h768 result.2) <$> run)) +
                (((budget + 2 ^ 39) ^ 2 : Nat) : ENNReal) / 2 ^ 256 := by ac_rfl
            _ = 1 + (((budget + 2 ^ 39) ^ 2 : Nat) : ENNReal) / 2 ^ 256 := by rw [hpart]
            _ ≤ (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS +
                (∏ i ∈ Finset.range (budget + 2 ^ 39 + 4096), survFactor i) := h1
        exact (ENNReal.add_le_add_iff_right hfin).mp hcomb
      exact hdet.trans hcol_le
    have hsampled :
        (prEvent ((ReplyBad h768) <$> (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      have hswap := distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
        (fun compression permutation => fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget))
      have hpr := (EvalDistEq.of_evalDist_eq hswap).prEvent_eq (ReplyBad h768)
      simp only [Oracle.sample, bind_assoc, pure_bind]
      rw [hpr]
      apply prEvent_bind_le_of_forall_le_of_support
      intro permutation _
      exact hperm permutation
    exact hred.trans hsampled

end CommitGolfCandidate
