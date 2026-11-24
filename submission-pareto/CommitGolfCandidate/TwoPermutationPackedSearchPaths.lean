import CommitGolfCandidate.TwoPermutationPackedSearchLoop
import CommitGolfCandidate.TwoPermutationPackedCapWalk
import CommitGolfCandidate.QuartetConcrete

/-! # One-byte search: paths after an accepting trial, and the honest trial

Binding: an accepting trial records `climbFrom`'s rows from u to a root equal to the commitment. Every opened
(marked) leaf leaves u's path at some level; the node there on the leaf's side is the sibling of a node on u's path.
With u ∈ {510, 511, 255} that sibling is a right-spine node or the left child of one, a survivor of the walk
(`CapSurvivor`), so the walk recorded the leaf's path to its final slot, which the climb then uses. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling CommitGolfCandidate.ShortTree
open TwoPermutationPrototype.Checker (capRootAt)
open TwoPermutationPrototype.Sampling.Quartet (xor_one_cases)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-! ### Paths through a climb -/

theorem climb_path (oracle : Oracle) (σ : Nat → BitVec 256) (rows : List PublicRow) :
    ∀ d n v, (∀ row ∈ (climbFrom oracle σ d n v).1, row ∈ rows) → n < 2^17 →
      ProjectedPath rows n d v (climbFrom oracle σ d n v).2 := by
  intro d
  induction d with
  | zero => intro n v _ _; exact .done n v
  | succ d ih =>
    intro n v inside small
    let pair := pathPair n v (σ (n ^^^ 1))
    have head : PublicRow.compression pair (oracle.compression pair) ∈ rows := inside _ (by simp [climbFrom, pair])
    have tail := ih (n/2) (pad238 (oracle.compression pair)) (fun row found => inside row (by
      simp only [climbFrom]; exact List.mem_cons_of_mem _ found)) (by omega)
    have keep : nodeKeep (n/2) (oracle.compression pair) = pad238 (oracle.compression pair) :=
      node_keep_238 (by omega) _
    have tail' := (congrArg (fun x => ProjectedPath rows (n/2) d x
      (climbFrom oracle σ d (n/2) (pad238 (oracle.compression pair))).2) keep).mpr tail
    exact .step head tail'

theorem pair_flip (n : Nat) (v w : BitVec 256) : pathPair (n ^^^ 1) w v = pathPair n v w := by
  unfold pathPair
  have parity : (n ^^^ 1) % 2 = 0 ↔ ¬ n % 2 = 0 := by
    rw [xor_one_cases]
    split <;> omega
  by_cases even : n % 2 = 0
  · rw [if_neg (fun h => (parity.mp h) even), if_pos even]
  · rw [if_pos (parity.mpr even), if_neg even]

theorem flip_half (n : Nat) : (n ^^^ 1) / 2 = n / 2 := by
  rw [xor_one_cases]
  split <;> omega

/-- A leaf's path to the sibling of the climb's k-th node joins the climb to its root. -/
theorem climb_join (oracle : Oracle) (σ : Nat → BitVec 256) (rows : List PublicRow) :
    ∀ d n v k, (∀ row ∈ (climbFrom oracle σ d n v).1, row ∈ rows) → n < 2^17 → k < d →
      ∀ leaf h start, ProjectedPath rows leaf h start (σ ((n/2^k) ^^^ 1)) → leaf/2^h = (n/2^k) ^^^ 1 →
        ProjectedPath rows leaf (h+(d-k)) start (climbFrom oracle σ d n v).2 := by
  intro d
  induction d with
  | zero => intro _ _ _ bad; omega
  | succ d ih =>
    intro n v k inside small kd leaf h start path hat
    let pair := pathPair n v (σ (n ^^^ 1))
    have rest : ∀ row ∈ (climbFrom oracle σ d (n/2) (pad238 (oracle.compression pair))).1, row ∈ rows :=
      fun row found => inside row (by simp only [climbFrom]; exact List.mem_cons_of_mem _ found)
    cases k with
    | zero =>
      simp only [Nat.pow_zero, Nat.div_one] at path hat
      have head : PublicRow.compression pair (oracle.compression pair) ∈ rows := inside _ (by simp [climbFrom, pair])
      have up := climb_path oracle σ rows d (n/2) (pad238 (oracle.compression pair)) rest (by omega)
      have keep : nodeKeep ((n ^^^ 1)/2) (oracle.compression pair) = pad238 (oracle.compression pair) :=
        node_keep_238 (by rw [flip_half]; omega) _
      have half : (n ^^^ 1)/2 = n/2 := flip_half n
      have edge : ProjectedPath rows (n ^^^ 1) (d+1) (σ (n ^^^ 1)) (climbFrom oracle σ (d+1) n v).2 := by
        apply ProjectedPath.step (sibling := v) (parent := oracle.compression pair)
        · rw [pair_flip]; exact head
        · rw [keep, half]; exact up
      have edge' : ProjectedPath rows (leaf/2^h) (d+1) (σ (n ^^^ 1)) (climbFrom oracle σ (d+1) n v).2 := by
        rw [hat]; exact edge
      have joined := path.append edge'
      simpa using joined
    | succ k =>
      have shifted : n/2^(k+1) = (n/2)/2^k := by
        rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      rw [shifted] at path hat
      have := ih (n/2) (pad238 (oracle.compression pair)) k rest (by omega) (by omega) leaf h start path hat
      simpa [climbFrom, show d+1-(k+1) = d-k by omega] using this

/-! ### The honest trial reaches the honest root -/

theorem climb_honest (oracle : Oracle) (heap : Nat → BitVec 256)
    (correct : ∀ p, 0 < p → p < 256 → heap p = pad238 (oracle.compression (heap (2*p+1) ++ heap (2*p))))
    (σ : Nat → BitVec 256) :
    ∀ d n, 2^d ≤ n → n < 512 → (∀ i, i < d → σ ((n/2^i) ^^^ 1) = heap ((n/2^i) ^^^ 1)) →
      (climbFrom oracle σ d n (heap n)).2 = heap (n/2^d) := by
  intro d
  induction d with
  | zero => intro n _ _ _; simp [climbFrom]
  | succ d ih =>
    intro n lo hi sibs
    have pow : 2^(d+1) = 2*2^d := by rw [Nat.pow_succ]; ring
    have one : 1 ≤ 2^d := Nat.one_le_two_pow
    have sib0 := sibs 0 (by omega)
    simp only [Nat.pow_zero, Nat.div_one] at sib0
    have pairEq : pathPair n (heap n) (σ (n ^^^ 1)) = heap (2*(n/2)+1) ++ heap (2*(n/2)) := by
      rw [sib0]
      unfold pathPair
      by_cases even : n % 2 = 0
      · rw [if_pos even, xor_one_cases, if_pos even, show n+1 = 2*(n/2)+1 by omega,
          show heap n = heap (2*(n/2)) by congr 1; omega]
      · rw [if_neg even, xor_one_cases, if_neg even, show n-1 = 2*(n/2) by omega,
          show heap n = heap (2*(n/2)+1) by congr 1; omega]
    have parent : pad238 (oracle.compression (pathPair n (heap n) (σ (n ^^^ 1)))) = heap (n/2) := by
      rw [pairEq, ← correct (n/2) (by omega) (by omega)]
    have sibsP : ∀ i, i < d → σ (((n/2)/2^i) ^^^ 1) = heap (((n/2)/2^i) ^^^ 1) := by
      intro i small
      have shifted : (n/2)/2^i = n/2^(i+1) := by
        rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      rw [shifted]
      exact sibs (i+1) (by omega)
    have := ih (n/2) (by omega) (by omega) sibsP
    simp only [climbFrom]
    rw [parent, this, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-! ### Survivors along the right spine -/

theorem leaf_mark (groups : List Nat) {leaf : Nat} (member : leaf ∈ groups) (t : Nat) :
    capIsMarked groups (leaf/2^t) t = true := by
  simp only [capIsMarked, List.any_eq_true, beq_iff_eq]
  exact ⟨leaf, member, rfl⟩

theorem survivor_up (groups : List Nat) (node h m hm : Nat) (mk : capIsMarked groups node (h+1) = true)
    (s : CapSurvivor groups (2*node+1) h m hm) : CapSurvivor groups node (h+1) m hm := by
  simp only [CapSurvivor]
  exact Or.inr ⟨mk, Or.inr s⟩

theorem survivor_left (groups : List Nat) (node h : Nat) (mk : capIsMarked groups node (h+1) = true) :
    CapSurvivor groups node (h+1) (2*node) h :=
  Or.inr ⟨mk, Or.inl ⟨rfl, rfl⟩⟩

/-- A survivor of the right-spine node `2^(j+1)-1` survives the whole walk when the spine above is marked. -/
theorem spine_lift (groups : List Nat) (m hm : Nat) :
    ∀ j, j ≤ 8 → (∀ i, i < j → capIsMarked groups (2^(i+1)-1) (8-i) = true) →
      CapSurvivor groups (2^(j+1)-1) (8-j) m hm → CapSurvivor groups 1 8 m hm := by
  intro j
  induction j with
  | zero => intro _ _ s; simpa using s
  | succ j ih =>
    intro hj marks s
    apply ih (by omega) (fun i hi => marks i (by omega))
    have one := Nat.one_le_two_pow (n := j+1)
    have e1 : 2^(j+1+1)-1 = 2*(2^(j+1)-1)+1 := by rw [Nat.pow_succ 2 (j+1)]; omega
    have e2 : 8-j = (8-(j+1))+1 := by omega
    rw [e2]
    apply survivor_up groups _ _ _ _ (by rw [← e2]; exact marks j (by omega))
    rw [← e1]
    exact s

theorem spine_marks (groups : List Nat) {leaf : Nat} (member : leaf ∈ groups) (j : Nat) (hj : j ≤ 7)
    (at_ : leaf/2^(8-j) = 2^(j+1)-1) : ∀ i, i ≤ j → capIsMarked groups (2^(i+1)-1) (8-i) = true := by
  intro i hi
  have e : leaf/2^(8-i) = 2^(i+1)-1 := by
    rw [show 8-i = (8-j)+(j-i) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul, at_]
    interval_cases j <;> interval_cases i <;> decide
  rw [← e]
  exact leaf_mark groups member _

/-- The sibling of a node on u's path, where an opened leaf leaves that path, survives the walk. -/
theorem meet_survivor (groups : List Nat) {leaf : Nat} (member : leaf ∈ groups) (j : Nat) (hj : j ≤ 7)
    (parent : leaf/2^(8-j) = 2^(j+1)-1) (c : Nat) (child : c = 2*(2^(j+1)-1) ∨ c = 2*(2^(j+1)-1)+1) :
    CapSurvivor groups 1 8 c (7-j) := by
  have marks := spine_marks groups member j hj parent
  have mk : capIsMarked groups (2^(j+1)-1) ((7-j)+1) = true := by
    rw [show (7-j)+1 = 8-j by omega]; exact marks j (le_refl _)
  have base : CapSurvivor groups (2^(j+1)-1) ((7-j)+1) c (7-j) := by
    rcases child with rfl | rfl
    · exact survivor_left groups _ _ mk
    · exact survivor_up groups _ _ _ _ mk (CapSurvivor.self _ _ _)
  rw [show (7-j)+1 = 8-j by omega] at base
  exact spine_lift groups c (7-j) j (by omega) (fun i hi => marks i (by omega)) base

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 4096 in
/-- The meeting table, checked by the kernel for every leaf. -/
theorem meet_table (u : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511) :
    ∀ leaf, leaf < 512 → 256 ≤ leaf → leaf ≠ u → (u = 255 → leaf ≠ 510 ∧ leaf ≠ 511) →
    ∃ k, k < 8 ∧ ∃ j, j < 8 ∧ k < depthOf u ∧ k+(8-depthOf u) = 7-j ∧ leaf/2^(7-j) = (u/2^k) ^^^ 1 ∧
      leaf/2^(8-j) = 2^(j+1)-1 ∧ ((u/2^k) ^^^ 1 = 2*(2^(j+1)-1) ∨ (u/2^k) ^^^ 1 = 2*(2^(j+1)-1)+1) := by
  rcases node with rfl | rfl | rfl <;> decide +kernel

/-- Where an opened leaf leaves u's path: level k, the sibling's height `7 - j`, and its parent on the spine. -/
theorem meet_point (u : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511) (leaf : Nat) (lo : 256 ≤ leaf) (hi : leaf < 512)
    (other : leaf ≠ u) (notBelow : u = 255 → leaf ≠ 510 ∧ leaf ≠ 511) :
    ∃ k, k < depthOf u ∧ ∃ j, j ≤ 7 ∧ k+(8-depthOf u) = 7-j ∧ leaf/2^(7-j) = (u/2^k) ^^^ 1 ∧
      leaf/2^(8-j) = 2^(j+1)-1 ∧ ((u/2^k) ^^^ 1 = 2*(2^(j+1)-1) ∨ (u/2^k) ^^^ 1 = 2*(2^(j+1)-1)+1) := by
  obtain ⟨k, _, j, jb, kd, height, at_, parent, child⟩ := meet_table u node leaf hi lo other notBelow
  exact ⟨k, kd, j, by omega, height, at_, parent, child⟩

/-- Binding after an accepting trial: every opened leaf has a recorded path to the trial's root. -/
theorem search_binding (oracle : Oracle) (groups : List Nat) (σ : Nat → BitVec 256) (rows : List PublicRow)
    (start : Nat → BitVec 256) (u : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511)
    (unmarked : u = 255 → capIsMarked groups 510 0 = false ∧ capIsMarked groups 511 0 = false)
    (unmarkedLeaf : u ≠ 255 → capIsMarked groups u 0 = false)
    (survivors : ∀ m hm, CapSurvivor groups 1 8 m hm → ∀ leaf ∈ groups, 256 ≤ leaf → leaf < 512 → leaf/2^hm = m →
      ProjectedPath rows leaf hm (start leaf) (σ m))
    (v : BitVec 256) (climbIn : ∀ row ∈ (climbFrom oracle σ (depthOf u) u v).1, row ∈ rows) :
    ∀ leaf ∈ groups, 256 ≤ leaf → leaf < 512 →
      ProjectedPath rows leaf 8 (start leaf) (climbFrom oracle σ (depthOf u) u v).2 := by
  intro leaf member lo hi
  have marked : capIsMarked groups leaf 0 = true := by simpa using leaf_mark groups member 0
  have other : leaf ≠ u := by
    intro same
    subst same
    by_cases top : leaf = 255
    · omega
    · rw [unmarkedLeaf top] at marked; cases marked
  have notBelow : u = 255 → leaf ≠ 510 ∧ leaf ≠ 511 := by
    intro h
    obtain ⟨a, b⟩ := unmarked h
    constructor <;> rintro rfl <;> simp_all
  obtain ⟨k, kd, j, hj, height, at_, parent, child⟩ := meet_point u node leaf lo hi other notBelow
  have surv := meet_survivor groups member j hj parent _ child
  have walk := survivors _ _ surv leaf member lo hi at_
  have uSmall : u < 2^17 := by rcases node with rfl | rfl | rfl <;> decide
  have joined := climb_join oracle σ rows (depthOf u) u v k climbIn uSmall kd leaf (7-j) (start leaf) walk at_
  have total : 7-j+(depthOf u-k) = 8 := by
    have : depthOf u ≤ 8 := depth_le u
    omega
  rw [total] at joined
  exact joined

/-! ### The honest trial -/

theorem eq_of_dwords (v w : BitVec 256) (same : ∀ k < 4, v.extractLsb' (64*k) 64 = w.extractLsb' (64*k) 64) :
    v = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (fun x : BitVec 64 => x.getLsbD (i % 64)) (same (i/64) (by omega))
  simp only [BitVec.getLsbD_extractLsb', Nat.mod_lt i (by decide : 0 < 64), decide_true, Bool.true_and] at e
  rwa [show 64*(i/64)+i%64 = i by omega] at e

/-- The slot u of trial g in terms of the entry slot's doublewords. -/
theorem patched_slot_eq (E : MachineState) (u g : Nat) (hu : u < 512) (target : BitVec 256)
    (low : ∀ k < 3, (capRootAt E u).extractLsb' (64*k) 64 = target.extractLsb' (64*k) 64)
    (top : replaceHalfword ((capRootAt E u).extractLsb' 192 64) 2
      (patchHalf (extractHalfword ((capRootAt E u).extractLsb' 192 64) 2) (BitVec.ofNat 64 g)) =
      target.extractLsb' 192 64) :
    patchedSlot E u g = target := by
  apply eq_of_dwords
  intro k hk
  have slotE (j : Nat) (hj : j < 4) : (capRootAt E u).extractLsb' (64*j) 64 = memoryView E (2048+4*u+j) := by
    unfold capRootAt memoryView wordAddress
    rw [read_digest_word _ _ _ (by omega) hj]
    congr 2
    omega
  unfold patchedSlot capRootAt
  rw [read_digest_word _ _ _ (by omega) hk, show 8*(2048+4*u)+8*k = 8*(2048+4*u+k) by omega]
  change memoryView (patchedState E u g) (2048+4*u+k) = _
  unfold patchedState
  rw [set_top_half E u hu _ _ (by omega)]
  by_cases three : k = 3
  · subst three
    rw [if_pos rfl, get_top_half E u hu, ← slotE 3 (by decide)]
    exact top
  · rw [if_neg (by unfold topWord; omega), ← slotE k hk]
    exact low k (by omega)

theorem honest_trial (oracle : Oracle) (heap : Nat → BitVec 256)
    (correct : ∀ p, 0 < p → p < 256 → heap p = pad238 (oracle.compression (heap (2*p+1) ++ heap (2*p))))
    (E : MachineState) (u g : Nat) (node : u = 255 ∨ u = 510 ∨ u = 511)
    (sibs : ∀ i, i < depthOf u → capRootAt E ((u/2^i) ^^^ 1) = heap ((u/2^i) ^^^ 1))
    (patched : patchedSlot E u g = heap u) :
    (trialClimb oracle E u g).2 = heap 1 := by
  obtain ⟨_, lo, _⟩ := depth_range u node
  unfold trialClimb
  rw [patched, climb_honest oracle heap correct (capRootAt E) (depthOf u) u lo
    (by rcases node with rfl | rfl | rfl <;> decide) sibs]
  rcases node with rfl | rfl | rfl <;> rfl

end TwoPermutationPrototype.Packed.Checker
