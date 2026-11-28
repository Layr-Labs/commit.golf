import CommitGolfCandidate.C3PCommitMeaning

/-! # The paired commit under a fixed oracle: memory of the passes

Each pair touches only its own 64 message words (and, in pass 3, its two 25-word replies). A generic
fold lemma (`fold_memory`) turns a per-pair memory function that is local to its region and the
identity outside it into the memory after a whole pass. -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.C3Leaves (compression_write_memory memoryView_congr addi_mem address_up
  view_store)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000

/-! ### Agreement on a region -/

def AgreeOn (R : Nat → Prop) (A B : Memory) : Prop := ∀ u, R u → A u = B u

theorem write_window_pt {n : Nat} {A B : Memory} {w : Nat} (d : Nat) (ws : Words n) (h : A w = B w) :
    writeWindow A d ws w = writeWindow B d ws w := by
  simp only [writeWindow]; split
  · rfl
  · exact h

theorem write_word_pt {A B : Memory} {w : Nat} (a : Nat) (v : Word) (h : A w = B w) :
    writeWord A a v w = writeWord B a v w := by
  simp only [writeWord]; split
  · rfl
  · exact h

theorem agree_write_window {R : Nat → Prop} {A B : Memory} {n : Nat} (d : Nat) (ws : Words n)
    (h : AgreeOn R A B) : AgreeOn R (writeWindow A d ws) (writeWindow B d ws) :=
  fun u hu => write_window_pt d ws (h u hu)

theorem agree_write_word {R : Nat → Prop} {A B : Memory} (a : Nat) (v : Word) (h : AgreeOn R A B) :
    AgreeOn R (writeWord A a v) (writeWord B a v) :=
  fun u hu => write_word_pt a v (h u hu)

theorem window_agree {R : Nat → Prop} {A B : Memory} {n : Nat} (s : Nat) (h : AgreeOn R A B)
    (inside : ∀ k < n, R (s + k)) : (window A s : Words n) = window B s := by
  funext k; exact h _ (inside k.val k.isLt)

theorem write_word_off (M : Memory) (a w : Nat) (v : Word) (h : w ≠ a) : writeWord M a v w = M w := by
  simp only [writeWord]; rw [if_neg h]

theorem write_word_at (M : Memory) (a : Nat) (v : Word) : writeWord M a v a = v := by
  simp [writeWord]

/-! ### A generic pair loop -/

def foldG {α : Type} (f : Nat → MachineState → α → MachineState) : List α → Nat → MachineState → MachineState
  | [], _, s => s
  | a :: as, p, s => foldG f as (p + 1) (f p s a)

theorem fold_g_cons {α : Type} (f : Nat → MachineState → α → MachineState) (a : α) (as : List α) (p : Nat)
    (s : MachineState) : foldG f (a :: as) p s = foldG f as (p + 1) (f p s a) := rfl

theorem iter_c_fold (f : Nat → MachineState → MachineState) :
    ∀ n p s, iterC f n p s = foldG (fun p s (_ : Unit) => f p s) (List.replicate n ()) p s := by
  intro n
  induction n with
  | zero => intro p s; rfl
  | succ n ih => intro p s; rw [iter_c_succ, ih]; rfl

theorem fold_c_fold (f : Nat → MachineState → BitVec 256 → MachineState) :
    ∀ ws p s, foldC f ws p s = foldG f ws p s := by
  intro ws
  induction ws with
  | nil => intro p s; rfl
  | cons w ws ih => intro p s; rw [fold_c_cons, ih]; rfl

/-- **Memory of a loop over disjoint regions.** Step `p` changes only region `R p`, and what it
writes there depends only on region `R p`. -/
theorem fold_memory {α : Type} (f : Nat → MachineState → α → MachineState) (F : Nat → α → Memory → Memory)
    (R : Nat → Nat → Prop) (Inv : Nat → MachineState → Prop) (top : Nat) (good : α → Prop)
    (inv_step : ∀ p a S, p < top → good a → Inv p S → Inv (p + 1) (f p S a))
    (mem_step : ∀ p a S, p < top → good a → Inv p S → ∀ w < 2 ^ 33,
      memoryView (f p S a) w = F p a (memoryView S) w)
    (loc : ∀ p a M M', p < top → AgreeOn (R p) M M' → AgreeOn (R p) (F p a M) (F p a M'))
    (frame : ∀ p a M w, p < top → ¬ R p w → F p a M w = M w)
    (bound : ∀ p u, p < top → R p u → u < 2 ^ 33)
    (disj : ∀ p q w, p < top → q < top → R p w → R q w → p = q) :
    ∀ (xs : List α) p S, p + xs.length ≤ top → (∀ a ∈ xs, good a) → Inv p S →
      Inv (p + xs.length) (foldG f xs p S) ∧
      (∀ k (hk : k < xs.length) w, R (p + k) w →
        memoryView (foldG f xs p S) w = F (p + k) xs[k] (memoryView S) w) ∧
      (∀ w < 2 ^ 33, (∀ k < xs.length, ¬ R (p + k) w) → memoryView (foldG f xs p S) w = memoryView S w) := by
  intro xs
  induction xs with
  | nil => intro p S _ _ inv; exact ⟨inv, fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  | cons a xs ih =>
    intro p S total goods inv
    simp only [List.length_cons] at total
    have hp : p < top := by omega
    have ga : good a := goods a (List.mem_cons_self ..)
    obtain ⟨inv', mem', out'⟩ := ih (p + 1) (f p S a) (by omega) (fun b hb => goods b (List.mem_cons_of_mem _ hb))
      (inv_step p a S hp ga inv)
    have step := mem_step p a S hp ga inv
    refine ⟨?_, ?_, ?_⟩
    · rw [fold_g_cons, List.length_cons, show p + (xs.length + 1) = p + 1 + xs.length by omega]; exact inv'
    · intro k hk w hw
      simp only [List.length_cons] at hk
      have wb := bound (p + k) w (by omega) hw
      rw [fold_g_cons]
      cases k with
      | zero =>
        rw [Nat.add_zero] at hw
        rw [out' w wb (fun j hj hR => by
          have := disj p (p + 1 + j) w hp (by omega) hw hR; omega), step w wb]
        rfl
      | succ k =>
        have hk' : k < xs.length := by omega
        rw [show p + (k + 1) = p + 1 + k by omega] at hw ⊢
        rw [mem' k hk' w hw, List.getElem_cons_succ]
        apply loc (p + 1 + k) xs[k] _ _ (by omega) _ w hw
        intro u hu
        have ub := bound _ u (by omega) hu
        rw [step u ub, frame p a _ u hp (fun hR => by
          have := disj p (p + 1 + k) u hp (by omega) hR hu; omega)]
    · intro w wb outside
      simp only [List.length_cons] at outside
      rw [fold_g_cons, out' w wb (fun j hj hR => outside (j + 1) (by omega)
          (by rw [show p + (j + 1) = p + 1 + j by omega]; exact hR)),
        step w wb, frame p a _ w hp (fun hR => outside 0 (by omega) (by rw [Nat.add_zero]; exact hR))]

/-! ### Regions -/

def msgR (E u : Nat) : Prop := E ≤ u ∧ u < E + 64

def pairR (E D u : Nat) : Prop := msgR E u ∨ (D ≤ u ∧ u < D + 50)

/-! ### Pass 1 -/

theorem p1_mem_frame (C : Compression) (M : Memory) (E w : Nat) (h : ¬ (E + 24 ≤ w ∧ w < E + 40)) :
    p1Mem C M E w = M w := by
  unfold p1Mem
  rw [write_window_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
    write_window_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega)]

theorem p1_mem_local (C : Compression) (M M' : Memory) (E : Nat) (h : AgreeOn (msgR E) M M') :
    AgreeOn (msgR E) (p1Mem C M E) (p1Mem C M' E) := by
  have inside (s n : Nat) (hs : E ≤ s) (hn : s + n ≤ E + 64) : ∀ k < n, msgR E (s + k) :=
    fun k hk => ⟨by omega, by omega⟩
  have hr : rE C M E = rE C M' E := by
    unfold rE; rw [window_agree (E + 24) h (inside _ 8 (by omega) (by omega))]
  have hq : qE C M E = qE C M' E := by
    unfold qE; rw [window_agree E h (inside _ 8 (by omega) (by omega))]
  have hz : zE C M E = zE C M' E := by unfold zE; rw [hr, hq]
  have hqo : qO C M E = qO C M' E := by
    unfold qO; rw [window_agree (E + 32) h (inside _ 8 (by omega) (by omega))]
  have hro : rO C M E = rO C M' E := by
    unfold rO; rw [window_agree (E + 56) h (inside _ 8 (by omega) (by omega))]
  have hzo : zO C M E = zO C M' E := by unfold zO; rw [hqo, hro]
  intro u hu
  unfold p1Mem
  rw [hr, hz, hqo, hzo]
  exact write_window_pt _ _ (write_window_pt _ _ (write_window_pt _ _ (write_window_pt _ _ (h u hu))))

theorem loop1_next (s : MachineState) (E p : Nat) (inv : Loop1 s E p) (hp : p < 1024)
    (a1 a2 a3 a4 a5 a6 : BitVec COMPRESSION_OUTPUT_LENGTH) :
    Loop1 (p1w6 s (E + 64 * p) a1 a2 a3 a4 a5 a6) E (p + 1) ∧
      (∀ g, g ≠ .x10 → g ≠ .x12 → (p1w6 s (E + 64 * p) a1 a2 a3 a4 a5 a6).getReg g = s.getReg g) := by
  have ready : P1PairReady s p (E + 64 * p) :=
    ⟨inv.pc, inv.source, by have := inv.low; omega, by have := inv.bound; omega, inv.selector, inv.size,
      inv.primitive, hp⟩
  have R := p1_pair_regs s p (E + 64 * p) ready a1 a2 a3 a4 a5 a6
  refine ⟨⟨R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, ?_, inv.low, inv.bound, ?_, ?_, ?_⟩,
    fun g h10 h12 => (R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g h10 h12).2.2.2.2.2.2⟩
  · rw [R.2.2.2.2.2.2.2.2.2.2.2.2.1]; congr 1 <;> omega
  · exact ((R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 .x5 (by decide) (by decide)).2.2.2.2.2.2).trans inv.selector
  · exact ((R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 .x11 (by decide) (by decide)).2.2.2.2.2.2).trans inv.size
  · exact ((R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 .x13 (by decide) (by decide)).2.2.2.2.2.2).trans inv.primitive

/-- Pass 1 of a block: every pair's words are `p1Mem` of its original words; the rest is unchanged. -/
theorem pass1_memory (C : Compression) (E : Nat) (S : MachineState) (inv : Loop1 S E 0) :
    let T := pass1Det C E 1024 0 S
    Loop1 T E 1024 ∧ (∀ g, g ≠ .x10 → g ≠ .x12 → T.getReg g = S.getReg g) ∧
      (∀ p < 1024, ∀ w, msgR (E + 64 * p) w → memoryView T w = p1Mem C (memoryView S) (E + 64 * p) w) ∧
      (∀ w < 2 ^ 33, (∀ p < 1024, ¬ msgR (E + 64 * p) w) → memoryView T w = memoryView S w) := by
  intro T
  have b := inv.bound
  have L := fold_memory (fun p s (_ : Unit) => p1Det C s (E + 64 * p)) (fun p _ M => p1Mem C M (E + 64 * p))
    (fun p u => msgR (E + 64 * p) u)
    (fun p t => Loop1 t E p ∧ ∀ g, g ≠ .x10 → g ≠ .x12 → t.getReg g = S.getReg g) 1024 (fun _ => True)
    (fun p _ t hp _ i => by
      obtain ⟨n1, n2⟩ : Loop1 (p1Det C t (E + 64 * p)) E (p + 1) ∧
          (∀ g : Reg, g ≠ Reg.x10 → g ≠ Reg.x12 → (p1Det C t (E + 64 * p)).getReg g = t.getReg g) := by
        simp only [p1Det]; exact loop1_next t E p i.1 hp _ _ _ _ _ _
      exact ⟨n1, fun g a b => (n2 g a b).trans (i.2 g a b)⟩)
    (fun p _ t hp _ _ w hw => p1_det_memory C t (E + 64 * p) (by omega) w hw)
    (fun p _ M M' _ h => p1_mem_local C M M' (E + 64 * p) h)
    (fun p _ M w _ h => p1_mem_frame C M (E + 64 * p) w (fun ⟨x, y⟩ => h ⟨by omega, by omega⟩))
    (fun p u hp h => by unfold msgR at h; omega)
    (fun p q w _ _ hp hq => by unfold msgR at hp hq; omega)
    (List.replicate 1024 ()) 0 S (by simp) (fun _ _ => trivial) ⟨inv, fun _ _ _ => rfl⟩
  simp only [List.length_replicate, Nat.zero_add] at L
  have e : T = foldG (fun p s (_ : Unit) => p1Det C s (E + 64 * p)) (List.replicate 1024 ()) 0 S :=
    iter_c_fold _ 1024 0 S
  rw [e]
  exact ⟨L.1.1, L.1.2, fun p hp w hw => L.2.1 p (by simpa using hp) w hw, L.2.2⟩

/-! ### Pass 2 -/

theorem p2_after_memory (s : MachineState) (E : Nat) (a : BitVec 256) (bound : E + 64 ≤ 2 ^ 33) :
    ∀ w < 2 ^ 33, memoryView (p2After s E a) w = writeWindow (memoryView s) (E + 30) (digestWords a) w := by
  intro w hw
  rw [show p2After s E a = writeBits (p2Draw s) (wordAddress (E + 30)) a from rfl,
    compression_write_memory _ _ _ _ (by omega) hw,
    show memoryView (p2Draw s) = memoryView s from memoryView_congr (seg1_facts s 512).2.1]

theorem pass2_memory (E : Nat) (ws : List (BitVec 256)) (len : ws.length = 1024) (S : MachineState)
    (inv : Loop2 S E 0) :
    let T := pass2Det E ws 0 S
    Loop2 T E 1024 ∧ (∀ g, g ≠ .x10 → T.getReg g = S.getReg g) ∧
      (∀ p (hp : p < 1024), ∀ w, msgR (E + 64 * p) w →
        memoryView T w = writeWindow (memoryView S) (E + 64 * p + 30) (digestWords ws[p]) w) ∧
      (∀ w < 2 ^ 33, (∀ p < 1024, ¬ msgR (E + 64 * p) w) → memoryView T w = memoryView S w) := by
  intro T
  have b := inv.bound
  have L := fold_memory (fun p s w => p2After s (E + 64 * p) w)
    (fun p a M => writeWindow M (E + 64 * p + 30) (digestWords a))
    (fun p u => msgR (E + 64 * p) u)
    (fun p t => Loop2 t E p ∧ ∀ g, g ≠ .x10 → t.getReg g = S.getReg g) 1024 (fun _ => True)
    (fun p a t hp _ i => by
      have n := loop2_next t E p i.1 hp a
      exact ⟨n.1, fun g h => (n.2 g h).trans (i.2 g h)⟩)
    (fun p a t hp _ _ w hw => p2_after_memory t (E + 64 * p) a (by omega) w hw)
    (fun p a M M' _ h => agree_write_window _ _ h)
    (fun p a M w _ h => write_window_off _ _ _ _ (fun ⟨x, y⟩ => h ⟨by omega, by omega⟩))
    (fun p u hp h => by unfold msgR at h; omega)
    (fun p q w _ _ hp hq => by unfold msgR at hp hq; omega)
    ws 0 S (by omega) (fun _ _ => trivial) ⟨inv, fun _ _ => rfl⟩
  simp only [len, Nat.zero_add] at L
  have e : T = foldG (fun p s w => p2After s (E + 64 * p) w) ws 0 S := fold_c_fold _ ws 0 S
  rw [e]
  exact ⟨L.1.1, L.1.2, fun p hp w hw => L.2.1 p (by omega) w hw, L.2.2⟩

/-! ### Pass 3 -/

def p3M1 (M : Memory) (E : Nat) : Memory := writeWord M (E + 28) (wordAddress (E + 7))
def p3Y1 (P : Sampling.Block → Sampling.Block) (M : Memory) (E : Nat) : Sampling.Block :=
  P (packBuffer (window (p3M1 M E) (E + 7)))
def p3M2 (P : Sampling.Block → Sampling.Block) (M : Memory) (E D : Nat) : Memory :=
  writeWindow (p3M1 M E) D (replyWords (p3Y1 P M E))
def p3M3 (P : Sampling.Block → Sampling.Block) (M : Memory) (E D : Nat) : Memory :=
  writeWord (p3M2 P M E D) (E + 34) (wordAddress (E + 32))
def p3Y2 (P : Sampling.Block → Sampling.Block) (M : Memory) (E D : Nat) : Sampling.Block :=
  P (packBuffer (window (p3M3 P M E D) (E + 32)))
/-- The pair's memory after pass 3: two tags, two replies. -/
def p3Mem (P : Sampling.Block → Sampling.Block) (M : Memory) (E D : Nat) : Memory :=
  writeWindow (p3M3 P M E D) (D + 25) (replyWords (p3Y2 P M E D))

private theorem imm168 : signExtend12 (168 : BitVec 12) = BitVec.ofNat 64 (8 * 21) := by decide
private theorem imm16 : signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 (8 * 2) := by decide

theorem p3_det_memory (P : Sampling.Block → Sampling.Block) (s : MachineState) (p E D : Nat)
    (r : P3PairReady s p E D) : ∀ w < 2 ^ 33, memoryView (p3Det P s E D) w = p3Mem P (memoryView s) E D w := by
  have b := r.bound
  have bD := r.boundD
  let M := memoryView s
  let y1 := P (packBuffer (window (memoryView (p3a s)) (E + 7)))
  let y2 := P (packBuffer (window (memoryView (p3b s D y1)) (E + 32)))
  have F := p3_facts s p E D r y1 y2
  have hA : ∀ w < 2 ^ 33, memoryView (p3a s) w = p3M1 M E w := by
    intro w hw
    have m : (p3a s).mem = ((seg1 s 312).setMem ((seg1 s 312).getReg .x10 + signExtend12 168)
        ((seg1 s 312).getReg .x10)).mem := (tag_facts (seg1 s 312) 168).2.2.2.2
    rw [memoryView_congr m, F.2.2.2.2.2.2.2.2.2.2.1, imm168, address_up,
      view_store _ _ _ _ (by omega) (by omega), memoryView_congr (seg1_facts s 312).2.1]
    rfl
  have e1 : y1 = p3Y1 P M E := by
    show P (packBuffer (window (memoryView (p3a s)) (E + 7))) = P (packBuffer (window (p3M1 M E) (E + 7)))
    congr 2; funext k; exact hA _ (by have := k.isLt; omega)
  have hW : ∀ w < 2 ^ 33, memoryView (p3w1 s D y1) w = p3M2 P M E D w := by
    intro w hw
    rw [show p3w1 s D y1 = writeBits (p3a s) (wordAddress D) y1 from rfl]
    erw [permutation_write_memory _ _ _ _ (by omega) hw]
    unfold p3M2; rw [← e1]
    exact write_window_pt _ _ (hA w hw)
  have hB : ∀ w < 2 ^ 33, memoryView (p3b s D y1) w = p3M3 P M E D w := by
    intro w hw
    have m : (p3b s D y1).mem = ((seg1 (p3w1 s D y1) 200).setMem ((seg1 (p3w1 s D y1) 200).getReg .x10 +
        signExtend12 16) ((seg1 (p3w1 s D y1) 200).getReg .x10)).mem :=
      (tag_facts (seg1 (p3w1 s D y1) 200) 16).2.2.2.2
    rw [memoryView_congr m, F.2.2.2.2.2.2.2.2.2.2.2, imm16, address_up,
      view_store _ _ _ _ (by omega) (by omega), memoryView_congr (seg1_facts (p3w1 s D y1) 200).2.1]
    unfold p3M3
    exact write_word_pt _ _ (hW w hw)
  have e2 : y2 = p3Y2 P M E D := by
    show P (packBuffer (window (memoryView (p3b s D y1)) (E + 32))) = P (packBuffer (window (p3M3 P M E D) (E + 32)))
    congr 2; funext k; exact hB _ (by have := k.isLt; omega)
  intro w hw
  rw [show p3Det P s E D = writeBits (p3b s D y1) (wordAddress (D + 25)) y2 from rfl]
  erw [permutation_write_memory _ _ _ _ (by omega) hw]
  unfold p3Mem; rw [← e2]
  exact write_window_pt _ _ (hB w hw)

theorem p3_mem_local (P : Sampling.Block → Sampling.Block) (M M' : Memory) (E D : Nat)
    (h : AgreeOn (pairR E D) M M') : AgreeOn (pairR E D) (p3Mem P M E D) (p3Mem P M' E D) := by
  have h1 : AgreeOn (pairR E D) (p3M1 M E) (p3M1 M' E) := agree_write_word _ _ h
  have y1 : p3Y1 P M E = p3Y1 P M' E := by
    unfold p3Y1; rw [window_agree (E + 7) h1 (fun k hk => Or.inl ⟨by omega, by omega⟩)]
  have h2 : AgreeOn (pairR E D) (p3M2 P M E D) (p3M2 P M' E D) := by
    unfold p3M2; rw [y1]; exact agree_write_window _ _ h1
  have h3 : AgreeOn (pairR E D) (p3M3 P M E D) (p3M3 P M' E D) := agree_write_word _ _ h2
  have y2 : p3Y2 P M E D = p3Y2 P M' E D := by
    unfold p3Y2; rw [window_agree (E + 32) h3 (fun k hk => Or.inl ⟨by omega, by omega⟩)]
  unfold p3Mem; rw [y2]; exact agree_write_window _ _ h3

theorem p3_mem_frame (P : Sampling.Block → Sampling.Block) (M : Memory) (E D w : Nat) (h : ¬ pairR E D w) :
    p3Mem P M E D w = M w := by
  unfold pairR msgR at h
  unfold p3Mem p3M3 p3M2 p3M1
  rw [write_window_off _ _ _ _ (by omega), write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
    write_word_off _ _ _ _ (by omega)]

theorem pass3_memory (P : Sampling.Block → Sampling.Block) (E D : Nat) (S : MachineState) (inv : Loop3 S E D 0)
    (sep : E + 65536 ≤ D) :
    let T := pass3Det P E D 1024 0 S
    Loop3 T E D 1024 ∧ (∀ g, g ≠ .x10 → g ≠ .x12 → T.getReg g = S.getReg g) ∧
      (∀ p < 1024, ∀ w, pairR (E + 64 * p) (D + 50 * p) w →
        memoryView T w = p3Mem P (memoryView S) (E + 64 * p) (D + 50 * p) w) ∧
      (∀ w < 2 ^ 33, (∀ p < 1024, ¬ pairR (E + 64 * p) (D + 50 * p) w) → memoryView T w = memoryView S w) := by
  intro T
  have b := inv.bound
  have bD := inv.boundD
  have L := fold_memory (fun p s (_ : Unit) => p3Det P s (E + 64 * p) (D + 50 * p))
    (fun p _ M => p3Mem P M (E + 64 * p) (D + 50 * p))
    (fun p u => pairR (E + 64 * p) (D + 50 * p) u)
    (fun p t => Loop3 t E D p ∧ ∀ g, g ≠ .x10 → g ≠ .x12 → t.getReg g = S.getReg g) 1024 (fun _ => True)
    (fun p _ t hp _ i => by
      obtain ⟨n1, n2⟩ : Loop3 (p3Det P t (E + 64 * p) (D + 50 * p)) E D (p + 1) ∧
          (∀ g : Reg, g ≠ Reg.x10 → g ≠ Reg.x12 → (p3Det P t (E + 64 * p) (D + 50 * p)).getReg g = t.getReg g) := by
        simp only [p3Det]; exact loop3_next t E D p i.1 hp _ _
      exact ⟨n1, fun g a b => (n2 g a b).trans (i.2 g a b)⟩)
    (fun p _ t hp _ i w hw => by
      have inv := i.1
      have ready : P3PairReady t p (E + 64 * p) (D + 50 * p) :=
        ⟨inv.pc, inv.source, inv.target, by have := inv.low; omega, by have := inv.lowD; omega,
          by have := inv.bound; omega, by have := inv.boundD; omega, inv.selector, inv.size, inv.primitive, hp⟩
      exact p3_det_memory P t p _ _ ready w hw)
    (fun p _ M M' _ h => p3_mem_local P M M' _ _ h)
    (fun p _ M w _ h => p3_mem_frame P M _ _ w h)
    (fun p u hp h => by unfold pairR msgR at h; omega)
    (fun p q w hp hq a c => by unfold pairR msgR at a c; omega)
    (List.replicate 1024 ()) 0 S (by simp) (fun _ _ => trivial) ⟨inv, fun _ _ _ => rfl⟩
  simp only [List.length_replicate, Nat.zero_add] at L
  have e : T = foldG (fun p s (_ : Unit) => p3Det P s (E + 64 * p) (D + 50 * p)) (List.replicate 1024 ()) 0 S :=
    iter_c_fold _ 1024 0 S
  rw [e]
  exact ⟨L.1.1, L.1.2, fun p hp w hw => L.2.1 p (by simpa using hp) w hw, L.2.2⟩

end TwoPermutationPrototype.RV64.C3P
