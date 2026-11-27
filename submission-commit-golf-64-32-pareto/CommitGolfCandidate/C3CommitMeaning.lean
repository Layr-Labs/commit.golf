import CommitGolfCandidate.C3CommitLoop
import CommitGolfCandidate.TwoPermutationPackedLeafInput

/-! # What the 3c1p commit loop computes

`C3State oracle before s done chained`: leaves below `done` have their digest in their heap slot,
leaves in `[done, chained)` have passed pass 1 (their words `0..18` are the entry's and `21..25`
hold `t3`), leaves from `chained` on are untouched, and every salt is intact. Pass 1 moves
`chained`, pass 3 moves `done`; after 8,192 blocks every heap leaf slot holds the 3c1p digest. -/
namespace TwoPermutationPrototype.RV64.C3Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure check_evaluation_support
  check_evaluation_public_bind splitBlocks read_buffer_memory_congr)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option autoImplicit false

def c3Reply (oracle : Oracle) (before : Memory) (i : Index) : Block :=
  oracle.permutation (c3PermInput oracle.compression i (window before (leafSalt i.val)) (window before (leafBase i.val)))

structure C3State (oracle : Oracle) (before : Memory) (s : MachineState) (done chained : Nat) : Prop where
  digests : ∀ i : Index, i.val < done →
    (window (memoryView s) (leafDest i.val) : Words 4) = lowDigest (replyWords (c3Reply oracle before i))
  chain : ∀ i, done ≤ i → i < chained → i < 2 ^ 24 →
    (∀ k < 18, memoryView s (leafBase i + k) = before (leafBase i + k)) ∧
    (window (memoryView s) (leafBase i + 21) : Words 4) =
      digestWords (c3T3 oracle.compression (window before (leafBase i)))
  fresh : ∀ i, chained ≤ i → i < 2 ^ 24 → (window (memoryView s) (leafBase i) : Words 32) = window before (leafBase i)
  salts : ∀ i < 2 ^ 24, (window (memoryView s) (leafSalt i) : Words 2) = window before (leafSalt i)

theorem c3_state_start (oracle : Oracle) (s : MachineState) : C3State oracle (memoryView s) s 0 0 :=
  ⟨fun _ impossible => False.elim (by omega), fun _ _ impossible => False.elim (by omega), fun _ _ _ => rfl,
    fun _ _ => rfl⟩

theorem c3_state_mem (oracle : Oracle) (before : Memory) (s t : MachineState) (done chained : Nat)
    (same : t.mem = s.mem) (prev : C3State oracle before s done chained) : C3State oracle before t done chained := by
  have mem : memoryView t = memoryView s := memoryView_congr same
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; rw [mem]; exact prev.digests i hi
  · intro i lo hi top; rw [mem]; exact prev.chain i lo hi top
  · intro i lo hi; rw [mem]; exact prev.fresh i lo hi
  · intro i hi; rw [mem]; exact prev.salts i hi

/-! ### Pass 1, one leaf -/

theorem p1_eval (oracle : Oracle) (s : MachineState) (base : Nat) :
    (checkEvaluation oracle (p1Trace s base)).1 =
      let t1 := oracle.compression (readBuffer (p1a s) (8 * (base + 24)) 64)
      let t2 := oracle.compression (readBuffer (p1b s base t1) (8 * (base + 20)) 64)
      let t3 := oracle.compression (readBuffer (p1c s base t1 t2) (8 * (base + 18)) 64)
      p1d s base t1 t2 t3 := by
  simp only [p1Trace, check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem p1Mem_outside (M : Memory) (base : Nat) (t1 t2 t3 : BitVec 256) (w : Nat)
    (outside : w < base + 21 ∨ base + 28 ≤ w) : p1Mem M base t1 t2 t3 w = M w := by
  have a : ¬ (base + 21 ≤ w ∧ w < base + 21 + 4) := by omega
  have b : ¬ (base + 24 ≤ w ∧ w < base + 24 + 4) := by omega
  simp only [p1Mem, writeWindow, dite_eq_right a, dite_eq_right b]

theorem p1Mem_t3 (M : Memory) (base : Nat) (t1 t2 t3 : BitVec 256) :
    (window (p1Mem M base t1 t2 t3) (base + 21) : Words 4) = digestWords t3 := by
  funext k
  have inside : base + 21 ≤ base + 21 + k.val ∧ base + 21 + k.val < base + 21 + 4 := by omega
  simp only [window, p1Mem, writeWindow, dite_eq_left inside]
  congr 1
  ext
  simp

theorem p1_step (oracle : Oracle) (before : Memory) (s : MachineState) (done i : Nat) (lower : done ≤ i)
    (top : i < 2 ^ 24) (ready : P1Ready s (leafBase i)) (prev : C3State oracle before s done i) :
    C3State oracle before (checkEvaluation oracle (p1Trace s (leafBase i))).1 done (i + 1) := by
  have room : leafBase i + 32 ≤ 2 ^ 33 := ready.bound
  have v : (window (memoryView s) (leafBase i) : Words 32) = window before (leafBase i) :=
    prev.fresh i (by omega) top
  have h1 : oracle.compression (readBuffer (p1a s) (8 * (leafBase i + 24)) 64) =
      c3T1 oracle.compression (window before (leafBase i)) := by
    rw [p1_first_input, v]; rfl
  have h2 : oracle.compression (readBuffer (p1b s (leafBase i) (c3T1 oracle.compression (window before (leafBase i))))
      (8 * (leafBase i + 20)) 64) = c3T2 oracle.compression (window before (leafBase i)) := by
    rw [p1_second_input s _ ready, v]; rfl
  have h3 : oracle.compression (readBuffer (p1c s (leafBase i) (c3T1 oracle.compression (window before (leafBase i)))
      (c3T2 oracle.compression (window before (leafBase i)))) (8 * (leafBase i + 18)) 64) =
      c3T3 oracle.compression (window before (leafBase i)) := by
    rw [p1_third_input s _ ready, v]; rfl
  rw [p1_eval]
  dsimp only
  rw [h1, h2, h3]
  have view (w : Nat) (hw : w < 2 ^ 33) :
      memoryView (p1d s (leafBase i) (c3T1 oracle.compression (window before (leafBase i)))
        (c3T2 oracle.compression (window before (leafBase i))) (c3T3 oracle.compression (window before (leafBase i)))) w =
      p1Mem (memoryView s) (leafBase i) (c3T1 oracle.compression (window before (leafBase i)))
        (c3T2 oracle.compression (window before (leafBase i))) (c3T3 oracle.compression (window before (leafBase i))) w :=
    p1d_memory s _ ready _ _ _ w hw
  have frame (w : Nat) (hw : w < 2 ^ 33) (outside : w < leafBase i + 21 ∨ leafBase i + 28 ≤ w) :
      memoryView (p1d s (leafBase i) (c3T1 oracle.compression (window before (leafBase i)))
        (c3T2 oracle.compression (window before (leafBase i))) (c3T3 oracle.compression (window before (leafBase i)))) w =
      memoryView s w :=
    (view w hw).trans (p1Mem_outside _ _ _ _ _ w outside)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    funext k
    have jt : j.val < 2 ^ 24 := j.isLt
    have kt := k.isLt
    change memoryView _ (leafDest j.val + k.val) = _
    rw [frame _ (by unfold leafDest; omega) (Or.inr (by unfold leafBase leafDest; omega))]
    exact congrFun (prev.digests j hj) k
  · intro j lo hi topj
    by_cases last : j = i
    · subst j
      refine ⟨fun k hk => ?_, ?_⟩
      · rw [frame _ (by unfold leafBase at room ⊢; omega) (Or.inl (by omega))]
        have := congrFun v ⟨k, by omega⟩
        simpa [window] using this
      · funext k
        have kt := k.isLt
        change memoryView _ (leafBase i + 21 + k.val) = _
        rw [view _ (by omega)]
        exact congrFun (p1Mem_t3 (memoryView s) _ _ _ _) k
    · have earlier : j < i := by omega
      have old := prev.chain j lo earlier topj
      refine ⟨fun k hk => ?_, ?_⟩
      · rw [frame _ (by unfold leafBase; omega) (Or.inl (by unfold leafBase; omega))]
        exact old.1 k hk
      · funext k
        have kt := k.isLt
        change memoryView _ (leafBase j + 21 + k.val) = _
        rw [frame _ (by unfold leafBase; omega) (Or.inl (by unfold leafBase; omega))]
        exact congrFun old.2 k
  · intro j lo topj
    funext k
    have kt := k.isLt
    change memoryView _ (leafBase j + k.val) = _
    rw [frame _ (by unfold leafBase; omega) (Or.inr (by unfold leafBase; omega))]
    exact congrFun (prev.fresh j (by omega) topj) k
  · intro j hj
    funext k
    have kt := k.isLt
    change memoryView _ (leafSalt j + k.val) = _
    rw [frame _ (by unfold leafSalt; omega) (Or.inr (by unfold leafBase leafSalt; omega))]
    exact congrFun (prev.salts j hj) k

theorem pass1_state (oracle : Oracle) (before : Memory) (s : MachineState) (g cnt j : Nat) (bound : g < 8192)
    (inside : j + cnt ≤ 2048) (r : P1Regs s g j) (prev : C3State oracle before s (2048 * g) (2048 * g + j)) :
    C3State oracle before (checkEvaluation oracle (pass1 g cnt j s)).1 (2048 * g) (2048 * g + j + cnt) := by
  induction cnt generalizing s j with
  | zero => simpa only [pass1, check_evaluation_pure, Nat.add_zero] using prev
  | succ k ih =>
    simp only [pass1, check_evaluation_bind]
    have next := p1_step oracle before s (2048 * g) (2048 * g + j) (by omega) (by omega)
      (p1_ready s g j bound (by omega) r) prev
    have regs := (p1_trace_post s g j bound (by omega) r (check_evaluation_support oracle _)).1
    rw [show 2048 * g + j + (k + 1) = 2048 * g + (j + 1) + k by omega]
    exact ih _ (j + 1) (by omega) regs (by simpa only [← Nat.add_assoc] using next)

/-! ### Pass 3, one leaf -/

theorem p3_unit_eval (oracle : Oracle) (s : MachineState) (g j : Nat) :
    (checkEvaluation oracle (p3Unit g j s)).1 =
      rebased3 (p3Final s j (leafDest (2048 * g + j))
        (oracle.permutation (packBuffer (window (memoryView (p3Prep s j)) (leafBase (2048 * g + j)))))) j := by
  simp only [p3Unit, p3Trace, check_evaluation_bind, check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem rebased3_mem (s : MachineState) (j : Nat) : (rebased3 s j).mem = s.mem := by
  unfold rebased3 heapUpdate3 nonceUpdate3; split <;> split <;> rfl

theorem tag_address (i : Index) : wordAddress (leafBase i.val) = c3Tag i := by
  unfold wordAddress leafBase c3Tag; congr 1; omega

theorem p3_input (oracle : Oracle) (before : Memory) (s : MachineState) (g j : Nat) (bound : g < 8192)
    (inside : j < 2048) (r : P3Regs s g j) (chained : Nat)
    (prev : C3State oracle before s (2048 * g + j) chained) (ahead : 2048 * g + j < chained)
    (i : Index) (hi : i.val = 2048 * g + j) :
    packBuffer (window (memoryView (p3Prep s j)) (leafBase (2048 * g + j))) =
      c3PermInput oracle.compression i (window before (leafSalt i.val)) (window before (leafBase i.val)) := by
  obtain ⟨iv, ilt⟩ := i
  change iv = 2048 * g + j at hi
  subst hi
  have ready := p3_ready s g j bound inside r
  have room := ready.sourceBound
  have chain := prev.chain (2048 * g + j) (by omega) ahead (by omega)
  have saltsSame := prev.salts (2048 * g + j) (by omega)
  have prep := (p3_prep_facts s j _ _ _ ready).1
  unfold c3PermInput
  congr 1
  funext k
  have kt := k.isLt
  change memoryView (p3Prep s j) (leafBase (2048 * g + j) + k.val) = _
  rw [prep _ (by omega), salt_word_of_block]
  have F (x : Nat) (h : x ≠ 18 ∧ x ≠ 19 ∧ x ≠ 20) :
      p3Stamp (memoryView s) (leafBase (2048 * g + j)) (wordAddress (leafBase (2048 * g + j)))
        (memoryView s (leafSalt (2048 * g + j))) (memoryView s (leafSalt (2048 * g + j) + 1))
        (leafBase (2048 * g + j) + x) = memoryView s (leafBase (2048 * g + j) + x) := by
    unfold p3Stamp
    simp only [writeWord, show leafBase (2048 * g + j) + x ≠ leafBase (2048 * g + j) + 20 by omega,
      show leafBase (2048 * g + j) + x ≠ leafBase (2048 * g + j) + 19 by omega,
      show leafBase (2048 * g + j) + x ≠ leafBase (2048 * g + j) + 18 by omega, ite_false]
  have S18 : p3Stamp (memoryView s) (leafBase (2048 * g + j)) (wordAddress (leafBase (2048 * g + j)))
      (memoryView s (leafSalt (2048 * g + j))) (memoryView s (leafSalt (2048 * g + j) + 1))
      (leafBase (2048 * g + j) + 18) = wordAddress (leafBase (2048 * g + j)) := by
    unfold p3Stamp
    simp only [writeWord, show leafBase (2048 * g + j) + 18 ≠ leafBase (2048 * g + j) + 20 by omega,
      show leafBase (2048 * g + j) + 18 ≠ leafBase (2048 * g + j) + 19 by omega, ite_false, ite_true]
  have S19 : p3Stamp (memoryView s) (leafBase (2048 * g + j)) (wordAddress (leafBase (2048 * g + j)))
      (memoryView s (leafSalt (2048 * g + j))) (memoryView s (leafSalt (2048 * g + j) + 1))
      (leafBase (2048 * g + j) + 19) = memoryView s (leafSalt (2048 * g + j)) := by
    unfold p3Stamp
    simp only [writeWord, show leafBase (2048 * g + j) + 19 ≠ leafBase (2048 * g + j) + 20 by omega, ite_false,
      ite_true]
  have S20 : p3Stamp (memoryView s) (leafBase (2048 * g + j)) (wordAddress (leafBase (2048 * g + j)))
      (memoryView s (leafSalt (2048 * g + j))) (memoryView s (leafSalt (2048 * g + j) + 1))
      (leafBase (2048 * g + j) + 20) = memoryView s (leafSalt (2048 * g + j) + 1) := by
    unfold p3Stamp
    simp only [writeWord, ite_true]
  have salt0 : memoryView s (leafSalt (2048 * g + j)) = before (leafSalt (2048 * g + j)) := by
    have := congrFun saltsSame ⟨0, by decide⟩
    simpa [window] using this
  have salt1 : memoryView s (leafSalt (2048 * g + j) + 1) = before (leafSalt (2048 * g + j) + 1) := by
    have := congrFun saltsSame ⟨1, by decide⟩
    simpa [window] using this
  by_cases low : k.val < 18
  · rw [F k.val (by omega)]
    simp only [c3PermWords, low, dite_true]
    exact chain.1 k.val low
  by_cases tag : k.val = 18
  · have kk : k = ⟨18, by decide⟩ := Fin.ext tag
    subst kk
    rw [S18]
    simp only [c3PermWords, show ¬ (18 < 18) by decide, dite_false, ite_true]
    exact tag_address ⟨2048 * g + j, ilt⟩
  by_cases n0 : k.val = 19
  · have kk : k = ⟨19, by decide⟩ := Fin.ext n0
    subst kk
    rw [S19, salt0]
    simp only [c3PermWords, show ¬ (19 < 18) by decide, show (19 : Nat) ≠ 18 by decide, show 19 < 21 by decide,
      dite_false, ite_false, dite_true]
    rfl
  by_cases n1 : k.val = 20
  · have kk : k = ⟨20, by decide⟩ := Fin.ext n1
    subst kk
    rw [S20, salt1]
    simp only [c3PermWords, show ¬ (20 < 18) by decide, show (20 : Nat) ≠ 18 by decide, show 20 < 21 by decide,
      dite_false, ite_false, dite_true]
    rfl
  · rw [F k.val (by omega)]
    simp only [c3PermWords, low, tag, dite_false, ite_false, show ¬ k.val < 21 by omega]
    have := congrFun chain.2 ⟨k.val - 21, by omega⟩
    simp only [window] at this
    rw [show leafBase (2048 * g + j) + 21 + (k.val - 21) = leafBase (2048 * g + j) + k.val by omega] at this
    exact this

theorem p3_step (oracle : Oracle) (before : Memory) (s : MachineState) (g j : Nat) (bound : g < 8192)
    (inside : j < 2048) (r : P3Regs s g j) (chained : Nat) (ahead : 2048 * g + j < chained)
    (limit : chained ≤ 2 ^ 24)
    (prev : C3State oracle before s (2048 * g + j) chained) :
    C3State oracle before (checkEvaluation oracle (p3Unit g j s)).1 (2048 * g + j + 1) chained := by
  have ready := p3_ready s g j bound inside r
  have idx : 2048 * g + j < LENGTH := by change _ < 2 ^ 24; omega
  have input := p3_input oracle before s g j bound inside r chained prev ahead ⟨2048 * g + j, idx⟩ rfl
  rw [p3_unit_eval]
  apply c3_state_mem oracle before _ _ _ _ (rebased3_mem _ j)
  rw [input]
  have view (w : Nat) (hw : w < 2 ^ 33) := p3_final_memory s j _ _ _ ready
    (c3Reply oracle before ⟨2048 * g + j, idx⟩) w hw
  have frame (w : Nat) (hw : w < 2 ^ 33)
      (heapOut : w < leafDest (2048 * g + j) ∨ leafDest (2048 * g + j) + 25 ≤ w)
      (stampOut : w ≠ leafBase (2048 * g + j) + 18 ∧ w ≠ leafBase (2048 * g + j) + 19 ∧
        w ≠ leafBase (2048 * g + j) + 20) :
      memoryView (p3Final s j (leafDest (2048 * g + j)) (c3Reply oracle before ⟨2048 * g + j, idx⟩)) w =
        memoryView s w := by
    rw [view w hw]
    have outside : ¬ (leafDest (2048 * g + j) ≤ w ∧ w < leafDest (2048 * g + j) + 25) := by omega
    rw [writeWindow, dite_eq_right outside]
    unfold p3Stamp
    simp only [writeWord, stampOut.1, stampOut.2.1, stampOut.2.2, ite_false]
  change C3State oracle before
    (p3Final s j (leafDest (2048 * g + j)) (c3Reply oracle before ⟨2048 * g + j, idx⟩)) (2048 * g + j + 1) chained
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    funext w
    have kt : k.val < 2 ^ 24 := k.isLt
    have wt := w.isLt
    change memoryView _ (leafDest k.val + w.val) = _
    by_cases last : k.val = 2048 * g + j
    · have kk : k = ⟨2048 * g + j, idx⟩ := Fin.ext last
      subst kk
      rw [view _ (by unfold leafDest; omega)]
      have inside' : leafDest (2048 * g + j) ≤ leafDest (2048 * g + j) + w.val ∧
          leafDest (2048 * g + j) + w.val < leafDest (2048 * g + j) + 25 := by omega
      rw [writeWindow, dite_eq_left inside']
      simp only [lowDigest]
      congr 1
      ext
      simp
    · have earlier : k.val < 2048 * g + j := by omega
      rw [frame _ (by unfold leafDest; omega) (Or.inl (by unfold leafDest; omega))
        ⟨by unfold leafBase leafDest; omega, by unfold leafBase leafDest; omega, by unfold leafBase leafDest; omega⟩]
      exact congrFun (prev.digests k earlier) w
  · intro k lo hi topk
    have old := prev.chain k (by omega) hi topk
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [frame _ (by unfold leafBase; omega) (Or.inl (by unfold leafBase leafDest; omega))
        ⟨by unfold leafBase; omega, by unfold leafBase; omega, by unfold leafBase; omega⟩]
      exact old.1 w hw
    · funext w
      have wt := w.isLt
      change memoryView _ (leafBase k + 21 + w.val) = _
      rw [frame _ (by unfold leafBase; omega) (Or.inl (by unfold leafBase leafDest; omega))
        ⟨by unfold leafBase; omega, by unfold leafBase; omega, by unfold leafBase; omega⟩]
      exact congrFun old.2 w
  · intro k lo topk
    funext w
    have wt := w.isLt
    change memoryView _ (leafBase k + w.val) = _
    rw [frame _ (by unfold leafBase; omega) (Or.inl (by unfold leafBase leafDest; omega))
      ⟨by unfold leafBase; omega, by unfold leafBase; omega, by unfold leafBase; omega⟩]
    exact congrFun (prev.fresh k lo topk) w
  · intro k hk
    funext w
    have wt := w.isLt
    change memoryView _ (leafSalt k + w.val) = _
    rw [frame _ (by unfold leafSalt; omega) (Or.inr (by unfold leafSalt leafDest; omega))
      ⟨by unfold leafBase leafSalt; omega, by unfold leafBase leafSalt; omega, by unfold leafBase leafSalt; omega⟩]
    exact congrFun (prev.salts k hk) w

theorem pass3_state (oracle : Oracle) (before : Memory) (s : MachineState) (g cnt j : Nat) (bound : g < 8192)
    (inside : j + cnt ≤ 2048) (r : P3Regs s g j)
    (prev : C3State oracle before s (2048 * g + j) (2048 * g + 2048)) :
    C3State oracle before (checkEvaluation oracle (pass3 g cnt j s)).1 (2048 * g + j + cnt) (2048 * g + 2048) := by
  induction cnt generalizing s j with
  | zero => simpa only [pass3, check_evaluation_pure, Nat.add_zero] using prev
  | succ k ih =>
    simp only [pass3, check_evaluation_bind]
    have next := p3_step oracle before s g j bound (by omega) r (2048 * g + 2048) (by omega) (by omega) prev
    have regs := (p3_unit_post s g j bound (by omega) r (check_evaluation_support oracle _)).1
    rw [show 2048 * g + j + (k + 1) = 2048 * g + (j + 1) + k by omega]
    exact ih _ (j + 1) (by omega) regs (by simpa only [← Nat.add_assoc] using next)

/-! ### Blocks -/

theorem eval_fst_bind (oracle : Oracle) {α β : Type} (p : OracleComp World α) (f : α → OracleComp World β) :
    (checkEvaluation oracle (p >>= f)).1 = (checkEvaluation oracle (f (checkEvaluation oracle p).1)).1 := by
  rw [check_evaluation_bind]

theorem eval_fst_pure (oracle : Oracle) {α : Type} (a : α) : (checkEvaluation oracle (pure a)).1 = a := by
  rw [check_evaluation_pure]

theorem block_eval (oracle : Oracle) (g : Nat) (s : MachineState) :
    (checkEvaluation oracle (blockTrace g s)).1 =
      (checkEvaluation oracle (pass3 g 2048 0
        (switchState (checkEvaluation oracle (pass1 g 2048 0 (entryState s))).1))).1.setPC (c3LatchPC g) := by
  unfold blockTrace
  rw [eval_fst_bind, eval_fst_bind, eval_fst_pure]

theorem set_pc_mem (t : MachineState) (pc : Word) : (t.setPC pc).mem = t.mem := rfl

theorem block_state (oracle : Oracle) (before : Memory) (s : MachineState) (g : Nat) (bound : g < 8192)
    (r : BlockRegs s g) (prev : C3State oracle before s (2048 * g) (2048 * g)) :
    C3State oracle before (checkEvaluation oracle (blockTrace g s)).1 (2048 * (g + 1)) (2048 * (g + 1)) := by
  obtain ⟨e1, e18, _, emem⟩ := entry_facts s g bound r
  have start : C3State oracle before (entryState s) (2048 * g) (2048 * g + 0) :=
    c3_state_mem oracle before s _ _ _ emem (by simpa only [Nat.add_zero] using prev)
  have afterP1 := pass1_state oracle before (entryState s) g 2048 0 bound (by decide) e1 start
  have sup1 := check_evaluation_support oracle (pass1 g 2048 0 (entryState s))
  have inner := block_inner s g bound r sup1
  obtain ⟨q1, qkeep⟩ := pass1_post _ g 2048 0 bound (by decide) e1 sup1
  have q18 : (checkEvaluation oracle (pass1 g 2048 0 (entryState s))).1.getReg .x18 =
      wordAddress (leafBase (2048 * g)) := (qkeep .x18 (by decide) (by decide)).trans e18
  obtain ⟨_, _, _, _, _, smem⟩ := switch_facts _ g q18 (by rw [q1.pc]; rfl)
  have afterP1' : C3State oracle before (checkEvaluation oracle (pass1 g 2048 0 (entryState s))).1
      (2048 * g + 0) (2048 * g + 2048) := by
    simpa only [Nat.add_zero] using afterP1
  have mid := c3_state_mem oracle before _ _ _ _ smem afterP1'
  have afterP3 := pass3_state oracle before _ g 2048 0 bound (by decide) inner.1 mid
  rw [block_eval]
  apply c3_state_mem oracle before _ _ _ _ (set_pc_mem _ _)
  rw [show 2048 * (g + 1) = 2048 * g + 0 + 2048 by omega]
  exact afterP3

theorem blocks_state (oracle : Oracle) (before : Memory) (s : MachineState) (cnt g : Nat) (limit : g + cnt = 8192)
    (r : 0 < cnt → BlockRegs s g) (prev : C3State oracle before s (2048 * g) (2048 * g)) :
    C3State oracle before (checkEvaluation oracle (blocks cnt g s)).1 (2048 * (g + cnt)) (2048 * (g + cnt)) := by
  induction cnt generalizing s g with
  | zero => simpa only [blocks, check_evaluation_pure, Nat.add_zero] using prev
  | succ k ih =>
    simp only [blocks, check_evaluation_bind]
    have valid := r (by omega)
    have next := block_state oracle before s g (by omega) valid prev
    have regs := (block_post s g (by omega) valid (check_evaluation_support oracle (blockTrace g s))).1
    rw [show g + (k + 1) = g + 1 + k by omega]
    exact ih _ (g + 1) (by omega) (fun more => regs (by omega)) next

/-! ### Counting -/

theorem counted_p1 (oracle : Oracle) (s : MachineState) (base : Nat) : RunPublic oracle (p1Trace s base) 3 := by
  unfold p1Trace
  apply run_bind_public _ _ _ 1 2 (run_query_public ..)
  intro t1
  apply run_bind_public _ _ _ 1 1 (run_query_public ..)
  intro t2
  apply run_bind_public _ _ _ 1 0 (run_query_public ..)
  intro t3
  exact run_pure_public ..

theorem counted_pass1 (oracle : Oracle) (g : Nat) (s : MachineState) (cnt j : Nat) :
    RunPublic oracle (pass1 g cnt j s) (3 * cnt) := by
  induction cnt generalizing s j with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [show 3 * (k + 1) = 3 + 3 * k by omega]
    exact run_bind_public _ _ _ 3 _ (counted_p1 ..) (fun _ => ih _ _)

theorem counted_p3 (oracle : Oracle) (g j : Nat) (s : MachineState) : RunPublic oracle (p3Unit g j s) 1 := by
  unfold p3Unit p3Trace
  simp only [bind_assoc, pure_bind]
  apply run_bind_public _ _ _ 1 0 (run_query_public ..)
  intro y
  exact run_pure_public ..

theorem counted_pass3 (oracle : Oracle) (g : Nat) (s : MachineState) (cnt j : Nat) :
    RunPublic oracle (pass3 g cnt j s) cnt := by
  induction cnt generalizing s j with
  | zero => exact run_pure_public ..
  | succ k ih =>
    have h := run_bind_public oracle (p3Unit g j s) (fun mid => pass3 g k (j + 1) mid) 1 k (counted_p3 ..)
      (fun mid => ih mid (j + 1))
    rw [show 1 + k = k + 1 by omega] at h
    exact h

theorem counted_block (oracle : Oracle) (g : Nat) (s : MachineState) : RunPublic oracle (blockTrace g s) 8192 := by
  unfold blockTrace
  apply run_bind_public _ _ _ (3 * 2048) 2048 (counted_pass1 ..)
  intro p1
  apply run_bind_public _ _ _ 2048 0 (counted_pass3 ..)
  intro p3
  exact run_pure_public ..

theorem counted_blocks (oracle : Oracle) (cnt g : Nat) (s : MachineState) :
    RunPublic oracle (blocks cnt g s) (8192 * cnt) := by
  induction cnt generalizing s g with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [show 8192 * (k + 1) = 8192 + 8192 * k by omega]
    exact run_bind_public _ _ _ 8192 _ (counted_block ..) (fun _ => ih _ _)

/-! ### The heap handed to the tree phase -/

theorem c3_parent_content (oracle : Oracle) (before : Memory) (leaves : MachineState)
    (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (inv : C3State oracle before leaves (2 ^ 24) (2 ^ 24))
    (leaf : ∀ i : Index, heap (LENGTH + i.val) = outputDigest (c3Reply oracle before i))
    (original_salts : ∀ i : Index, (window before (leafSalt i.val) : Words 2) = saltWords (salts i)) :
    ParentContent (parentSetup leaves 5) heap salts (2 ^ 24 - 1) := by
  constructor
  · intro n lo hi
    have valid : n - LENGTH < LENGTH := by change n - 2 ^ 24 < 2 ^ 24; change n < 2 * 2 ^ 24 at hi; omega
    let i : Index := ⟨n - LENGTH, valid⟩
    have idx : n = LENGTH + i.val := by change n = 2 ^ 24 + (n - 2 ^ 24); omega
    rw [idx, leaf i]
    unfold nodeDigest
    rw [read_buffer_memory_congr _ leaves (show (parentSetup leaves 5).mem = leaves.mem from rfl)]
    have addr : treeWord (LENGTH + i.val) = leafDest i.val := by
      change 516 + 32 * 2 ^ 24 + 4 * (2 ^ 24 + i.val) = _; unfold leafDest; omega
    rw [addr]
    apply aligned_buffer_eq leaves _ 32 (by decide)
    intro k hk
    have value := congrFun (inv.digests i i.isLt) (⟨k, hk⟩ : Fin 4)
    change memoryView leaves (leafDest i.val + k) = _ at value
    rw [value]
    exact low_digest_word _ (⟨k, hk⟩ : Fin 4)
  · intro i
    unfold nonceBuffer
    rw [read_buffer_memory_congr _ leaves (show (parentSetup leaves 5).mem = leaves.mem from rfl)]
    apply aligned_buffer_eq leaves _ 16 (by decide)
    intro k hk
    have v := (inv.salts i.val i.isLt).trans (original_salts i)
    exact congrFun v (⟨k, hk⟩ : Fin 2)

theorem c3_ready_memory_view (s : MachineState) {bits : Nat} (packed : BitVec bits) :
    memoryView (jumpState (packed_wideReadyState s packed)) = memoryView (readyState s packed) := by
  apply memoryView_congr
  rw [jumpState, set_pc_mem]
  exact packed_wide_ready_state_memory s packed

theorem c3_reference_leaf (oracle : Oracle) (msg : Message) (packed : BitVec (128 * LENGTH)) (i : Index) :
    packedPublicTree oracle msg (splitBlocks 128 LENGTH packed) (LENGTH + i.val) =
      outputDigest (c3Reply oracle (memoryView (jumpState (packed_wideReadyState
        (packedSubmission.initialState .commit msg) packed))) i) := by
  rw [c3_ready_memory_view, packedPublicTree, Hybrid.heap_leaf, c3Reply,
    show leafBase i.val = leafStart i.val + 5 by unfold leafBase leafStart; omega,
    PackedLeaves.wide_ready_messages packedSubmission rfl msg packed i, ready_salts _ packed i]
  rfl

def c3Meaning : PackedLeafMeaning c3Leaves where
  counted oracle s := by
    change RunPublic oracle (blocks 8192 0 (jumpState s)) 67108864
    exact counted_blocks oracle 8192 0 (jumpState s)
  content oracle msg packed := by
    let s := packedSubmission.initialState .commit msg
    let ready := packed_wideReadyState s packed
    have entry : CommitEntry s := ⟨rfl, rfl, rfl, rfl⟩
    have regs := (ready_block_regs s entry packed).1
    have readySalts (i : Index) : (window (memoryView (jumpState ready)) (leafSalt i.val) : Words 2) =
        saltWords (splitBlocks 128 LENGTH packed i) := by
      rw [c3_ready_memory_view]
      exact ready_salts s packed i
    have all := blocks_state oracle (memoryView (jumpState ready)) (jumpState ready) 8192 0 (by decide)
      (fun _ => regs) (by simpa using c3_state_start oracle (jumpState ready))
    exact c3_parent_content oracle (memoryView (jumpState ready)) _ _ _ all
      (c3_reference_leaf oracle msg packed) readySalts

end TwoPermutationPrototype.RV64.C3Leaves
