import CommitGolfCandidate.C3PCommitRun
import CommitGolfCandidate.C3PLeafModel
import CommitGolfCandidate.PairedSaltDraws
import CommitGolfCandidate.TwoPermutationHybridMeaning

/-! # The paired commit under a fixed oracle: memory of one pair

`p1Det C s E` is pass 1 of the pair at message word `E` with the honest compression answers; its
memory is `p1Mem C (memoryView s) E`, the pair's original words with
`z_e, r_e` at `E + 24 .. E + 32` and `q_o, z_o` at `E + 32 .. E + 40`, every answer computed from the
pair's original words. -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.C3Leaves (c3_read_compression compression_write_memory memoryView_congr
  addi_mem)
open CommitGolfCandidate (fixedOracleRun fixed_oracle_run_public fixed_oracle_run_pure checkEvaluation)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000

/-! ### Window algebra -/

theorem window_write_apart {n m : Nat} (M : Memory) (d s : Nat) (ws : Words n)
    (apart : s + m ≤ d ∨ d + n ≤ s) : (window (writeWindow M d ws) s : Words m) = window M s := by
  funext k
  have hk := k.isLt
  simp only [window, writeWindow]
  rw [dif_neg (by omega)]

theorem write_window_at {n : Nat} (M : Memory) (d w : Nat) (ws : Words n) (h : d ≤ w ∧ w < d + n) :
    writeWindow M d ws w = ws ⟨w - d, by omega⟩ := by
  simp only [writeWindow]; rw [dif_pos h]

theorem write_window_off {n : Nat} (M : Memory) (d w : Nat) (ws : Words n) (h : ¬ (d ≤ w ∧ w < d + n)) :
    writeWindow M d ws w = M w := by
  simp only [writeWindow]; rw [dif_neg h]

/-- The `z` input read back from the two 32-byte halves just written. -/
theorem cw_mem (state : MachineState) (dst word : Nat) (reply : BitVec COMPRESSION_OUTPUT_LENGTH)
    (dstBound : dst + 4 ≤ 2 ^ 33) (wordBound : word < 2 ^ 33) :
    memoryView (writeBits state (wordAddress dst) reply) word =
      writeWindow (memoryView state) dst (digestWords reply) word :=
  compression_write_memory state dst word reply dstBound wordBound

theorem window_two_digests (M : Memory) (d : Nat) (lo hi : BitVec COMPRESSION_OUTPUT_LENGTH) :
    (window (writeWindow (writeWindow M (d + 4) (digestWords hi)) d (digestWords lo)) d : Words 8) =
      c3pZWords (digestWords lo) (digestWords hi) := by
  funext k
  have hk := k.isLt
  simp only [window, c3pZWords, writeWindow]
  by_cases low : k.val < 4
  · rw [dif_pos (by omega), dif_pos low]
    congr 1; apply Fin.ext; simp
  · rw [dif_neg (by omega), dif_pos (by omega), dif_neg low]
    congr 1; apply Fin.ext; simp; omega

/-! ### Pass 1 of one pair -/

/-- The six honest pass-1 answers from the pair's original memory `M`. -/
def rE (C : Compression) (M : Memory) (E : Nat) : BitVec COMPRESSION_OUTPUT_LENGTH := C (packWords8 (window M (E + 24)))
def qE (C : Compression) (M : Memory) (E : Nat) : BitVec COMPRESSION_OUTPUT_LENGTH := C (packWords8 (window M E))
def zE (C : Compression) (M : Memory) (E : Nat) : BitVec COMPRESSION_OUTPUT_LENGTH :=
  C (packWords8 (c3pZWords (digestWords (qE C M E)) (digestWords (rE C M E))))
def qO (C : Compression) (M : Memory) (E : Nat) : BitVec COMPRESSION_OUTPUT_LENGTH := C (packWords8 (window M (E + 32)))
def rO (C : Compression) (M : Memory) (E : Nat) : BitVec COMPRESSION_OUTPUT_LENGTH := C (packWords8 (window M (E + 56)))
def zO (C : Compression) (M : Memory) (E : Nat) : BitVec COMPRESSION_OUTPUT_LENGTH :=
  C (packWords8 (c3pZWords (digestWords (qO C M E)) (digestWords (rO C M E))))

/-- The pair's memory after pass 1. -/
def p1Mem (C : Compression) (M : Memory) (E : Nat) : Memory :=
  writeWindow (writeWindow (writeWindow (writeWindow M (E + 28) (digestWords (rE C M E))) (E + 24)
    (digestWords (zE C M E))) (E + 32) (digestWords (qO C M E))) (E + 36) (digestWords (zO C M E))

/-- Pass 1 of one pair with the answers of the fixed compression `C`. -/
def p1Det (C : Compression) (s : MachineState) (E : Nat) : MachineState :=
  let a1 := C (readBuffer (p1s1 s) (8 * (E + 24)) 64)
  let a2 := C (readBuffer (p1s2 s E a1) (8 * E) 64)
  let a3 := C (readBuffer (p1s3 s E a1 a2) (8 * (E + 24)) 64)
  let a4 := C (readBuffer (p1s4 s E a1 a2 a3) (8 * (E + 32)) 64)
  let a5 := C (readBuffer (p1s5 s E a1 a2 a3 a4) (8 * (E + 56)) 64)
  let a6 := C (readBuffer (p1s6 s E a1 a2 a3 a4 a5) (8 * (E + 32)) 64)
  p1w6 s E a1 a2 a3 a4 a5 a6

theorem p1_det_memory (C : Compression) (s : MachineState) (E : Nat) (bound : E + 64 ≤ 2 ^ 33) :
    ∀ w < 2 ^ 33, memoryView (p1Det C s E) w = p1Mem C (memoryView s) E w := by
  let M := memoryView s
  let a1 := C (readBuffer (p1s1 s) (8 * (E + 24)) 64)
  have v1 : memoryView (p1s1 s) = M := memoryView_congr (seg2_facts s 448 32).2.2.1
  have e1 : a1 = rE C M E := by
    show C (readBuffer (p1s1 s) (8 * (E + 24)) 64) = _
    rw [c3_read_compression, v1]; rfl
  let W1 := p1w1 s E a1
  have m1 : ∀ w < 2 ^ 33, memoryView W1 w = writeWindow M (E + 28) (digestWords a1) w := by
    intro w hw
    rw [show W1 = writeBits (p1s1 s) (wordAddress (E + 28)) a1 from rfl,
      cw_mem _ _ _ _ (by omega) hw, v1]
  let a2 := C (readBuffer (p1s2 s E a1) (8 * E) 64)
  have v2 : memoryView (p1s2 s E a1) = memoryView W1 := memoryView_congr (seg2_facts W1 3904 192).2.2.1
  have e2 : a2 = qE C M E := by
    show C (readBuffer (p1s2 s E a1) (8 * E) 64) = _
    rw [c3_read_compression, v2]
    congr 2
    funext k; have hk := k.isLt
    simp only [window]
    rw [m1 _ (by omega), write_window_off _ _ _ _ (by omega)]
  let W2 := p1w2 s E a1 a2
  have m2 : ∀ w < 2 ^ 33, memoryView W2 w =
      writeWindow (writeWindow M (E + 28) (digestWords a1)) (E + 24) (digestWords a2) w := by
    intro w hw
    rw [show W2 = writeBits (p1s2 s E a1) (wordAddress (E + 24)) a2 from rfl,
      cw_mem _ _ _ _ (by omega) hw, v2]
    by_cases inside : E + 24 ≤ w ∧ w < E + 24 + 4
    · rw [write_window_at _ _ _ _ inside, write_window_at _ _ _ _ inside]
    · rw [write_window_off _ _ _ _ inside, write_window_off _ _ _ _ inside, m1 w hw]
  let a3 := C (readBuffer (p1s3 s E a1 a2) (8 * (E + 24)) 64)
  have v3 : memoryView (p1s3 s E a1 a2) = memoryView W2 := memoryView_congr (seg1_facts W2 192).2.1
  have e3 : a3 = zE C M E := by
    show C (readBuffer (p1s3 s E a1 a2) (8 * (E + 24)) 64) = _
    rw [c3_read_compression, v3]
    have w2 : (window (memoryView W2) (E + 24) : Words 8) =
        (window (writeWindow (writeWindow M (E + 28) (digestWords a1)) (E + 24) (digestWords a2)) (E + 24) : Words 8) := by
      funext k; have hk := k.isLt; simp only [window]; rw [m2 _ (by omega)]
    rw [w2, show E + 28 = E + 24 + 4 by omega, window_two_digests, e1, e2]
    rfl
  let W3 := p1w3 s E a1 a2 a3
  have m3 : ∀ w < 2 ^ 33, memoryView W3 w =
      writeWindow (writeWindow (writeWindow M (E + 28) (digestWords a1)) (E + 24) (digestWords a2)) (E + 24)
        (digestWords a3) w := by
    intro w hw
    rw [show W3 = writeBits (p1s3 s E a1 a2) (wordAddress (E + 24)) a3 from rfl, cw_mem _ _ _ _ (by omega) hw, v3]
    by_cases inside : E + 24 ≤ w ∧ w < E + 24 + 4
    · rw [write_window_at _ _ _ _ inside, write_window_at _ _ _ _ inside]
    · rw [write_window_off _ _ _ _ inside, write_window_off _ _ _ _ inside, m2 w hw]
  let a4 := C (readBuffer (p1s4 s E a1 a2 a3) (8 * (E + 32)) 64)
  have v4 : memoryView (p1s4 s E a1 a2 a3) = memoryView W3 := memoryView_congr (seg2_facts W3 64 0).2.2.1
  have e4 : a4 = qO C M E := by
    show C (readBuffer (p1s4 s E a1 a2 a3) (8 * (E + 32)) 64) = _
    rw [c3_read_compression, v4]
    congr 2
    funext k; have hk := k.isLt
    simp only [window]
    rw [m3 _ (by omega), write_window_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
      write_window_off _ _ _ _ (by omega)]
  let W4 := p1w4 s E a1 a2 a3 a4
  have m4 : ∀ w < 2 ^ 33, memoryView W4 w = writeWindow (memoryView W3) (E + 32) (digestWords a4) w := by
    intro w hw
    rw [show W4 = writeBits (p1s4 s E a1 a2 a3) (wordAddress (E + 32)) a4 from rfl, cw_mem _ _ _ _ (by omega) hw, v4]
  let a5 := C (readBuffer (p1s5 s E a1 a2 a3 a4) (8 * (E + 56)) 64)
  have v5 : memoryView (p1s5 s E a1 a2 a3 a4) = memoryView W4 := memoryView_congr (seg2_facts W4 192 3936).2.2.1
  have e5 : a5 = rO C M E := by
    show C (readBuffer (p1s5 s E a1 a2 a3 a4) (8 * (E + 56)) 64) = _
    rw [c3_read_compression, v5]
    congr 2
    funext k; have hk := k.isLt
    simp only [window]
    rw [m4 _ (by omega), write_window_off _ _ _ _ (by omega), m3 _ (by omega), write_window_off _ _ _ _ (by omega),
      write_window_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega)]
  let W5 := p1w5 s E a1 a2 a3 a4 a5
  have m5 : ∀ w < 2 ^ 33, memoryView W5 w = writeWindow (memoryView W4) (E + 36) (digestWords a5) w := by
    intro w hw
    rw [show W5 = writeBits (p1s5 s E a1 a2 a3 a4) (wordAddress (E + 36)) a5 from rfl,
      cw_mem _ _ _ _ (by omega) hw, v5]
  let a6 := C (readBuffer (p1s6 s E a1 a2 a3 a4 a5) (8 * (E + 32)) 64)
  have v6 : memoryView (p1s6 s E a1 a2 a3 a4 a5) = memoryView W5 := memoryView_congr (seg1_facts W5 3904).2.1
  have e6 : a6 = zO C M E := by
    show C (readBuffer (p1s6 s E a1 a2 a3 a4 a5) (8 * (E + 32)) 64) = _
    rw [c3_read_compression, v6]
    have w5 : (window (memoryView W5) (E + 32) : Words 8) =
        (window (writeWindow (writeWindow M (E + 32 + 4) (digestWords a5)) (E + 32) (digestWords a4)) (E + 32) :
          Words 8) := by
      funext k; have hk := k.isLt
      simp only [window]
      rw [m5 _ (by omega)]
      by_cases hi : E + 36 ≤ E + 32 + k.val ∧ E + 32 + k.val < E + 36 + 4
      · rw [write_window_at _ _ _ _ hi, write_window_off _ _ _ _ (by omega), write_window_at _ _ _ _ (by omega)]
      · rw [write_window_off _ _ _ _ hi, m4 _ (by omega), write_window_at _ _ _ _ (by omega),
          write_window_at _ _ _ _ (by omega)]
    rw [w5, window_two_digests, e4, e5]
    rfl
  intro w hw
  show memoryView (writeBits (p1s6 s E a1 a2 a3 a4 a5) (wordAddress (E + 36)) a6) w = _
  rw [cw_mem _ _ _ _ (by omega) hw, v6]
  unfold p1Mem
  by_cases h36 : E + 36 ≤ w ∧ w < E + 36 + 4
  · rw [write_window_at _ _ _ _ h36, write_window_at _ _ _ _ h36, e6]
  · rw [write_window_off _ _ _ _ h36, write_window_off _ _ _ _ h36, m5 w hw, write_window_off _ _ _ _ h36, m4 w hw]
    by_cases h32 : E + 32 ≤ w ∧ w < E + 32 + 4
    · rw [write_window_at _ _ _ _ h32, write_window_at _ _ _ _ h32, e4]
    · rw [write_window_off _ _ _ _ h32, write_window_off _ _ _ _ h32, m3 w hw]
      by_cases h24 : E + 24 ≤ w ∧ w < E + 24 + 4
      · rw [write_window_at _ _ _ _ h24, write_window_at _ _ _ _ h24, e3]
      · rw [write_window_off _ _ _ _ h24, write_window_off _ _ _ _ h24, write_window_off _ _ _ _ h24]
        by_cases h28 : E + 28 ≤ w ∧ w < E + 28 + 4
        · rw [write_window_at _ _ _ _ h28, write_window_at _ _ _ _ h28, e1]
        · rw [write_window_off _ _ _ _ h28, write_window_off _ _ _ _ h28]

/-! ### The leaf phase under a fixed oracle -/

/-- A per-ordinal deterministic step, iterated (generic, so no heavy equation lemmas). -/
def iterC (f : Nat → MachineState → MachineState) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n + 1, p, s => iterC f n (p + 1) (f p s)

theorem iter_c_zero (f : Nat → MachineState → MachineState) (p : Nat) (s : MachineState) : iterC f 0 p s = s := rfl
theorem iter_c_succ (f : Nat → MachineState → MachineState) (n p : Nat) (s : MachineState) :
    iterC f (n + 1) p s = iterC f n (p + 1) (f p s) := rfl

/-- A per-ordinal step with one draw each, folded over a list of draws. -/
def foldC (f : Nat → MachineState → BitVec 256 → MachineState) : List (BitVec 256) → Nat → MachineState → MachineState
  | [], _, s => s
  | w :: ws, p, s => foldC f ws (p + 1) (f p s w)

theorem fold_c_nil (f : Nat → MachineState → BitVec 256 → MachineState) (p : Nat) (s : MachineState) :
    foldC f [] p s = s := rfl
theorem fold_c_cons (f : Nat → MachineState → BitVec 256 → MachineState) (w : BitVec 256) (ws : List (BitVec 256))
    (p : Nat) (s : MachineState) : foldC f (w :: ws) p s = foldC f ws (p + 1) (f p s w) := rfl

theorem p1_fixed (oracle : Oracle) {α : Type} (s : MachineState) (E : Nat) (k : MachineState → OracleComp World α) :
    fixedOracleRun oracle (p1PairTrace s E >>= k) = fixedOracleRun oracle (k (p1Det oracle.compression s E)) := by
  simp only [p1PairTrace, bind_assoc, pure_bind]
  rw [fixed_oracle_run_public, fixed_oracle_run_public, fixed_oracle_run_public, fixed_oracle_run_public,
    fixed_oracle_run_public, fixed_oracle_run_public]
  rfl

def p3Det (P : Sampling.Block → Sampling.Block) (s : MachineState) (E D : Nat) : MachineState :=
  let y1 := P (packBuffer (window (memoryView (p3a s)) (E + 7)))
  let y2 := P (packBuffer (window (memoryView (p3b s D y1)) (E + 32)))
  p3w2 s D y1 y2

theorem p3_fixed (oracle : Oracle) {α : Type} (s : MachineState) (E D : Nat) (k : MachineState → OracleComp World α) :
    fixedOracleRun oracle (p3PairTrace s E D >>= k) =
      fixedOracleRun oracle (k (p3Det (fun x => oracle.permutation x) s E D)) := by
  simp only [p3PairTrace, bind_assoc, pure_bind]
  rw [fixed_oracle_run_public, fixed_oracle_run_public]
  rfl

def pass1Det (C : Compression) (E : Nat) : Nat → Nat → MachineState → MachineState :=
  iterC (fun p s => p1Det C s (E + 64 * p))

def pass2Det (E : Nat) : List (BitVec 256) → Nat → MachineState → MachineState :=
  foldC (fun p s w => p2After s (E + 64 * p) w)

def pass3Det (P : Sampling.Block → Sampling.Block) (E D : Nat) : Nat → Nat → MachineState → MachineState :=
  iterC (fun p s => p3Det P s (E + 64 * p) (D + 50 * p))

theorem pass1_fixed (oracle : Oracle) {α : Type} (E : Nat) :
    ∀ n p s (k : MachineState → OracleComp World α),
      fixedOracleRun oracle (pass1Loop E n p s >>= k) = fixedOracleRun oracle (k (pass1Det oracle.compression E n p s)) := by
  intro n
  induction n with
  | zero => intro p s k; simp only [pass1Loop, pure_bind, pass1Det, iter_c_zero]
  | succ n ih =>
    intro p s k
    simp only [pass1Loop, bind_assoc]
    rw [p1_fixed, ih]
    rfl

theorem pass3_fixed (oracle : Oracle) {α : Type} (E D : Nat) :
    ∀ n p s (k : MachineState → OracleComp World α),
      fixedOracleRun oracle (pass3Loop E D n p s >>= k) =
        fixedOracleRun oracle (k (pass3Det (fun x => oracle.permutation x) E D n p s)) := by
  intro n
  induction n with
  | zero => intro p s k; simp only [pass3Loop, pure_bind, pass3Det, iter_c_zero]
  | succ n ih =>
    intro p s k
    simp only [pass3Loop, bind_assoc]
    rw [p3_fixed, ih]
    rfl

/-- `n` draws of 32 bytes. -/
def drawsN (n : Nat) : ProbComp (List (BitVec 256)) := (List.range n).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256)))

theorem pass2_fixed (oracle : Oracle) {α : Type} (E : Nat) :
    ∀ n p s (k : MachineState → OracleComp World α),
      fixedOracleRun oracle (pass2Loop E n p s >>= k) =
        ((List.range n).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256))) >>= fun ws =>
          fixedOracleRun oracle (k (pass2Det E ws p s))) := by
  intro n
  induction n with
  | zero => intro p s k; simp [pass2Loop, pass2Det, fold_c_nil]
  | succ n ih =>
    intro p s k
    simp only [pass2Loop, bind_assoc]
    rw [fixed_oracle_run_coins_bind]
    simp only [ih]
    rw [List.range_succ_eq_map, List.mapM_cons]
    simp only [bind_assoc, List.mapM_map, Function.comp_def]
    apply bind_congr
    intro w
    apply bind_congr
    intro ws
    simp only [pure_bind, pass2Det, fold_c_cons]

/-- One block under a fixed oracle, given its 1,024 draws. -/
def blockDet (oracle : Oracle) (g : Nat) (s : MachineState) (ws : List (BitVec 256)) : MachineState :=
  runOpsC (pass3Det (fun x => oracle.permutation x) (E0 g) (D0 g) 1024 0
    (runOpsC (pass2Det (E0 g) ws 0
      (runOpsC (pass1Det oracle.compression (E0 g) 1024 0 (runOpsC s prologueOps)) p2SetupOps)) p3SetupOps))
    epilogueOps

theorem block_fixed (oracle : Oracle) {α : Type} (g : Nat) (s : MachineState) (k : MachineState → OracleComp World α) :
    fixedOracleRun oracle (blockTrace g s >>= k) =
      ((List.range 1024).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256))) >>= fun ws =>
        fixedOracleRun oracle (k (blockDet oracle g s ws))) := by
  simp only [blockTrace, bind_assoc, pure_bind]
  rw [pass1_fixed, pass2_fixed]
  apply bind_congr
  intro ws
  rw [pass3_fixed]
  rfl

/-- Blocks folded over their draws (generic over the per-block step). -/
def foldB (f : Nat → MachineState → List (BitVec 256) → MachineState) :
    List (List (BitVec 256)) → Nat → MachineState → MachineState
  | [], _, s => s
  | ws :: wss, g, s => foldB f wss (g + 1) (f g s ws)

theorem fold_b_nil (f : Nat → MachineState → List (BitVec 256) → MachineState) (g : Nat) (s : MachineState) :
    foldB f [] g s = s := rfl
theorem fold_b_cons (f : Nat → MachineState → List (BitVec 256) → MachineState) (ws : List (BitVec 256))
    (wss : List (List (BitVec 256))) (g : Nat) (s : MachineState) :
    foldB f (ws :: wss) g s = foldB f wss (g + 1) (f g s ws) := rfl

def leafDet (oracle : Oracle) : List (List (BitVec 256)) → Nat → MachineState → MachineState :=
  foldB (fun g s ws => (blockDet oracle g s ws).setPC (latchPC g))

theorem leaf_fixed (oracle : Oracle) {α : Type} :
    ∀ n g s (k : MachineState → OracleComp World α),
      fixedOracleRun oracle (leafPhaseP n g s >>= k) =
        ((List.range n).mapM (fun _ => (List.range 1024).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256)))) >>=
          fun wss => fixedOracleRun oracle (k (leafDet oracle wss g s))) := by
  intro n
  induction n with
  | zero => intro g s k; simp [leafPhaseP, leafDet, fold_b_nil]
  | succ n ih =>
    intro g s k
    simp only [leafPhaseP, bind_assoc]
    rw [block_fixed]
    simp only [ih]
    rw [List.range_succ_eq_map (n := n), List.mapM_cons]
    simp only [bind_assoc, List.mapM_map, Function.comp_def]
    apply bind_congr
    intro ws
    apply bind_congr
    intro wss
    simp only [pure_bind, leafDet, fold_b_cons]

theorem fixed_public_bind (oracle : Oracle) {α β : Type} (p : OracleComp World α) (c : Nat)
    (hpub : RunPublic oracle p c) (k : α → OracleComp World β) :
    fixedOracleRun oracle (p >>= k) = fixedOracleRun oracle (k (checkEvaluation oracle p).1) := by
  rw [CommitGolfCandidate.fixed_oracle_run_bind]
  have h : fixedOracleRun oracle p = pure (checkEvaluation oracle p).1 := by
    unfold fixedOracleRun RunPublic at *
    rw [hpub]; rfl
  rw [h, pure_bind]

/-- The whole commit under a fixed oracle: the draws, then one deterministic end state. -/
theorem commit_fixed (oracle : Oracle) (initial : MachineState) :
    fixedOracleRun oracle (commitTraceP initial) =
      ((List.range 8192).mapM (fun _ => (List.range 1024).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256)))) >>=
        fun wss => pure (⟨.success, rootPrefix (checkEvaluation oracle
          (hybridParentPhase (exitState (leafDet oracle wss 0 (firstState initial))))).1 10, 1266820207, 83886079⟩ :
            Execution)) := by
  unfold commitTraceP
  rw [leaf_fixed]
  apply bind_congr
  intro wss
  rw [fixed_public_bind oracle _ _ (counted_hybrid_phase oracle _), fixed_oracle_run_pure]

end TwoPermutationPrototype.RV64.C3P
