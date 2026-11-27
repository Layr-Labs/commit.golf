import CommitGolfCandidate.PentaGroupedKeySetup
import CommitGolfCandidate.QuadCommitMeaning
import CommitGolfCandidate.TwoPermutationPackedLeafInput
import CommitGolfCandidate.TwoPermutationPentaSpec

/-! End-to-end penta counter-mode commit proof:
prologue (17 steps, 20 cycles, RANDOM 24B key) ->
16,777,215-leaf loop scan (`4097 * 4095`, 184,930,385 steps, 35,082,611 calls, 430,508,662 cycles) ->
trailing leaf `2^24 - 1` (11 steps, 3 calls, 32 cycles) ->
level-0 ragged zeroing (16 steps, 16 cycles) ->
levels 1..10 (12,583,425 steps, 4,194,307 calls, 41,943,574 cycles) ->
root node + root copy + HALT (16 steps, 1 call, 23 cycles).
Total: 197,513,870 steps, 39,276,922 oracle calls, 472,452,327 cycles. -/
namespace TwoPermutationPrototype.PentaGrouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Quad.Commit
open TwoPermutationPrototype.Quad.Commit.Penta
open TwoPermutationPrototype.RV64.PackedLeaves (wide_message_byte)
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000

private theorem written_words {w : Nat} (s : MachineState) (a : Nat) (v : BitVec w)
    (off cnt : Nat) (size : off + cnt ≤ (w + 7) / 8) (bound : (w + 7) / 8 ≤ 2^64) :
    readBuffer (writeBits s (BitVec.ofNat 64 a) v) (a + off) cnt =
      v.extractLsb' (8 * off) (8 * cnt) := by
  apply read_serialized_slice
  intro j hj
  simpa only [BitVec.ofNat_add, Nat.add_assoc, BitVec.add_assoc] using
    write_bits_byte s (BitVec.ofNat 64 a) v (off + j) (by omega) bound

private theorem high_word_zero (opening checker : Image) (msg : Message) (w : Nat)
    (lo : 4294971392 ≤ 8 * w) (hi : w + 1 ≤ 2^33) :
    memoryView ((submission opening checker).initialState .commit msg) w = 0 := by
  let s := submission opening checker
  change (s.initialState .commit msg).getMem (BitVec.ofNat 64 (8 * w)) = _
  rw [initial_input_word s .commit msg (8 * w) (by omega)]
  have empty (j : Nat) (hj : j < 8) : inputByte s .commit msg (8 * w + j) = 0 := by
    have gone : ¬(4096 ≤ 8 * w + j ∧ 8 * w + j < 4096 + LENGTH * (LEAF_SIZE / 8)) := by
      change ¬(_ ∧ _ < 4096 + 16777216 * 256); omega
    have mb : s.layout.message = 4096 := rfl
    have d : (s.image .commit).data = [] := rfl
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, messageBuffer, mb, gone, decide_false,
      Bool.false_eq_true, ite_false, List.find?_nil, d]; simp
  rw [Finset.sum_eq_zero (fun j hj => by rw [empty j (Finset.mem_range.mp hj)]; simp)]; rfl

theorem seed_memory (s : MachineState) (k : Key) :
    (keyReady s k).mem = (writeBits s (BitVec.ofNat 64 (8 * keyWord + 8)) k).mem := by
  have adr : wordAddress (keyWord + 1) = BitVec.ofNat 64 (8 * keyWord + 8) := by decide
  change (writeBits (keySetup s) (wordAddress (keyWord + 1)) k).mem = _
  rw [adr]
  exact write_bits_memory_congr (keySetup s) s _ k rfl

theorem initially_good (opening checker : Image) (o : Oracle) (k : Key) (msg : Message) :
    Good o k msg (memoryView (keyReady ((submission opening checker).initialState .commit msg) k)) 0 := by
  let s := (submission opening checker).initialState .commit msg
  let st := keyReady s k
  have same := seed_memory s k
  have outside (w : Nat) (hi : w + 1 ≤ 2^33) (disjoint : w < keyWord + 1 ∨ keyWord + 4 ≤ w) :
      memoryView st w = memoryView s w := by
    rw [← read_word, read_buffer_memory_congr _ _ same,
      write_bits_read_outside _ k _ _ _ (by decide) (by omega)
        (by dsimp [Key]; rcases disjoint with h | h; left; omega; right; omega),
      read_word]
  constructor
  · intro i _; funext j
    have hi : i.val < 16777216 := i.isLt
    have hj := j.isLt
    rw [show window (memoryView st) (msgWord i.val) j = memoryView st (msgWord i.val + j.val) from rfl,
      outside _ (by unfold msgWord; omega) (Or.inl (by unfold msgWord keyWord saltWord; omega)), ← read_word]
    have atByte (l : Nat) (hl : l < 8) :
        s.getByte (BitVec.ofNat 64 (8 * (msgWord i.val + j.val) + l)) = (msg i).extractLsb' (8 * (8 * j.val + l)) 8 := by
      rw [show 8 * (msgWord i.val + j.val) + l = 4096 + 256 * i.val + (8 * j.val + l) by unfold msgWord; omega]
      exact wide_message_byte (submission opening checker) rfl msg i _ (by omega)
    simpa only [messageWords, ← Nat.mul_assoc] using
      read_serialized_slice s (msg i) (8 * (msgWord i.val + j.val)) (8 * j.val) 8 atByte
  · intro _ h; omega
  · intro l g hl hg t ht
    have := Quad.Commit.prefix_words_le l
    have below := group_below_salts l g (by omega) hg 0
    have above := trapdoor_below_levels l g (by omega)
    rw [outside _ (by unfold saltWord at below; omega) (Or.inl (by unfold keyWord; omega))]
    exact high_word_zero opening checker msg _ (by omega) (by unfold saltWord at below; omega)
  · intro j lo hi
    by_cases inKey : j < 4
    · rw [← read_word, read_buffer_memory_congr _ _ same, show 8 * (keyWord + j) = (8 * keyWord + 8) + 8 * (j - 1) by omega,
        written_words _ _ k (8 * (j - 1)) 8 (by dsimp [Key]; omega) (by decide)]
      simp only [keyBlock, ← Nat.mul_assoc]
    · rw [outside _ (by unfold keyWord saltWord; omega) (Or.inr (by omega)),
        high_word_zero opening checker msg _ (by unfold keyWord saltWord; omega) (by unfold keyWord saltWord; omega)]
      apply BitVec.eq_of_getLsbD_eq; intro n hn
      simp [keyBlock, hn, show 192 ≤ 64 * (j - 1) + n by omega]
  · intro i _ nz; exact (nz rfl).elim

def fixedLeaf (o : Oracle) (s : MachineState) (i : Nat) :=
  ((plan i).foldl (fixedStep o) s).setPC (startPC (i + 1))

def fixedScan (o : Oracle) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n + 1, i, s => fixedScan o n (i + 1) (fixedLeaf o s i)

theorem fixed_leaf_run (o : Oracle) (s : MachineState) (i : Nat) :
    o.run (stepTrace s i) = pure (fixedLeaf o s i, opCalls (plan i)) := by
  rw [stepTrace, oracle_run_bind, fixed_ops, pure_bind]; simp [oracle_run_pure, fixedLeaf]

theorem fixed_leaf_supported (o : Oracle) (s : MachineState) (i : Nat) :
    fixedLeaf o s i ∈ support (stepTrace s i) := by
  apply writer_support (o.world.withAddCost Oracle.callCost) _ (fixedLeaf o s i, opCalls (plan i))
  change (_, _) ∈ support (o.run (stepTrace s i))
  rw [fixed_leaf_run]; simp

theorem fixed_scan_run (o : Oracle) (n i : Nat) (s : MachineState) (bound : i + n ≤ N_loop) :
    o.run (scan n i s) = pure (fixedScan o n i s, Q (i + n) - Q i) := by
  induction n generalizing s i with
  | zero => simp [scan, fixedScan, oracle_run_pure]
  | succ n ih =>
    have h := cumul i (by omega)
    have m := monotone_counts (i + 1) n (by omega)
    rw [scan, oracle_run_bind, fixed_leaf_run, pure_bind]
    dsimp only
    rw [ih (i + 1) _ (by omega)]
    simp only [fixedScan, pure_bind]
    apply congrArg pure
    apply congrArg (Prod.mk _)
    change opCalls (plan i) + (Q ((i + 1) + n) - Q (i + 1)) = Q (i + (n + 1)) - Q i
    rw [show i + (n + 1) = (i + 1) + n by omega]; omega

theorem scan_content (o : Oracle) (k : Key) (msg : Message) (n i : Nat) (s : MachineState)
    (bound : i + n ≤ N_loop) (r : Live s i) (good : Good o k msg (memoryView s) i)
    (saved : Prefetched s.getReg (memoryView s) i) :
    Good o k msg (memoryView (fixedScan o n i s)) (i + n) := by
  induction n generalizing i s with
  | zero => exact good
  | succ n ih =>
    have hi : i < N_loop := by dsimp [N_loop] at bound ⊢; omega
    let idx : Index := ⟨i, by dsimp [N_loop] at hi; change i < LENGTH; unfold LENGTH LOG_LENGTH; omega⟩
    obtain ⟨next, carry⟩ := fixed_packet_good o k msg s idx hi r.toPacketRegs good saved
    have live := step_live s i hi r _ (fixed_leaf_supported o s i)
    exact (show i + (n + 1) = (i + 1) + n by omega) ▸ ih (i + 1) _ (by omega) live next (by
      intro a b j
      simpa only [fixedLeaf, MachineState.getReg_setPC, memoryView, MachineState.getMem_setPC] using carry a b j)

/-! ### Full commit trace and execution theorem -/

attribute [local irreducible] execute scan runOps levels rootPrefix writeBits
  checkEvaluation readBuffer fixedScan

def commitTrace (ready : MachineState) : OracleComp World MachineState := do
  let mid ← scan N_loop 0 ready
  let leaves ← runOps trailingPlan mid
  let tops ← levels (zeroed leaves 32 16 16)
  let reply ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView tops) (pentaGroupWord 15 0))))))
  return rootPrefix (writeBits (rootNode tops 4) (wordAddress (heapWord 1)) reply) 10

theorem counted_levels (o : Oracle) (s : MachineState) :
    RunPublic o (levels s) 4250170 := by
  unfold levels
  rw [show 4250170 = pentaCount (0 + 1) + (pentaCount (1 + 1) + (pentaCount (2 + 1) + (pentaCount (3 + 1) + (pentaCount (4 + 1) + (pentaCount (5 + 1) + (pentaCount (6 + 1) + (pentaCount (7 + 1) + (pentaCount (8 + 1) + (pentaCount (9 + 1) + (pentaCount (10 + 1) + (pentaCount (11 + 1) + (pentaCount (12 + 1) + (pentaCount (13 + 1) + (pentaCount (14 + 1) + 0)))))))))))))) by decide]
  refine run_bind_public _ _ _ (pentaCount (0 + 1)) _ (Penta.counted_level Penta.layout1 ..) fun s1 => ?_
  refine run_bind_public _ _ _ (pentaCount (1 + 1)) _ (Penta.counted_level Penta.layout2 ..) fun s2 => ?_
  refine run_bind_public _ _ _ (pentaCount (2 + 1)) _ (Penta.counted_level Penta.layout3 ..) fun s3 => ?_
  refine run_bind_public _ _ _ (pentaCount (3 + 1)) _ (Penta.counted_level Penta.layout4 ..) fun s4 => ?_
  refine run_bind_public _ _ _ (pentaCount (4 + 1)) _ (Penta.counted_level Penta.layout5 ..) fun s5 => ?_
  refine run_bind_public _ _ _ (pentaCount (5 + 1)) _ (Penta.counted_level Penta.layout6 ..) fun s6 => ?_
  refine run_bind_public _ _ _ (pentaCount (6 + 1)) _ (Penta.counted_level Penta.layout7 ..) fun s7 => ?_
  refine run_bind_public _ _ _ (pentaCount (7 + 1)) _ (Penta.counted_level Penta.layout8 ..) fun s8 => ?_
  refine run_bind_public _ _ _ (pentaCount (8 + 1)) _ (Penta.counted_level Penta.layout9 ..) fun s9 => ?_
  refine run_bind_public _ _ _ (pentaCount (9 + 1)) _ (Penta.counted_level Penta.layout10 ..) fun s10 => ?_
  refine run_bind_public _ _ _ (pentaCount (10 + 1)) _ (Penta.counted_level Penta.layout11 ..) fun s11 => ?_
  refine run_bind_public _ _ _ (pentaCount (11 + 1)) _ (Penta.counted_level Penta.layout12 ..) fun s12 => ?_
  refine run_bind_public _ _ _ (pentaCount (12 + 1)) _ (Penta.counted_level Penta.layout13 ..) fun s13 => ?_
  refine run_bind_public _ _ _ (pentaCount (13 + 1)) _ (Penta.counted_level Penta.layout14 ..) fun s14 => ?_
  exact Penta.counted_level Penta.layout15 ..

def fixedLeaves (o : Oracle) (ready : MachineState) : MachineState :=
  trailingPlan.foldl (fixedStep o) (fixedScan o N_loop 0 ready)

def fixedCommitState (o : Oracle) (ready : MachineState) : MachineState :=
  let leaves := fixedLeaves o ready
  let tops := (checkEvaluation o (levels (zeroed leaves 32 16 16))).1
  let reply := o.permutation (packBuffer (window (memoryView tops) (pentaGroupWord 15 0)))
  rootPrefix (writeBits (rootNode tops 4) (wordAddress (heapWord 1)) reply) 10

theorem fixed_commit_trace_run (o : Oracle) (ready : MachineState) :
    o.run (commitTrace ready) = pure (fixedCommitState o ready, 39332785) := by
  obtain ⟨_, qN, _, _, q0, _⟩ := scan_counts
  have callsTrail : opCalls trailingPlan = 3 := rfl
  unfold commitTrace
  rw [oracle_run_bind, fixed_scan_run o N_loop 0 ready (by omega), pure_bind]
  dsimp only
  rw [oracle_run_bind, fixed_ops o _ trailingPlan, pure_bind]
  dsimp only
  rw [oracle_run_bind, counted_levels o _, pure_bind]
  dsimp only
  rw [oracle_run_public_bind]
  simp only [oracle_run_pure, pure_bind, fixedCommitState, fixedLeaves, Nat.zero_add, qN, q0, callsTrail, Oracle.answer]
  apply congrArg pure
  apply congrArg (Prod.mk _)
  omega

attribute [local irreducible] commitTrace fixedLeaves fixedCommitState

theorem execute_after_key (ready : MachineState) (r : Live ready 0) (fuel : Nat) :
    execute image (197681877 + fuel) ready true =
      (do let final ← commitTrace ready
          return ⟨.success, final, 473011372, 39332785⟩) := by
  obtain ⟨sN, qN, cN, s0, q0, c0⟩ := scan_counts
  have splitFuel : 197681877 + fuel = (S (0 + N_loop) - S 0) + (11 + (16 + (12751449 + (5 + (11 + fuel))))) := by
    simp only [Nat.zero_add, sN, s0]; omega
  rw [splitFuel, run_scan N_loop 0 ready (by omega) r]
  simp only [commitTrace, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro mid hitMid
  have rMid : Live mid N_loop := by simpa only [Nat.zero_add] using scan_post N_loop 0 ready mid (by omega) r hitMid
  rw [trailing_execute mid rMid]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves hitLeaves
  obtain ⟨leafPC, leafDest, x5, x11, x13, x8, x9⟩ := trailing_post mid leaves rMid hitLeaves
  rw [zero_run 45201 32 16 leaf_zero_segment (by decide) leaves (leafWord (2^24 - 1)) leafPC leafDest
    (by decide) (by decide) (by decide)]
  simp only [bind_assoc, pure_bind]
  let z := zeroed leaves 32 16 16
  have regZ (reg : Reg) : z.getReg reg = leaves.getReg reg := zeroed_reg leaves 32 16 16 le_rfl reg
  have entry : Entry 45217 z := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [zeroed_pc leaves 32 16 16 le_rfl, leafPC]; rfl
    · rw [regZ, x9]
    · rw [regZ, x8]
    · rw [regZ, x5]
    · rw [regZ, x11]
    · rw [regZ, x13]
  rw [levels_run z entry]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro tops hitTops
  have entryT : Entry 214588 tops := levels_post z entry hitTops
  rw [execute_root_node tops entryT.pc entryT.heap entryT.selector entryT.size entryT.primitive]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro reply
  let w := writeBits (rootNode tops 4) (wordAddress (heapWord 1)) reply
  have wpc : w.pc = 862468 := by
    change (writeBits _ _ _).pc = _
    rw [written_pc]
    simp only [rootNode, rootNodeOps, List.take, List.foldl, execInstrBr, MachineState.setPC, entryT.pc]; rfl
  have wheap : w.getReg .x9 = 4294971424 := by
    change (writeBits _ _ _).getReg .x9 = _
    rw [CommitGolfCandidate.writeBits_register, root_node_keep tops .x9 (by decide) (by decide), entryT.heap]
  have wout : w.getReg .x8 = 4294971392 := by
    change (writeBits _ _ _).getReg .x8 = _
    rw [CommitGolfCandidate.writeBits_register, root_node_keep tops .x8 (by decide) (by decide), entryT.out]
  rw [execute_root w wpc wheap wout]
  simp only [pure_bind, Execution.charge, Nat.zero_add, cN, c0, qN, q0]
  apply congrArg pure
  congr 1

attribute [local irreducible] keyReady

private theorem execute_commit_gen (initial : MachineState) (entry : CommitEntry initial) (fuel : Nat) :
    execute image (197681894 + fuel) initial true =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let final ← commitTrace (keyReady initial k)
          return ⟨.success, final, 473011392, 39332785⟩) := by
  have clock : 197681894 + fuel = 17 + (197681877 + fuel) := by omega
  rw [clock, prologue_run initial entry]
  apply bind_congr; intro k
  rw [execute_after_key (keyReady initial k) (ready_live initial entry k) fuel]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro final
  have cEq : 20 + 473011372 = 473011392 := by omega
  have qEq : 0 + 39332785 = 39332785 := by omega
  show pure ((⟨.success, final, 473011372, 39332785⟩ : Execution).charge 20 0) = _
  simp only [Execution.charge, cEq, qEq]

private theorem program_commit_run (program : Submission) (code : program.image .commit = image)
    (enough : 197681894 ≤ program.steps .commit) (msg : Message)
    (entry : CommitEntry (program.initialState .commit msg)) :
    program.run .commit msg =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let final ← commitTrace (keyReady (program.initialState .commit msg) k)
          return ⟨.success, final, 473011392, 39332785⟩) := by
  change execute (program.image .commit) (program.steps .commit) (program.initialState .commit msg) true = _
  rw [code, show program.steps .commit = 197681894 + (program.steps .commit - 197681894) by omega]
  exact execute_commit_gen _ entry _

theorem execute_commit_full (opening checker : Image) (msg : Message) :
    (submission opening checker).run .commit msg =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let final ← commitTrace (keyReady ((submission opening checker).initialState .commit msg) k)
          return ⟨.success, final, 473011392, 39332785⟩) :=
  program_commit_run (submission opening checker) rfl (by change 197681894 ≤ 1073807360; omega) msg
    (abi_entry _ (abi opening checker) msg)

theorem commit_resources (opening checker : Image) (msg : Message) (result : Execution)
    (reached : result ∈ support ((submission opening checker).run .commit msg)) :
    result.exit = .success ∧ result.cycles = 473011392 ∧ result.oracleCalls ≤ COMMIT_BUDGET := by
  rw [execute_commit_full] at reached
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨k, _, final, _, rfl⟩ := reached
  refine ⟨rfl, rfl, ?_⟩
  change 39332785 ≤ COMMIT_BUDGET
  unfold COMMIT_BUDGET LENGTH LOG_LENGTH
  omega

def tapeOf (m : Memory) : CompleteSaltTape :=
  fun i => m (saltWord i.val + 1) ++ m (saltWord i.val)

private theorem tape_of_extract (m : Memory) (i : Index) (t : Fin 2) :
    m (saltWord i.val + t.val) = (tapeOf m i).extractLsb' (64 * t.val) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  fin_cases t
  · dsimp only [tapeOf]
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp [hb]
  · dsimp only [tapeOf]
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp [hb, show ¬(64 + b < 64) by omega]

private theorem key_from_salts {n : Nat} (td : BitVec n) (k : Key)
    (h0 : quadTrapdoorSalt td ⟨0, by decide⟩ = (k.extractLsb' 0 64) ++ td.extractLsb' (8 * QUAD_SALT_BASE) 64)
    (h1 : quadTrapdoorSalt td ⟨1, by decide⟩ = (k.extractLsb' 128 64) ++ (k.extractLsb' 64 64)) :
    td.extractLsb' (8 * (QUAD_SALT_BASE + 8)) 192 = k := by
  apply BitVec.eq_of_getLsbD_eq; intro bit hbit
  by_cases b0 : bit < 64
  · have e := congrArg (fun w : BitVec 128 => w.getLsbD (64 + bit)) h0
    simp only [quadTrapdoorSalt, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at e
    simp only [show decide (64 + bit < 128) = true from decide_eq_true (by omega), Bool.true_and,
      show ¬(64 + bit < 64) by omega, ↓reduceIte,
      show 64 + bit - 64 = bit by omega, show decide (bit < 64) = true from decide_eq_true b0,
      Nat.zero_add, Nat.mul_zero, Nat.add_zero] at e
    simp only [BitVec.getLsbD_extractLsb', show decide (bit < 192) = true from decide_eq_true hbit, Bool.true_and]
    simpa [show 8 * (QUAD_SALT_BASE + 8) + bit = 8 * QUAD_SALT_BASE + (64 + bit) by omega] using e
  · by_cases b1 : bit < 128
    · have e := congrArg (fun w : BitVec 128 => w.getLsbD (bit - 64)) h1
      simp only [quadTrapdoorSalt, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at e
      simp only [show decide (bit - 64 < 128) = true from decide_eq_true (by omega), Bool.true_and,
        show bit - 64 < 64 by omega, ↓reduceIte,
        show decide (bit - 64 < 64) = true from decide_eq_true (by omega)] at e
      simp only [BitVec.getLsbD_extractLsb', show decide (bit < 192) = true from decide_eq_true hbit, Bool.true_and]
      simpa [show 8 * (QUAD_SALT_BASE + 8) + bit = 8 * (QUAD_SALT_BASE + 16 * 1) + (bit - 64) by omega,
        show 64 + (bit - 64) = bit by omega] using e
    · have e := congrArg (fun w : BitVec 128 => w.getLsbD (bit - 64)) h1
      simp only [quadTrapdoorSalt, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] at e
      simp only [show decide (bit - 64 < 128) = true from decide_eq_true (by omega), Bool.true_and,
        show ¬(bit - 64 < 64) by omega, ↓reduceIte,
        show decide (bit - 64 - 64 < 64) = true from decide_eq_true (by omega)] at e
      simp only [BitVec.getLsbD_extractLsb', show decide (bit < 192) = true from decide_eq_true hbit, Bool.true_and]
      simpa [show 8 * (QUAD_SALT_BASE + 8) + bit = 8 * (QUAD_SALT_BASE + 16 * 1) + (bit - 64) by omega,
        show 128 + (bit - 64 - 64) = bit by omega] using e

/-- What the counter-mode penta commit program delivers to the opening program. -/
structure PentaCounterCommitTranscript (s : Submission) where
  trapdoor : Oracle → Message → Key → BitVec (8 * s.sizes.trapdoor)
  distribution : ∀ oracle message,
    fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let k ← $ᵗ Key
          pure (pentaPublicNodes oracle message (salts oracle.permutation k) PENTA_LEVELS 0,
            trapdoor oracle message k))
  key : ∀ oracle message k,
    (trapdoor oracle message k).extractLsb' (8 * (QUAD_SALT_BASE + 8)) 192 = k
  slot : ∀ oracle message k level g (t : Fin 5), level < PENTA_LEVELS → g < pentaCount (level + 1) →
    pentaTrapdoorSlot (trapdoor oracle message k) level g t.val =
      pentaGroup (pentaFunction oracle.permutation) (quadPublicLeaves oracle message (salts oracle.permutation k)) level g t

def commitOutput (opening checker : Image) (o : Oracle) (msg : Message) (k : Key) : Execution :=
  ⟨.success, fixedCommitState o (keyReady ((submission opening checker).initialState .commit msg) k), 473011392, 39332785⟩

theorem commit_physical_results (opening checker : Image) (o : Oracle) (msg : Message) (k : Key) :
    let out := (submission opening checker).readCommit (commitOutput opening checker o msg k)
    out.1 = pentaPublicNodes o msg (salts o.permutation k) PENTA_LEVELS 0 ∧
    (∀ level g (t : Fin 5), level < PENTA_LEVELS → g < pentaCount (level + 1) →
      pentaTrapdoorSlot out.2 level g t.val =
        groupChildren (pentaPublicNodes o msg (salts o.permutation k)) level g t) ∧
    out.2.extractLsb' (8 * (QUAD_SALT_BASE + 8)) 192 = k := by
  let s := submission opening checker
  let init := s.initialState .commit msg
  let ready := keyReady init k
  have entry0 : CommitEntry init := abi_entry s (abi opening checker) msg
  have r0 : Live ready 0 := ready_live init entry0 k
  have g0 : Good o k msg (memoryView ready) 0 := initially_good opening checker o k msg
  have pref0 : Prefetched ready.getReg (memoryView ready) 0 := fun h => absurd h (by decide)
  let mid := fixedScan o N_loop 0 ready
  have gMid : Good o k msg (memoryView mid) N_loop := by
    simpa only [Nat.zero_add] using scan_content o k msg N_loop 0 ready (by omega) r0 g0 pref0
  have hitMid : mid ∈ support (scan N_loop 0 ready) := by
    apply writer_support (o.world.withAddCost Oracle.callCost) _ (mid, Q (0 + N_loop) - Q 0)
    change (_, _) ∈ support (o.run (scan N_loop 0 ready))
    rw [fixed_scan_run o N_loop 0 ready (by omega)]; simp [mid]
  have rMid : Live mid N_loop := by simpa only [Nat.zero_add] using scan_post N_loop 0 ready mid (by omega) r0 hitMid
  let leaves := fixedLeaves o ready
  have gLeaves : Good o k msg (memoryView leaves) 16777216 := by
    unfold leaves; rw [fixedLeaves]
    exact fixed_trailing_good o k msg mid rMid.toPacketRegs gMid
  have hitLeaves : leaves ∈ support (runOps trailingPlan mid) := by
    apply writer_support (o.world.withAddCost Oracle.callCost) _ (leaves, opCalls trailingPlan)
    change (_, _) ∈ support (o.run (runOps trailingPlan mid))
    rw [fixed_ops o mid trailingPlan]; simp [leaves, fixedLeaves, mid]
  obtain ⟨leafPC, leafDest, x5, x11, x13, x8, x9⟩ := trailing_post mid leaves rMid hitLeaves
  let tape := tapeOf (memoryView leaves)
  have v := penta_values o msg (salts o.permutation k)
  have tree0 : Tree (zeroed leaves 32 16 16) (pentaPublicNodes o msg (salts o.permutation k)) tape 1 := by
    apply leaf_tree o leaves _ tape v _ _ _ leafDest
    · intro i hi t
      have ch := congrFun (gLeaves.children ⟨i, hi⟩ hi) t
      change memoryView leaves (leafWord i + t.val) = (value o k msg ⟨i, hi⟩).extractLsb' (64 * t.val) 64 at ch
      rw [ch]
      change _ = (pentaNode (pentaFunction o.permutation) (quadPublicLeaves o msg (salts o.permutation k)) 0 i).extractLsb' _ _
      simp only [pentaNode, show i < LENGTH from hi, dite_true, quadPublicLeaves, value]
    · intro i t
      exact tape_of_extract (memoryView leaves) i t
    · intro l g hl hg t ht
      exact gLeaves.zeros l g hl hg t ht
  let z := zeroed leaves 32 16 16
  have regZ (reg : Reg) : z.getReg reg = leaves.getReg reg := zeroed_reg leaves 32 16 16 le_rfl reg
  have entryZ : Entry 45217 z := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [zeroed_pc leaves 32 16 16 le_rfl, leafPC]; rfl
    · rw [regZ, x9]
    · rw [regZ, x8]
    · rw [regZ, x5]
    · rw [regZ, x11]
    · rw [regZ, x13]
  let tops := (checkEvaluation o (levels z)).1
  have tree21 : Tree tops (pentaPublicNodes o msg (salts o.permutation k)) tape 16 :=
    levels_content o z _ tape v entryZ tree0
  have entryT : Entry 214588 tops := levels_post z entryZ (check_evaluation_support o (levels z))
  have stEq : (commitOutput opening checker o msg k).state =
      rootPrefix (writeBits (rootNode tops 4) (wordAddress (heapWord 1))
        (o.permutation (packBuffer (window (memoryView tops) (pentaGroupWord 15 0))))) 10 := by
    unfold commitOutput; rw [fixedCommitState]
  obtain ⟨hRoot, hNodes, hSalts⟩ :=
    root_results opening checker o msg (salts o.permutation k) tape tops tree21 entryT
      (commitOutput opening checker o msg k) stEq
  refine ⟨hRoot, hNodes, ?_⟩
  have s0 := hSalts ⟨0, by decide⟩
  have s1 := hSalts ⟨1, by decide⟩
  have k1 : memoryView leaves (saltWord 0 + 1) = k.extractLsb' 0 64 := by
    simpa only [keyBlock, show saltWord 0 + 1 = keyWord + 1 by decide] using gLeaves.key 1 (by decide) (by decide)
  have k2 : memoryView leaves (saltWord 1) = k.extractLsb' 64 64 := by
    simpa only [keyBlock, show saltWord 1 = keyWord + 2 by decide] using gLeaves.key 2 (by decide) (by decide)
  have k3 : memoryView leaves (saltWord 1 + 1) = k.extractLsb' 128 64 := by
    simpa only [keyBlock, show saltWord 1 + 1 = keyWord + 3 by decide] using gLeaves.key 3 (by decide) (by decide)
  let outTd := ((submission opening checker).readCommit (commitOutput opening checker o msg k)).2
  have lo0 : memoryView leaves (saltWord 0) = outTd.extractLsb' (8 * QUAD_SALT_BASE) 64 := by
    have e := congrArg (fun w : BitVec 128 => w.extractLsb' 0 64) s0
    simp only [tape, tapeOf, BitVec.extractLsb'_append_eq_right] at e
    rw [← e]
    unfold quadTrapdoorSalt outTd
    apply BitVec.eq_of_getLsbD_eq; intro bit hbit
    simp [hbit, show bit < 128 by omega]
  apply key_from_salts outTd k
  · rw [s0]; unfold tape tapeOf; rw [k1, lo0]
  · rw [s1]; unfold tape tapeOf; rw [k3, k2]

theorem commit_counted_trace (opening checker : Image) (o : Oracle) (msg : Message) :
    o.run ((submission opening checker).run .commit msg) =
      (do let k ← $ᵗ Key
          return (commitOutput opening checker o msg k, 39332785)) := by
  rw [execute_commit_full, CommitGolfCandidate.oracle_run_coins_bind]
  apply bind_congr; intro k
  rw [oracle_run_bind, fixed_commit_trace_run o, pure_bind]
  simp only [oracle_run_pure, pure_bind, commitOutput]

noncomputable def penta_counter_commit_transcript (opening checker : Image) :
    PentaCounterCommitTranscript (submission opening checker) where
  trapdoor o msg k := ((submission opening checker).readCommit (commitOutput opening checker o msg k)).2
  distribution o msg := by
    let s := submission opening checker
    change fixedOracleRun o (s.readCommit <$> s.run .commit msg) =ᵈ _
    rw [fixed_oracle_run_map]
    unfold fixedOracleRun
    rw [commit_counted_trace opening checker o msg]
    simp only [map_bind, map_pure]
    apply EvalDistEq.bind_right ($ᵗ Key)
    intro k
    have hR := (commit_physical_results opening checker o msg k).1
    change pure (s.readCommit (commitOutput opening checker o msg k)) =ᵈ _
    rw [show s.readCommit (commitOutput opening checker o msg k) =
      (pentaPublicNodes o msg (salts o.permutation k) PENTA_LEVELS 0,
       (s.readCommit (commitOutput opening checker o msg k)).2) from Prod.ext hR rfl]
    rfl
  key o msg k := (commit_physical_results opening checker o msg k).2.2
  slot o msg k level g t hl hg := (commit_physical_results opening checker o msg k).2.1 level g t hl hg

end TwoPermutationPrototype.PentaGrouped
