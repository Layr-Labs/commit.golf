import CommitGolfCandidate.C3POpenRun
import CommitGolfCandidate.C3PCommitFacts
import CommitGolfCandidate.C3PProofMatch
import CommitGolfCandidate.PairedSaltDraws

/-! # The paired transcript refines the honest view

Under a fixed oracle the commit ends in `commitEnd` (the draws decide it), and the opener's pre-pass
inverts each opened leaf's stored reply. That gives back the leaf's permutation input, hence its salt,
and the pre-pass copies the mate's digest from the reply area. So trapdoor′ is right at every internal
node, every opened salt and every opened mate slot, which is all the records read. -/
namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.C3Leaves TwoPermutationPrototype.Sampling
open Prepass
open Opening (OpeningLayout trapdoorBase trapdoorHeap trapdoorSalt sortedIndex)
open TwoPermutationPrototype.RV64.C3P (commitEnd pInput pLeaves commit_end_facts PairedCommitLayout
  paired_commit_distribution slice_digest replyW)
-- Sequential elaboration, as in C3PAdmission (the verifier builds with parallel elaboration on two CPUs).
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option autoImplicit false

local instance transcriptDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

/-! ### Words of a reply -/

theorem reply_pack (ws : Words 25) : replyWords (packBuffer ws) = ws := by
  funext i; exact packed_word ws i

theorem reply_words_injective : Function.Injective replyWords := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  have e := congrArg (fun f : Words 25 => (f ⟨bit / 64, by omega⟩).getLsbD (bit % 64)) h
  simp only [replyWords, BitVec.getLsbD_extractLsb', true_and_of (Nat.mod_lt bit (by decide : 0 < 64))] at e
  rwa [show 64 * (bit / 64) + bit % 64 = bit by omega] at e

theorem pack_reply (y : BitVec 1600) : packBuffer (replyWords y) = y :=
  reply_words_injective (reply_pack _)

theorem pack_reply_block (y : Block) : packBuffer (replyWords y) = y := pack_reply y

theorem slice_digest_block (x : Block) (s : Nat) (h : s + 4 ≤ 25) :
    x.extractLsb' (64 * s) 256 = packDigestWords (fun k => replyWords x ⟨s + k.val, by omega⟩) :=
  slice_digest x s h

theorem halves_eq (x y : BitVec 128) (h0 : x.extractLsb' 0 64 = y.extractLsb' 0 64)
    (h1 : x.extractLsb' 64 64 = y.extractLsb' 64 64) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  by_cases low : bit < 64
  · have e := congrArg (fun v : BitVec 64 => v.getLsbD bit) h0
    simpa [BitVec.getLsbD_extractLsb', low] using e
  · have e := congrArg (fun v : BitVec 64 => v.getLsbD (bit - 64)) h1
    simp only [BitVec.getLsbD_extractLsb', true_and_of (show bit - 64 < 64 by omega)] at e
    rwa [show 64 + (bit - 64) = bit by omega] at e

/-! ### The opener's input memory is the commit's end memory on the trapdoor -/

theorem trapdoor_bytes : Opening.trapdoorBytes = 232 * 2 ^ 24 + 4096 := by unfold Opening.trapdoorBytes; rfl

theorem opening_input_word (s : Submission) (lay : OpeningLayout s) (R : MachineState) (positions : Positions)
    (w : Nat) (lo : TDw ≤ w) (hi : w + 1 ≤ TDw + Opening.trapdoorBytes / 8) :
    memoryView (s.initialState .opening (readBuffer R trapdoorBase s.sizes.trapdoor, positions)) w =
      memoryView R w := by
  have tb : trapdoorBase = 8 * TDw := rfl
  have tbytes := trapdoor_bytes
  have slice := Opening.input_trapdoor_slice s lay (readBuffer R trapdoorBase s.sizes.trapdoor) positions
    (8 * w - trapdoorBase) 8 (by rw [tbytes] at hi ⊢; omega)
  rw [show trapdoorBase + (8 * w - trapdoorBase) = 8 * w by omega, read_one_word] at slice
  rw [slice, CommitGolfCandidate.read_buffer_slice R trapdoorBase s.sizes.trapdoor (8 * w - trapdoorBase) 8
      (by rw [lay.trapdoorSize, tbytes]; rw [tbytes] at hi; omega),
    show trapdoorBase + (8 * w - trapdoorBase) = 8 * w by omega, read_one_word]

/-! ### Reading trapdoor′ -/

theorem heap_slot (s : Submission) (lay : OpeningLayout s) (P : MachineState) (node : Nat)
    (h : 32 * node + 32 ≤ Opening.trapdoorBytes) :
    trapdoorHeap (s := s) (trapdoorOf s P) node = packDigestWords (window (memoryView P) (TDw + 4 * node)) := by
  unfold trapdoorHeap trapdoorOf
  rw [show 256 * node = 8 * (32 * node) by omega]
  refine (CommitGolfCandidate.read_buffer_slice P trapdoorBase s.sizes.trapdoor (32 * node) 32
    (by rw [lay.trapdoorSize]; exact h)).trans ?_
  rw [show trapdoorBase + 32 * node = 8 * (TDw + 4 * node) by unfold trapdoorBase TDw; norm_num [LENGTH, LOG_LENGTH]; omega]
  exact c3_read_digest P (TDw + 4 * node)

theorem salt_slot (s : Submission) (lay : OpeningLayout s) (P : MachineState) (i : Index) :
    (trapdoorSalt (s := s) (trapdoorOf s P) i).extractLsb' 0 64 = memoryView P (NW + 2 * i.val) ∧
    (trapdoorSalt (s := s) (trapdoorOf s P) i).extractLsb' 64 64 = memoryView P (NW + 2 * i.val + 1) := by
  have hi := i.isLt
  have hL : LENGTH = 16777216 := rfl
  have tbytes := trapdoor_bytes
  have slot : trapdoorSalt (s := s) (trapdoorOf s P) i = readBuffer P (8 * (NW + 2 * i.val)) 16 := by
    have e := CommitGolfCandidate.read_buffer_slice P trapdoorBase s.sizes.trapdoor (80 * LENGTH + 16 * i.val) 16
      (by rw [lay.trapdoorSize, tbytes]; have := hL; omega)
    rw [show trapdoorBase + (80 * LENGTH + 16 * i.val) = 8 * (NW + 2 * i.val) by
      unfold trapdoorBase NW TDw; have := hL; omega] at e
    exact e
  rw [slot]
  constructor
  · have e0 := CommitGolfCandidate.read_buffer_slice P (8 * (NW + 2 * i.val)) 16 0 8 (by decide)
    rw [Nat.add_zero, read_one_word] at e0
    exact e0
  · have e1 := CommitGolfCandidate.read_buffer_slice P (8 * (NW + 2 * i.val)) 16 8 8 (by decide)
    rw [show 8 * (NW + 2 * i.val) + 8 = 8 * (NW + 2 * i.val + 1) by omega, read_one_word] at e1
    exact e1

/-! ### The opened positions -/

theorem opened_ordinal (positions : Positions) (i : Index) (hi : i ∈ positions) :
    ∃ j < positions.card, preIdx positions j = i.val := by
  have m : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort _).mpr hi
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.mp m
  have len : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
  refine ⟨j, by omega, ?_⟩
  unfold preIdx
  rw [dif_pos (by omega)]
  unfold sortedIndex
  rw [e]

/-! ### What the pre-pass leaves -/

theorem perm_window_salt (C : Compression) (i : Index) (nonce : Words 2) (v : Words 32) (t : Nat) (ht : t < 2) :
    c3pPermWords C i nonce v ⟨saltOff i.val + t, by unfold saltOff; split <;> omega⟩ = nonce ⟨t, ht⟩ := by
  unfold c3pPermWords saltOff
  by_cases ev : i.val % 2 = 0
  · have even : c3pEven i := ev
    rw [if_pos even]
    unfold c3pEvenWords
    simp only [ev, ↓reduceIte]
    rw [dif_neg (by omega), dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1; apply Fin.ext; simp
  · have odd : ¬ c3pEven i := ev
    rw [if_neg odd]
    unfold c3pOddWords
    simp only [ev, ↓reduceIte, Nat.zero_add]
    rw [dif_pos ht]

/-- **Trapdoor′** after an honest pre-pass over the trapdoor of an honest commit. -/
theorem trapdoor_prime (s : Submission) (abi : OpeningABI s) (oracle : Oracle) (msg : Message)
    (salts : CompleteSaltTape) (R : MachineState)
    (nodes : ∀ n, 0 < n → n < LENGTH →
      readBuffer R (8 * treeWord n) 32 = Hybrid.heap oracle.compression (pLeaves oracle msg salts) n)
    (replies : ∀ j (hj : j < 2 ^ 24), (window (memoryView R) (replyW + 25 * j) : Words 25) =
      replyWords (oracle.permutation (pInput oracle msg salts ⟨j, hj⟩)))
    (positions : Positions) (positive : 0 < positions.card) (P : MachineState)
    (ended : PreEnd (setupPrefix (s.initialState .opening (readBuffer R trapdoorBase s.sizes.trapdoor, positions)) 12)
      positions.card (preIdx positions)
      (honestYs oracle (memoryView (setupPrefix (s.initialState .opening
        (readBuffer R trapdoorBase s.sizes.trapdoor, positions)) 12)) (preIdx positions)) P) :
    let heap := Hybrid.heap oracle.compression (pLeaves oracle msg salts)
    (∀ n, 0 < n → n < LENGTH → trapdoorHeap (s := s) (trapdoorOf s P) n = heap n) ∧
    (∀ i ∈ positions, trapdoorHeap (s := s) (trapdoorOf s P) (LENGTH + (i.val ^^^ 1)) = heap (LENGTH + (i.val ^^^ 1))) ∧
    (∀ i ∈ positions, trapdoorSalt (s := s) (trapdoorOf s P) i = salts i) := by
  intro heap
  let initial := s.initialState .opening (readBuffer R trapdoorBase s.sizes.trapdoor, positions)
  let Q := setupPrefix initial 12
  have hL : LENGTH = 16777216 := rfl
  have tbytes := trapdoor_bytes
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have ready := pre_ready s abi.toOpeningLayout (readBuffer R trapdoorBase s.sizes.trapdoor) positions positive
  have nonempty : initial.getReg .x16 ≠ 0#64 :=
    (show initial.getReg .x16 = BitVec.ofNat 64 positions.card from rfl) ▸ nonempty_count positions positive
  have setupMem := (setup12_registers initial nonempty).2.2.2.2.2.2.2.2.2.2.2
  have mQ : ∀ w, TDw ≤ w → w + 1 ≤ TDw + Opening.trapdoorBytes / 8 → memoryView Q w = memoryView R w := by
    intro w lo hi
    rw [show memoryView Q = memoryView initial from memoryView_congr setupMem]
    exact opening_input_word s abi.toOpeningLayout R positions w lo hi
  have rw' : Rw = replyW := rfl
  have idxB : ∀ j < positions.card, preIdx positions j < LENGTH := fun j hj => ready.idxSmall j hj
  -- the honest answers are the leaves' inputs
  have ys : ∀ j (hj : j < positions.card), honestYs oracle (memoryView Q) (preIdx positions) j =
      pInput oracle msg salts ⟨preIdx positions j, idxB j hj⟩ := by
    intro j hj
    have small := ready.idxSmall j hj
    unfold honestYs
    have win : (window (memoryView Q) (Rw + 25 * preIdx positions j) : Words 25) =
        replyWords (oracle.permutation (pInput oracle msg salts ⟨preIdx positions j, idxB j hj⟩)) := by
      rw [← replies _ (idxB j hj)]
      funext ⟨k, hk⟩
      simp only [window]
      rw [rw']
      exact mQ _ (by unfold replyW TDw; omega) (by rw [tbytes]; unfold replyW TDw; omega)
    rw [win, pack_reply_block, inverse_answer, Equiv.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro n lo hi
    show _ = Hybrid.heap oracle.compression (pLeaves oracle msg salts) n
    rw [heap_slot s abi.toOpeningLayout P n (by rw [tbytes]; omega), ← nodes n lo hi,
      show 8 * treeWord n = 8 * (TDw + 4 * n) by unfold treeWord TDw; omega, c3_read_digest]
    congr 1
    funext ⟨k, hk⟩
    simp only [window]
    have wv : TDw + 4 * n + k < HW := by unfold HW; omega
    rw [ended.frame _ (by unfold TDw at *; omega) (Or.inr (by unfold scratchW TDw; omega))
      (Or.inr (by unfold Lw TDw; omega))
      (fun j hj => by have := ready.idxSmall j hj; unfold NW HW at *; omega)
      (fun j hj t ht => by unfold HW at wv ⊢; omega)]
    exact mQ _ (by omega) (by rw [tbytes]; unfold HW TDw at wv; omega)
  · intro i hi
    obtain ⟨j, hj, hij⟩ := opened_ordinal positions i hi
    have small := i.isLt
    rw [heap_slot s abi.toOpeningLayout P _ (by rw [tbytes]; have := xor_one_small i.val small; omega),
      show TDw + 4 * (LENGTH + (i.val ^^^ 1)) = HW + 4 * (i.val ^^^ 1) by unfold HW; have := hL; omega]
    have mateW : ∀ t < 4, memoryView P (HW + 4 * (i.val ^^^ 1) + t) = memoryView R (mateWord i.val + t) := by
      intro t ht
      have e := ended.mate j hj t ht
      rw [hij] at e
      rw [e]
      unfold listVal
      rw [dif_neg (by omega), show 2 + t - 2 = t by omega]
      exact mQ _ (by unfold mateWord Rw TDw; split <;> omega) (by rw [tbytes]; unfold mateWord Rw TDw; split <;> omega)
    by_cases ev : i.val % 2 = 0
    · have hx : i.val ^^^ 1 = i.val + 1 := xor_one_even ev
      have hm : i.val + 1 < 2 ^ 24 := by omega
      have y := replies (i.val + 1) hm
      rw [show (packDigestWords (window (memoryView P) (HW + 4 * (i.val ^^^ 1))) : BitVec 256) =
          packDigestWords (fun k => replyWords (oracle.permutation (pInput oracle msg salts ⟨i.val + 1, hm⟩))
            ⟨0 + k.val, by omega⟩) by
        congr 1; funext ⟨k, hk⟩; simp only [window]
        rw [mateW k hk, show mateWord i.val + k = replyW + 25 * (i.val + 1) + k by
          unfold mateWord replyW Rw TDw; rw [if_pos ev]; omega, ← y]
        simp only [window, Nat.zero_add]]
      rw [← slice_digest_block _ 0 (by decide), hx]
      show _ = Hybrid.heap oracle.compression (pLeaves oracle msg salts) (LENGTH + (i.val + 1))
      rw [show LENGTH + (i.val + 1) = LENGTH + (⟨i.val + 1, hm⟩ : Index).val from rfl, Hybrid.heap_leaf]
      simp only [pLeaves, c3pFullLeafDigests, c3pLeafDigest, c3pDigestWindow]
      rw [if_neg (show ¬ c3pEven ⟨i.val + 1, hm⟩ by unfold c3pEven; simp only; omega)]
      rfl
    · have hx : i.val ^^^ 1 = i.val - 1 := xor_one_odd (by omega)
      have hm : i.val - 1 < 2 ^ 24 := by omega
      have y := replies (i.val - 1) hm
      rw [show (packDigestWords (window (memoryView P) (HW + 4 * (i.val ^^^ 1))) : BitVec 256) =
          packDigestWords (fun k => replyWords (oracle.permutation (pInput oracle msg salts ⟨i.val - 1, hm⟩))
            ⟨21 + k.val, by omega⟩) by
        congr 1; funext ⟨k, hk⟩; simp only [window]
        rw [mateW k hk, show mateWord i.val + k = replyW + 25 * (i.val - 1) + (21 + k) by
          unfold mateWord replyW Rw TDw; rw [if_neg ev]; omega]
        have e := congrFun y ⟨21 + k, by omega⟩
        simp only [window] at e
        exact e]
      rw [← slice_digest_block _ 21 (by decide), hx]
      show _ = Hybrid.heap oracle.compression (pLeaves oracle msg salts) (LENGTH + (i.val - 1))
      rw [show LENGTH + (i.val - 1) = LENGTH + (⟨i.val - 1, hm⟩ : Index).val from rfl, Hybrid.heap_leaf]
      simp only [pLeaves, c3pFullLeafDigests, c3pLeafDigest, c3pDigestWindow]
      rw [if_pos (show c3pEven ⟨i.val - 1, hm⟩ by unfold c3pEven; simp only; omega)]
      rfl
  · intro i hi
    obtain ⟨j, hj, hij⟩ := opened_ordinal positions i hi
    obtain ⟨s0, s1⟩ := salt_slot s abi.toOpeningLayout P i
    have saltW : ∀ t (ht : t < 2), memoryView P (NW + 2 * i.val + t) = saltWords (salts i) ⟨t, ht⟩ := by
      intro t ht
      have e := ended.salt j hj t ht
      rw [hij] at e
      rw [e]
      unfold listVal
      rw [dif_pos ht, ys j hj]
      have ie : (⟨preIdx positions j, idxB j hj⟩ : Index) = i := Fin.ext hij
      unfold pInput c3pPermInput
      rw [reply_pack, ie]
      exact perm_window_salt oracle.compression i (saltWords (salts i)) (messageWords msg i) t ht
    apply halves_eq
    · rw [s0, show NW + 2 * i.val = NW + 2 * i.val + 0 from rfl, saltW 0 (by decide)]; rfl
    · rw [s1, saltW 1 (by decide)]; rfl

/-! ### The refinement -/

theorem mapM_support {α β : Type} (f : α → ProbComp β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (xs.mapM f) →
      ys.length = xs.length ∧ ∀ y ∈ ys, ∃ x ∈ xs, y ∈ support (f x) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    simp only [List.mapM_nil, support_pure, Set.mem_singleton_iff] at h
    subst h; simp
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨l, m⟩ := ih bs hbs
    refine ⟨by simp [l], ?_⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨x, List.mem_cons_self .., hb⟩
    · obtain ⟨x', hx', hy'⟩ := m y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', hy'⟩

theorem draws_lengths (wss : List (List (BitVec 256)))
    (h : wss ∈ support ((List.range 8192).mapM (fun _ =>
      (List.range 1024).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256)))))) :
    wss.length = 8192 ∧ ∀ ws ∈ wss, ws.length = 1024 := by
  obtain ⟨l, m⟩ := mapM_support _ _ wss h
  refine ⟨by simpa using l, fun ws hws => ?_⟩
  obtain ⟨_, _, hws'⟩ := m ws hws
  simpa using (mapM_support _ _ ws hws').1

/-- The commit's end state, with the message kept behind a definition (so rewrites see no
dependent `Input` application). -/
def asTrapdoor (s : Submission) (p : Commitment × BitVec (8 * s.sizes.trapdoor)) : Commitment × s.scheme.Trapdoor := p

def pairedEnd (s : Submission) (oracle : Oracle) (msg : Message) (wss : List (List (BitVec 256))) : MachineState :=
  commitEnd oracle (s.initialState .commit msg) wss

theorem paired_commit_distribution' (s : Submission) (lay : PairedCommitLayout s) (oracle : Oracle) (msg : Message) :
    fixedOracleRun oracle (s.scheme.commit msg) =
      ((List.range 8192).mapM (fun _ => (List.range 1024).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256)))) >>=
        fun wss => pure (asTrapdoor s (s.readCommit ⟨.success, pairedEnd s oracle msg wss, 1267884575, 83886079⟩))) :=
  paired_commit_distribution s lay oracle msg

theorem empty_builder (compress : Compression) (positions : Positions) (salts : OpenedSalts positions)
    (leaves : DigestTape) (empty : positions.card = 0) :
    (Hybrid.builder compress positions salts leaves).2 = [] := by
  have e : positions = ∅ := Finset.card_eq_zero.mp empty
  subst e
  simp [Hybrid.builder, frontierProof]

theorem empty_read_proof (s : Submission) (result : Execution) (h : (result.state.getReg .x11).toNat = 0) :
    s.readProof result = [] := by
  unfold Submission.readProof
  split <;> simp [h]

set_option maxHeartbeats 400000 in
/-- One draw sequence: the opening against the commit's trapdoor gives the honest view of the paired
salt tape. -/
theorem transcript_at (s : Submission) (lay : PairedCommitLayout s) (abi : OpeningABI s) (oracle : Oracle)
    (msg : Message) (positions : Positions) (wss : List (List (BitVec 256))) (len : wss.length = 8192)
    (lens : ∀ ws ∈ wss, ws.length = 1024) :
    fixedOracleRun oracle (s.scheme.opening (readBuffer (pairedEnd s oracle msg wss) s.layout.trapdoor s.sizes.trapdoor)
        positions >>= fun opening => pure (readBuffer (pairedEnd s oracle msg wss) s.layout.commitment DIGEST_BYTES,
          opening)) =
      pure (c3pHonestView Hybrid.wireBuilder oracle.compression (BiPermutation.equiv Block oracle.permutation) msg positions
        (pairedSaltTape wss.flatten)) := by
  obtain ⟨root0, nodes, replies⟩ := commit_end_facts s lay oracle msg wss len lens
  have root : readBuffer (pairedEnd s oracle msg wss) 4294971392 DIGEST_BYTES =
      Hybrid.heap oracle.compression (pLeaves oracle msg (pairedSaltTape wss.flatten)) 1 := root0
  rw [lay.trapdoor, lay.commitment, fixed_oracle_run_bind]
  let td := readBuffer (pairedEnd s oracle msg wss) 4294971424 s.sizes.trapdoor
  change (fixedOracleRun oracle (s.readProof <$> s.run .opening (td, positions)) >>= _) = _
  rw [fixed_oracle_run_map]
  by_cases empty : positions.card = 0
  · obtain ⟨result, run, wire⟩ := opening_physical_empty s abi td positions empty
    rw [run, fixed_oracle_run_pure, map_pure, pure_bind, fixed_oracle_run_pure]
    unfold c3pHonestView
    refine congrArg Pure.pure (Prod.ext ?_ ?_)
    · exact root
    rw [wire.bytes]
    show Hybrid.wireProof positions _ = Hybrid.wireProof positions _
    congr 1
    have e : positions = ∅ := Finset.card_eq_zero.mp empty
    subst e
    simp [proofFromTrapdoor, Hybrid.builder, frontierProof, Opening.openingNodes]
  · obtain ⟨P, result, fixed, ended, success, rest⟩ := paired_opening_fixed s abi oracle td positions (by omega)
    rw [fixed, map_pure, pure_bind, fixed_oracle_run_pure]
    unfold c3pHonestView
    refine congrArg Pure.pure (Prod.ext ?_ ?_)
    · exact root
    have shape : result = ⟨.success, result.state, result.cycles, result.oracleCalls⟩ := by
      cases result; simp_all
    rw [shape, rest.proof]
    obtain ⟨tI, tM, tS⟩ := trapdoor_prime s abi oracle msg (pairedSaltTape wss.flatten) _ nodes replies positions
      (by omega) P ended
    show Hybrid.wireProof positions _ = Hybrid.wireProof positions _
    rw [proof_from_trapdoor_on s (trapdoorOf s P) positions oracle.compression
      (pLeaves oracle msg (pairedSaltTape wss.flatten)) _ tI tM tS]

theorem flat_map_const_length {α β : Type} (xs : List α) (ys : List β) :
    (xs.flatMap fun _ => ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; rw [Nat.succ_mul]; omega

/-- **`C3PTranscriptRefines`**: the paired machine's commitment and opening are the honest view of a
uniform salt tape. -/
theorem paired_transcript_refines (s : Submission) (lay : PairedCommitLayout s) (abi : OpeningABI s) :
    C3PTranscriptRefines s.scheme Hybrid.wireBuilder := by
  intro oracle msg positions
  let V := fun salts => c3pHonestView Hybrid.wireBuilder oracle.compression (BiPermutation.equiv Block oracle.permutation)
    msg positions salts
  unfold executableTranscript
  rw [fixed_oracle_run_bind, paired_commit_distribution' s lay oracle msg, bind_assoc]
  simp only [pure_bind]
  simp only [asTrapdoor, Submission.readCommit]
  rw [bind_congr_of_forall_mem_support _ (g := fun wss => (Pure.pure (V (pairedSaltTape wss.flatten)) : ProbComp _)) ?step]
  case step =>
    intro wss hw
    exact transcript_at s lay abi oracle msg positions wss (draws_lengths wss hw).1 (draws_lengths wss hw).2
  have flat := map_tiles_flatten (m := ProbComp) (List.range 8192) (List.range 1024)
    ($ᵗ BitVec 256 : ProbComp (BitVec 256))
  have e : ((List.range 8192).mapM (fun _ => (List.range 1024).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256)))) >>=
        fun wss => (pure (V (pairedSaltTape wss.flatten)) : ProbComp _)) =
      (((List.range 8192).flatMap (fun _ => List.range 1024)).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256))) >>=
        fun words => pure (V (pairedSaltTape words))) := by
    rw [← flat, bind_assoc]
    simp only [pure_bind]
  rw [e]
  exact paired_salt_draws_uniform _ (by rw [flat_map_const_length]; simp; rfl) (fun salts => pure (V salts))

end TwoPermutationPrototype.PackedOpening
