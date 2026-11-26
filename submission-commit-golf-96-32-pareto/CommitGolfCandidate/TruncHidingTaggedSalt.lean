import CommitGolfCandidate.HidingTaggedSalt

import CommitGolfCandidate.TruncHidingHybrid

namespace CommitGolfCandidate.Trunc

open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

local instance (priority := high) hidingTaggedSaltDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 12000

set_option maxHeartbeats 800000

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

def evalParents (leaves : Nat → Digest) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun node => if LENGTH ≤ node ∧ node < 2 * LENGTH then leaves (node - LENGTH) else 0)
  | k + 1 => do
      let heap ← evalParents leaves k
      let node := LENGTH - 1 - k
      let p ← hashParent (heap (2 * node)) (heap (2 * node + 1))
      pure (Function.update heap node (storeNode node p))

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
    rw [hp, if_pos h2l, if_pos h2r,
      pure_bind, fixed_oracle_run_pure]
    congr 1; funext m
    have hnodeEq : LENGTH - 1 - k = node := rfl
    rw [hnodeEq]
    by_cases hm : m = node
    · subst hm
      have hnodeIn : LENGTH - (k + 1) ≤ node ∧ node < 2 * LENGTH := by dsimp only [node]; omega
      rw [Function.update_self, if_pos hnodeIn,reference_heap_parent oracle.compression LENGTH leaves node hpos hlt]; rfl
    · rw [Function.update_of_ne hm]
      have hiff : (LENGTH - k ≤ m ∧ m < 2 * LENGTH) ↔ (LENGTH - (k + 1) ≤ m ∧ m < 2 * LENGTH) := by
        dsimp only [node] at hm; omega
      by_cases hc : LENGTH - (k + 1) ≤ m ∧ m < 2 * LENGTH
      · rw [if_pos (hiff.mpr hc), if_pos hc]
      · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]

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

private theorem digestHitsStored (ps : Positions) (salt : Index → Salt) (n : Nat) (x : Digest) :
    digestHitsUnopened ps salt (storeNode n x)=digestHitsUnopened ps salt x := by
  have slice (offset len : Nat) (h : offset+len≤240) :
      (storeNode n x).extractLsb' offset len=x.extractLsb' offset len := by
    unfold storeNode;split
    · apply BitVec.eq_of_getLsbD_eq;intro j hj
      have small : offset+j<240 := by omega
      simp only [padLow,BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and,BitVec.getLsbD_append,if_pos small,low240,Nat.zero_add,small,ite_true]
    · rfl
  unfold digestHitsUnopened
  rw [slice 128 64 (by decide),slice 0 128 (by decide)]

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
      · subst hm; simpa only [Function.update_self, digestHitsStored] using hpClean.1
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

end CommitGolfCandidate.Trunc
