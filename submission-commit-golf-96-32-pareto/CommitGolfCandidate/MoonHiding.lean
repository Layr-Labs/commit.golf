import CommitGolfCandidate.MoonHidingCore

/-! Complete paired late-salt (SM-PLS-40) statistical hiding proof for our pure-binary commitment scheme.
Conditioned on Stage 1's lazy compression cache plus all `3 * LENGTH` unsalted leaf calls (`u, a, b`):
  1. Simultaneous Call-3 reprogramming for ALL hidden leaves `i ∉ positions` outside the rare
     salt event `BadRand` (`BadMidpoint(sM)` with multiplicity >= 5, plus 192-bit salt collisions):
     `TV(Real(m), Ideal(m)) <= 8 * budget / 2^128 + 2 / 2^141 + O((budget + 2^26) * 2^24 / 2^192)`.
  2. Since Call 3 is the final leaf call, `Ideal(m₀) = Ideal(m₁)` identically (`TV = 0`).
Total TV distance is strictly below `(budget + 1) / 2^120` for every opening size `0 <= k <= 2^24`. -/
namespace CommitGolfCandidate

local instance moonHidingDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

/-! ### 1. Exact Machine-to-Reference Interface -/

def honestTranscript (message : Message) (positions : Positions) :
    OracleComp World (Commitment × Proof) := do
  let (root, trapdoor) ← submission.scheme.commit message
  let proof ← submission.scheme.opening trapdoor positions
  return (root, proof)

def referenceTranscript (h768 : COMPRESSION_INPUT_LENGTH = 768) (compress : Compression)
    (message : Message) (salts : Index → Salt192) (positions : Positions) : Commitment × Proof :=
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  (rootVal c message salts, referenceProof (nodeVal c message salts) salts positions)

/-- Machine refinement contract proved by `MoonCommitRef` + `MoonOpenRef` + `MoonCertificate`. -/
def HonestTranscriptRefines (h768 : COMPRESSION_INPUT_LENGTH = 768) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    EvalDistEq (fixedOracleRun oracle (honestTranscript message positions))
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        pure (referenceTranscript h768 oracle.compression message (pairSalts rand) positions))

/-! ### 2. Ideal Game (Fresh Uniform 256-bit Leaf Digests on Unopened Positions) -/

def idealLeaves (c : Comp96) (msg : Message) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) (i : Index) : Digest :=
  if i ∈ positions then leafDigest c i (sOpen i) (msg i) else leafRand i

def idealTranscript (h768 : COMPRESSION_INPUT_LENGTH = 768) (compress : Compression)
    (msg : Message) (sOpen : Index → Salt192) (leafRand : Index → Digest) (positions : Positions) :
    Commitment × Proof :=
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  let nodes := nodeValFromLeaves c (idealLeaves c msg sOpen leafRand positions)
  (nodes 24 0, referenceProof nodes sOpen positions)

def idealLeavesFromAB (c : Comp96) (aVec bVec : Index → Digest) (sOpen : Index → Salt192)
    (leafRand : Index → Digest) (positions : Positions) (i : Index) : Digest :=
  if i ∈ positions then c (leafFinalInput i (aVec i) (bVec i) (sOpen i)) else leafRand i

theorem idealLeafFn_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768) (o : Oracle)
    (aVec bVec : Index → Digest) (salts : Index → Salt192) (lr : Index → Digest)
    (positions : Positions) (i : Index) :
    fixedOracleRun o (idealLeafFn h768 aVec bVec salts lr positions i) =
      pure (idealLeavesFromAB (fun x => o.compression (x.cast h768.symm)) aVec bVec salts lr positions i) := by
  let c : Comp96 := fun x => o.compression (x.cast h768.symm)
  change fixedOracleRun o (idealLeafFn h768 aVec bVec salts lr positions i) =
    pure (idealLeavesFromAB c aVec bVec salts lr positions i)
  unfold idealLeafFn idealLeavesFromAB
  by_cases hi : i ∈ positions
  · simp only [hi, ite_true]; exact queryCompress_fixed h768 o _
  · simp only [hi, ite_false]; exact fixed_oracle_run_pure o _

def idealTranscriptFromAB (h768 : COMPRESSION_INPUT_LENGTH = 768) (compress : Compression)
    (aVec bVec : Index → Digest) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) : Commitment × Proof :=
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  let nodes := nodeValFromLeaves c (idealLeavesFromAB c aVec bVec sOpen leafRand positions)
  (nodes 24 0, referenceProof nodes sOpen positions)

theorem referenceProof_congr_opened (nodes : Nat → Nat → Digest)
    (s1 s2 : Index → Salt192) (positions : Positions)
    (hagree : ∀ i ∈ positions, s1 i = s2 i) :
    referenceProof nodes s1 positions = referenceProof nodes s2 positions := by
  unfold referenceProof referenceProofFwd
  split
  · rfl
  · apply congrArg (· ++ pack6BitsRev (referenceProofTails nodes positions))
    apply congrArg (· ++ capFrontierFwd nodes positions)
    apply List.flatMap_congr
    intro i hi
    have hmem : i ∈ positions := (Finset.mem_sort (· ≤ ·)).mp hi
    simp only [recordFwd, hagree i hmem]

theorem idealTranscript_congr_opened_msg (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (compress : Compression) (m0 m1 : Message) (sOpen : Index → Salt192)
    (leafRand : Index → Digest) (positions : Positions)
    (hagree : ∀ i ∈ positions, m0 i = m1 i) :
    idealTranscript h768 compress m0 sOpen leafRand positions =
      idealTranscript h768 compress m1 sOpen leafRand positions := by
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  have hlv : idealLeaves c m0 sOpen leafRand positions =
      idealLeaves c m1 sOpen leafRand positions := by
    funext i
    unfold idealLeaves
    by_cases hi : i ∈ positions
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hi), ite_eq_left_of_eq_true _ _ (eq_true hi), hagree i hi]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hi), ite_eq_right_of_eq_false _ _ (eq_false hi)]
  unfold idealTranscript
  dsimp only
  change (nodeValFromLeaves c (idealLeaves c m0 sOpen leafRand positions) 24 0,
      referenceProof (nodeValFromLeaves c (idealLeaves c m0 sOpen leafRand positions)) sOpen positions) =
    (nodeValFromLeaves c (idealLeaves c m1 sOpen leafRand positions) 24 0,
      referenceProof (nodeValFromLeaves c (idealLeaves c m1 sOpen leafRand positions)) sOpen positions)
  rw [hlv]

theorem idealTranscript_congr_opened_salts (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (compress : Compression) (aVec bVec : Index → Digest) (s1 s2 : Index → Salt192)
    (leafRand : Index → Digest) (positions : Positions)
    (hagree : ∀ i ∈ positions, s1 i = s2 i) :
    idealTranscriptFromAB h768 compress aVec bVec s1 leafRand positions =
      idealTranscriptFromAB h768 compress aVec bVec s2 leafRand positions := by
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  have hlv : idealLeavesFromAB c aVec bVec s1 leafRand positions =
      idealLeavesFromAB c aVec bVec s2 leafRand positions := by
    funext i; unfold idealLeavesFromAB
    by_cases hi : i ∈ positions
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hi), ite_eq_left_of_eq_true _ _ (eq_true hi), hagree i hi]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hi), ite_eq_right_of_eq_false _ _ (eq_false hi)]
  unfold idealTranscriptFromAB
  dsimp only
  change (nodeValFromLeaves c (idealLeavesFromAB c aVec bVec s1 leafRand positions) 24 0,
      referenceProof (nodeValFromLeaves c (idealLeavesFromAB c aVec bVec s1 leafRand positions)) s1 positions) =
    (nodeValFromLeaves c (idealLeavesFromAB c aVec bVec s2 leafRand positions) 24 0,
      referenceProof (nodeValFromLeaves c (idealLeavesFromAB c aVec bVec s2 leafRand positions)) s2 positions)
  rw [hlv]
  exact Prod.ext rfl (referenceProof_congr_opened _ s1 s2 positions hagree)

theorem idealTranscriptFromAB_eq_ideal (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (compress : Compression) (msg : Message) (aVec bVec : Index → Digest)
    (sOpen : Index → Salt192) (leafRand : Index → Digest) (positions : Positions)
    (hab : ∀ i : Index,
      leafA (fun x => compress (x.cast h768.symm)) (msg i) = aVec i ∧
      leafB (fun x => compress (x.cast h768.symm)) (msg i) = bVec i) :
    idealTranscriptFromAB h768 compress aVec bVec sOpen leafRand positions =
      idealTranscript h768 compress msg sOpen leafRand positions := by
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  have hlv : idealLeavesFromAB c aVec bVec sOpen leafRand positions =
      idealLeaves c msg sOpen leafRand positions := by
    funext i; unfold idealLeavesFromAB idealLeaves leafDigest
    by_cases hi : i ∈ positions
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hi), ite_eq_left_of_eq_true _ _ (eq_true hi),
        (hab i).1, (hab i).2]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hi), ite_eq_right_of_eq_false _ _ (eq_false hi)]
  unfold idealTranscriptFromAB idealTranscript
  dsimp only
  change (nodeValFromLeaves c (idealLeavesFromAB c aVec bVec sOpen leafRand positions) 24 0,
      referenceProof (nodeValFromLeaves c (idealLeavesFromAB c aVec bVec sOpen leafRand positions)) sOpen positions) =
    (nodeValFromLeaves c (idealLeaves c msg sOpen leafRand positions) 24 0,
      referenceProof (nodeValFromLeaves c (idealLeaves c msg sOpen leafRand positions)) sOpen positions)
  rw [hlv]

theorem idealTranscriptFromAB_eq_reference (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (compress : Compression) (msg : Message) (aVec bVec : Index → Digest)
    (salts : Index → Salt192) (positions : Positions)
    (hab : ∀ i : Index,
      leafA (fun x => compress (x.cast h768.symm)) (msg i) = aVec i ∧
      leafB (fun x => compress (x.cast h768.symm)) (msg i) = bVec i) :
    let c : Comp96 := fun x => compress (x.cast h768.symm)
    idealTranscriptFromAB h768 compress aVec bVec salts
      (fun i => c (leafFinalInput i (aVec i) (bVec i) (salts i))) positions =
    referenceTranscript h768 compress msg salts positions := by
  intro c
  have hlv : idealLeavesFromAB c aVec bVec salts
      (fun i => c (leafFinalInput i (aVec i) (bVec i) (salts i))) positions =
      fun i => leafDigest c i (salts i) (msg i) := by
    funext i; unfold idealLeavesFromAB leafDigest
    by_cases hi : i ∈ positions
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hi), (hab i).1, (hab i).2]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hi), (hab i).1, (hab i).2]
  unfold idealTranscriptFromAB referenceTranscript rootVal nodeVal
  dsimp only
  change (nodeValFromLeaves c (idealLeavesFromAB c aVec bVec salts
        (fun i => c (leafFinalInput i (aVec i) (bVec i) (salts i))) positions) 24 0,
      referenceProof (nodeValFromLeaves c (idealLeavesFromAB c aVec bVec salts
        (fun i => c (leafFinalInput i (aVec i) (bVec i) (salts i))) positions)) salts positions) =
    (nodeValFromLeaves c (fun i => leafDigest c i (salts i) (msg i)) 24 0,
      referenceProof (nodeValFromLeaves c (fun i => leafDigest c i (salts i) (msg i))) salts positions)
  rw [hlv]

/-! ### 3. Simultaneous Reprogramming on Any Injective Finset `S` -/

def hiddenCall3 (h768 : COMPRESSION_INPUT_LENGTH = 768) (aVec bVec : Index → Digest)
    (salts : Index → Salt192) (i : Index) : BitVec COMPRESSION_INPUT_LENGTH :=
  (leafFinalInput i (aVec i) (bVec i) (salts i)).cast h768.symm

private def toOut (d : Digest) : BitVec COMPRESSION_OUTPUT_LENGTH := d
private def fromOut (d : BitVec COMPRESSION_OUTPUT_LENGTH) : Digest := d

noncomputable def reprogramFinset (callFn : Index → BitVec COMPRESSION_INPUT_LENGTH)
    (table : Compression) (leafRand : Index → Digest) (S : Finset Index) : Compression :=
  fun x =>
    if h : ∃ i ∈ S, callFn i = x then
      toOut (leafRand (Classical.choose h))
    else table x

theorem reprogramFinset_mem (callFn : Index → BitVec COMPRESSION_INPUT_LENGTH)
    (table : Compression) (leafRand : Index → Digest) (S : Finset Index)
    (hinj : Set.InjOn callFn (S : Set Index)) (i : Index) (hi : i ∈ S) :
    reprogramFinset callFn table leafRand S (callFn i) = toOut (leafRand i) := by
  unfold reprogramFinset
  split_ifs with h
  · have hsp := Classical.choose_spec h
    rw [hinj hsp.1 hi hsp.2]
  · exact (h ⟨i, hi, rfl⟩).elim

theorem reprogramFinset_not_mem (callFn : Index → BitVec COMPRESSION_INPUT_LENGTH)
    (table : Compression) (leafRand : Index → Digest) (S : Finset Index)
    (x : BitVec COMPRESSION_INPUT_LENGTH) (hnot : ∀ i ∈ S, callFn i ≠ x) :
    reprogramFinset callFn table leafRand S x = table x := by
  unfold reprogramFinset
  split_ifs with h
  · obtain ⟨i, hi, heq⟩ := h
    exact (hnot i hi heq).elim
  · rfl

theorem reprogramFinset_insert (callFn : Index → BitVec COMPRESSION_INPUT_LENGTH)
    (table : Compression) (leafRand : Index → Digest) (a : Index) (S : Finset Index)
    (hinj : Set.InjOn callFn ((insert a S : Finset Index) : Set Index)) :
    reprogramFinset callFn table leafRand (insert a S) =
      Function.update (reprogramFinset callFn table leafRand S) (callFn a) (toOut (leafRand a)) := by
  have hinjS : Set.InjOn callFn (S : Set Index) :=
    hinj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
  funext x
  by_cases hx : x = callFn a
  · subst hx
    rw [Function.update_self, reprogramFinset_mem callFn _ _ _ hinj a (Finset.mem_insert_self a S)]
  · rw [Function.update_of_ne hx]
    by_cases hS : ∃ i ∈ S, callFn i = x
    · obtain ⟨i, hi, rfl⟩ := hS
      rw [reprogramFinset_mem callFn _ _ _ hinj i (Finset.mem_insert_of_mem hi),
        reprogramFinset_mem callFn _ _ _ hinjS i hi]
    · rw [reprogramFinset_not_mem callFn _ _ (insert a S), reprogramFinset_not_mem callFn _ _ S]
      · intro i hi heq; exact hS ⟨i, hi, heq⟩
      · intro i hi heq
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · exact hx heq.symm
        · exact hS ⟨i, hiS, heq⟩

theorem reprogramFinset_dist (callFn : Index → BitVec COMPRESSION_INPUT_LENGTH) (S : Finset Index)
    (hinj : Set.InjOn callFn (S : Set Index)) {α : Type}
    (F : Compression → (Index → Digest) → ProbComp α) :
    𝒟[do let leafRand ← $ᵗ (Index → Digest)
         let table ← $ᵗ Compression
         F (reprogramFinset callFn table leafRand S) leafRand] =
    𝒟[do let leafRand ← $ᵗ (Index → Digest)
         let table ← $ᵗ Compression
         F table (fun i => if i ∈ S then fromOut (table (callFn i)) else leafRand i)] := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
    apply _root_.evalDist_bind_congr; intro leafRand
    apply _root_.evalDist_bind_congr; intro table
    have h1 : reprogramFinset callFn table leafRand ∅ = table := by
      funext x; exact reprogramFinset_not_mem callFn _ _ ∅ x (by simp)
    have h2 : (fun i => if i ∈ (∅ : Finset Index) then fromOut (table (callFn i)) else leafRand i) = leafRand := by
      funext i; exact ite_eq_right_of_eq_false _ _ (eq_false (Finset.notMem_empty i))
    rw [h1]
    exact congrArg (fun lr => 𝒟[F table lr]) h2.symm
  | @insert a S ha ih =>
    have hinjS : Set.InjOn callFn (S : Set Index) :=
      hinj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
    let F' : Compression → (Index → Digest) → ProbComp α := fun tbl lr =>
      do let ans ← $ᵗ Digest
         F (Function.update tbl (callFn a) (toOut ans)) (Function.update lr a ans)
    have hlhs :
        𝒟[do let leafRand ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             F (reprogramFinset callFn table leafRand (insert a S)) leafRand] =
        𝒟[do let leafRand ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             F' (reprogramFinset callFn table leafRand S) leafRand] := by
      rw [← uniform_coordinate_bind a (fun leafRand =>
        ($ᵗ Compression) >>= fun table => F (reprogramFinset callFn table leafRand (insert a S)) leafRand)]
      apply _root_.evalDist_bind_congr; intro leafRand
      rw [distribution_bind_comm ($ᵗ Digest) ($ᵗ Compression)]
      apply _root_.evalDist_bind_congr; intro table
      apply _root_.evalDist_bind_congr; intro ans
      have hrep : reprogramFinset callFn table (Function.update leafRand a ans) (insert a S) =
          Function.update (reprogramFinset callFn table leafRand S) (callFn a) (toOut ans) := by
        rw [reprogramFinset_insert callFn _ _ a S hinj, Function.update_self]
        apply congrArg (fun f : Compression => Function.update f (callFn a) (toOut ans))
        funext x
        by_cases hS : ∃ i ∈ S, callFn i = x
        · obtain ⟨i, hi, rfl⟩ := hS
          rw [reprogramFinset_mem callFn _ _ S hinjS i hi,
            reprogramFinset_mem callFn _ _ S hinjS i hi,
            Function.update_of_ne (fun h => ha (by subst h; exact hi))]
        · rw [reprogramFinset_not_mem callFn _ _ S x (fun i hi heq => hS ⟨i, hi, heq⟩),
            reprogramFinset_not_mem callFn _ _ S x (fun i hi heq => hS ⟨i, hi, heq⟩)]
      simp only [hrep]
    rw [hlhs, ih hinjS F']
    apply _root_.evalDist_bind_congr; intro leafRand
    rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ Digest)]
    have hupd := compression_table_update_bind (callFn a)
      (fun table => F table (fun i => if i ∈ insert a S then fromOut (table (callFn i)) else leafRand i))
    rw [← hupd]
    apply _root_.evalDist_bind_congr; intro ans
    apply _root_.evalDist_bind_congr; intro table
    have hlr : Function.update (fun i => if i ∈ S then fromOut (table (callFn i)) else leafRand i) a ans =
        (fun i => if i ∈ insert a S then
          fromOut ((Function.update table (callFn a) (toOut ans)) (callFn i))
        else leafRand i) := by
      funext i
      by_cases hia : i = a
      · subst hia
        rw [Function.update_self, ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_insert_self i S)), Function.update_self]
        rfl
      · rw [Function.update_of_ne hia]
        by_cases hiS : i ∈ S
        · have hne : callFn i ≠ callFn a :=
            fun heq => hia (hinj (Finset.mem_insert_of_mem hiS) (Finset.mem_insert_self a S) heq)
          rw [ite_eq_left_of_eq_true _ _ (eq_true hiS),
            ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_insert_of_mem hiS)),
            Function.update_of_ne hne]
        · have hni : i ∉ insert a S := by
            intro hm; rcases Finset.mem_insert.mp hm with rfl | h'
            · exact hia rfl
            · exact hiS h'
          rw [ite_eq_right_of_eq_false _ _ (eq_false hiS),
            ite_eq_right_of_eq_false _ _ (eq_false hni)]
    exact congrArg (fun lr => 𝒟[F (Function.update table (callFn a) (toOut ans)) lr]) hlr

/-! ### 4. Union Bounds, `BadMidpoint`, `BadRand`, and Conditional `ObsHit` Bounds -/

private theorem prEvent_exists_finset_le_sum {α ι : Type} [DecidableEq ι]
    (comp : ProbComp α) (S : Finset ι) (P : ι → α → Prop) :
    prEvent ((fun a => ∃ i ∈ S, P i a) <$> comp) ≤
      ∑ i ∈ S, prEvent ((fun a => P i a) <$> comp) := by
  induction S using Finset.induction_on with
  | empty =>
    have hz : prEvent ((fun a => ∃ i ∈ (∅ : Finset ι), P i a) <$> comp) = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ ⟨i, hi, _⟩ => Finset.notMem_empty i hi)
    rw [hz]; simp
  | @insert x S hx ih =>
    rw [Finset.sum_insert hx]
    have hsplit : prEvent ((fun a => ∃ i ∈ insert x S, P i a) <$> comp) ≤
        prEvent ((fun a => P x a) <$> comp) + prEvent ((fun a => ∃ i ∈ S, P i a) <$> comp) := by
      refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_or_le comp (P x) (fun a => ∃ i ∈ S, P i a))
      intro a _ ⟨i, hi, hpa⟩
      rcases Finset.mem_insert.mp hi with rfl | hiS
      · exact Or.inl hpa
      · exact Or.inr ⟨i, hiS, hpa⟩
    exact hsplit.trans (add_le_add le_rfl ih)

private theorem prEvent_exists_le_sum {α ι : Type} [Fintype ι] [DecidableEq ι]
    (comp : ProbComp α) (P : ι → α → Prop) :
    prEvent ((fun a => ∃ i : ι, P i a) <$> comp) ≤ ∑ i : ι, prEvent ((fun a => P i a) <$> comp) := by
  have hle : prEvent ((fun a => ∃ i : ι, P i a) <$> comp) ≤
      prEvent ((fun a => ∃ i ∈ (Finset.univ : Finset ι), P i a) <$> comp) :=
    prEvent_mono_of_support _ _ _ (fun _ _ ⟨i, h⟩ => ⟨i, Finset.mem_univ i, h⟩)
  exact hle.trans (prEvent_exists_finset_le_sum comp Finset.univ P)

private theorem prEvent_uniform_eq_target {α : Type} [Fintype α] [DecidableEq α] [SampleableType α]
    (target : α) :
    prEvent ((fun x : α => x = target) <$> ($ᵗ α)) = (1 : ENNReal) / Fintype.card α := by
  rw [SampleableType.prEvent_uniformSample]
  have hfilt : (Finset.univ.filter (fun x : α => x = target)).card = 1 := by
    rw [Finset.filter_eq', ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_univ _)), Finset.card_singleton]
  rw [hfilt, Nat.cast_one]

private theorem prEvent_uniform_coord_le {D R : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (i0 : D) (p : R → Prop) {ε : ENNReal} (hp : prEvent (p <$> ($ᵗ R)) ≤ ε) :
    prEvent ((fun f : D → R => p (f i0)) <$> ($ᵗ (D → R))) ≤ ε := by
  rw [map_eq_bind_pure_comp, ← id_map (x := ($ᵗ (D → R)) >>= _)]
  change prEvent (id <$> (do let values ← $ᵗ (D → R); pure (p (values i0)))) ≤ ε
  have hswap := (EvalDistEq.of_evalDist_eq
    (uniform_coordinate_bind (D := D) (R := R) i0 (fun f => pure (p (f i0))))).prEvent_eq id
  rw [← hswap]
  apply prEvent_bind_le_of_forall_le_of_support
  intro f _
  have hev : (do let fresh ← $ᵗ R; pure (p (Function.update f i0 fresh i0))) = (p <$> ($ᵗ R)) := by
    simp only [Function.update_self, map_eq_bind_pure_comp]; rfl
  rw [hev, prEvent_map]
  exact hp


private theorem pairSaltEven_uniform_target (t : Salt192) :
    prEvent ((fun r : PairRand => pairSaltEven r = t) <$> ($ᵗ PairRand)) ≤ (1 : ENNReal) / 2 ^ 192 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hinj : Set.InjOn pairSR
      ((Finset.univ.filter (fun r : PairRand => pairSaltEven r = t)) : Set PairRand) := by
    intro a ha b hb hsr
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have hsm : pairSM a = pairSM b := by
      have heq := ha.2.trans hb.2.symm
      rw [pairSaltEven_eq, pairSaltEven_eq] at heq
      have := congrArg (fun v : Salt192 => v.extractLsb' 128 64) heq
      simpa only [BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 128), Nat.sub_self,
        BitVec.extractLsb'_eq_self] using this
    have hsl : pairSL a = pairSL b := by
      have heq := ha.2.trans hb.2.symm
      rw [pairSaltEven_eq, pairSaltEven_eq] at heq
      have := congrArg (fun v : Salt192 => v.extractLsb' 0 128) heq
      simpa only [BitVec.extractLsb'_append_eq_right] using this
    rw [pairRand_eq_parts a, pairRand_eq_parts b, hsr, hsm, hsl]
  have hcard : (Finset.univ.filter (fun r : PairRand => pairSaltEven r = t)).card ≤ 2 ^ 128 := by
    calc
      (Finset.univ.filter (fun r : PairRand => pairSaltEven r = t)).card
        ≤ (Finset.univ : Finset (BitVec 128)).card :=
          Finset.card_le_card_of_injOn pairSR (fun _ _ => Finset.mem_univ _) hinj
      _ = 2 ^ 128 := by rw [Finset.card_univ, Fintype.card_bitVec]
  rw [Fintype.card_bitVec 320]
  calc
    ((Finset.univ.filter (fun r : PairRand => pairSaltEven r = t)).card : ENNReal) / (2 ^ 320 : Nat)
      ≤ ((2 ^ 128 : Nat) : ENNReal) / (2 ^ 320 : Nat) := ENNReal.div_le_div_right (Nat.cast_le.mpr hcard) _
    _ = 1 / 2 ^ 192 := by
        simp only [Nat.cast_pow, Nat.cast_ofNat]
        rw [show (2 : ENNReal) ^ 320 = 2 ^ 128 * 2 ^ 192 by rw [← pow_add],
          ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (pow_ne_zero 128 two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
          mul_comm ((2 : ENNReal) ^ 128)⁻¹, mul_assoc,
          ENNReal.inv_mul_cancel (pow_ne_zero 128 two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
          mul_one, one_div]


private theorem pairSaltOdd_uniform_target (t : Salt192) :
    prEvent ((fun r : PairRand => pairSaltOdd r = t) <$> ($ᵗ PairRand)) ≤ (1 : ENNReal) / 2 ^ 192 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hinj : Set.InjOn pairSL
      ((Finset.univ.filter (fun r : PairRand => pairSaltOdd r = t)) : Set PairRand) := by
    intro a ha b hb hsl
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have hsr : pairSR a = pairSR b := by
      have heq := ha.2.trans hb.2.symm
      rw [pairSaltOdd_eq, pairSaltOdd_eq] at heq
      have := congrArg (fun v : Salt192 => v.extractLsb' 64 128) heq
      simpa only [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64), Nat.sub_self,
        BitVec.extractLsb'_eq_self] using this
    have hsm : pairSM a = pairSM b := by
      have heq := ha.2.trans hb.2.symm
      rw [pairSaltOdd_eq, pairSaltOdd_eq] at heq
      have := congrArg (fun v : Salt192 => v.extractLsb' 0 64) heq
      simpa only [BitVec.extractLsb'_append_eq_right] using this
    rw [pairRand_eq_parts a, pairRand_eq_parts b, hsr, hsm, hsl]
  have hcard : (Finset.univ.filter (fun r : PairRand => pairSaltOdd r = t)).card ≤ 2 ^ 128 := by
    calc
      (Finset.univ.filter (fun r : PairRand => pairSaltOdd r = t)).card
        ≤ (Finset.univ : Finset (BitVec 128)).card :=
          Finset.card_le_card_of_injOn pairSL (fun _ _ => Finset.mem_univ _) hinj
      _ = 2 ^ 128 := by rw [Finset.card_univ, Fintype.card_bitVec]
  rw [Fintype.card_bitVec 320]
  calc
    ((Finset.univ.filter (fun r : PairRand => pairSaltOdd r = t)).card : ENNReal) / (2 ^ 320 : Nat)
      ≤ ((2 ^ 128 : Nat) : ENNReal) / (2 ^ 320 : Nat) := ENNReal.div_le_div_right (Nat.cast_le.mpr hcard) _
    _ = 1 / 2 ^ 192 := by
        simp only [Nat.cast_pow, Nat.cast_ofNat]
        rw [show (2 : ENNReal) ^ 320 = 2 ^ 128 * 2 ^ 192 by rw [← pow_add],
          ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (pow_ne_zero 128 two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
          mul_comm ((2 : ENNReal) ^ 128)⁻¹, mul_assoc,
          ENNReal.inv_mul_cancel (pow_ne_zero 128 two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
          mul_one, one_div]


theorem pairSalts_target_le (i : Index) (t : Salt192) :
    prEvent ((fun rand : PairIdx → PairRand => pairSalts rand i = t) <$> ($ᵗ (PairIdx → PairRand))) ≤
      (1 : ENNReal) / 2 ^ 192 := by
  unfold pairSalts
  dsimp only
  split_ifs
  · exact prEvent_uniform_coord_le (D := PairIdx) (R := PairRand) (pairOf i)
      (fun r => pairSaltEven r = t) (pairSaltEven_uniform_target t)
  · exact prEvent_uniform_coord_le (D := PairIdx) (R := PairRand) (pairOf i)
      (fun r => pairSaltOdd r = t) (pairSaltOdd_uniform_target t)

private theorem prEvent_map_eq_id_bind {α : Type} (mx : ProbComp α) (P : α → Prop) :
    prEvent (P <$> mx) = prEvent (id <$> (mx >>= fun a => pure (P a))) := by
  have h : (mx >>= fun a => pure (P a)) = (P <$> mx) := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [h, prEvent_map]; rfl

private theorem prEvent_uniform_coord_cond_le {D R : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (i0 : D) (P : (D → R) → Prop) {ε : ENNReal}
    (hP : ∀ f : D → R, prEvent ((fun r : R => P (Function.update f i0 r)) <$> ($ᵗ R)) ≤ ε) :
    prEvent (P <$> ($ᵗ (D → R))) ≤ ε := by
  rw [prEvent_map_eq_id_bind]
  have hswap := (EvalDistEq.of_evalDist_eq
    (uniform_coordinate_bind (D := D) (R := R) i0 (fun f => pure (P f)))).prEvent_eq id
  rw [← hswap]
  apply prEvent_bind_le_of_forall_le; intro f
  have hev : (do let r ← $ᵗ R; pure (P (Function.update f i0 r))) =
      ((fun r : R => P (Function.update f i0 r)) <$> ($ᵗ R)) := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [hev, prEvent_map]
  exact hP f

private theorem prEvent_prod_fst_le {A B : Type} [SampleableType A] [SampleableType B]
    (P : A → Prop) {ε : ENNReal} (hP : prEvent (P <$> ($ᵗ A)) ≤ ε) :
    prEvent ((fun p : A × B => P p.1) <$> ($ᵗ (A × B))) ≤ ε := by
  have hp : 𝒟[(fun p : A × B => P p.1) <$> ($ᵗ (A × B))] = 𝒟[P <$> ($ᵗ A)] := by
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    change 𝒟[($ᵗ (A × B)) >>= fun p => pure (P p.1)] = 𝒟[($ᵗ A) >>= fun a => pure (P a)]
    rw [← prod_uniform_bind (fun p : A × B => pure (P p.1))]
    apply _root_.evalDist_bind_congr; intro a
    exact OracleComp.evalDist_bind_const ($ᵗ B) (pure (P a))
  have hpr := (EvalDistEq.of_evalDist_eq hp).prEvent_eq id
  rw [prEvent_map, prEvent_map] at hpr
  exact (le_of_eq hpr).trans hP

private theorem prEvent_prod_snd_le {A B : Type} [SampleableType A] [SampleableType B]
    (P : B → Prop) {ε : ENNReal} (hP : prEvent (P <$> ($ᵗ B)) ≤ ε) :
    prEvent ((fun p : A × B => P p.2) <$> ($ᵗ (A × B))) ≤ ε := by
  have hp : 𝒟[(fun p : A × B => P p.2) <$> ($ᵗ (A × B))] = 𝒟[P <$> ($ᵗ B)] := by
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    change 𝒟[($ᵗ (A × B)) >>= fun p => pure (P p.2)] = 𝒟[($ᵗ B) >>= fun b => pure (P b)]
    rw [← prod_uniform_bind (fun p : A × B => pure (P p.2))]
    exact OracleComp.evalDist_bind_const ($ᵗ A) (($ᵗ B) >>= fun b => pure (P b))
  have hpr := (EvalDistEq.of_evalDist_eq hp).prEvent_eq id
  rw [prEvent_map, prEvent_map] at hpr
  exact (le_of_eq hpr).trans hP

private theorem prEvent_bind_fst_mid_snd {A B C : Type}
    [SampleableType A] [SampleableType B] [SampleableType C]
    (P : B → Prop) {ε : ENNReal} (hP : prEvent (P <$> ($ᵗ B)) ≤ ε) :
    prEvent (id <$> (do let _ ← $ᵗ A; let b ← $ᵗ B; let _ ← $ᵗ C; pure (P b))) ≤ ε := by
  apply prEvent_bind_le_of_forall_le; intro _
  have h : 𝒟[do let b ← $ᵗ B; let _ ← $ᵗ C; pure (P b)] = 𝒟[P <$> ($ᵗ B)] := by
    rw [map_eq_bind_pure_comp]
    apply _root_.evalDist_bind_congr; intro b
    exact OracleComp.evalDist_bind_const ($ᵗ C) (pure (P b))
  have hpr := (EvalDistEq.of_evalDist_eq h).prEvent_eq id
  rw [prEvent_map] at hpr
  exact (le_of_eq hpr).trans hP

theorem hiddenCall3_eq_fixed_le (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (aVec bVec : Index → Digest) (i : Index) (x : BitVec COMPRESSION_INPUT_LENGTH) :
    prEvent ((fun rand : PairIdx → PairRand => hiddenCall3 h768 aVec bVec (pairSalts rand) i = x) <$>
      ($ᵗ (PairIdx → PairRand))) ≤ (1 : ENNReal) / 2 ^ 192 := by
  by_cases he : i.val % 2 = 0
  · refine (prEvent_mono_of_support _ _ _ ?_).trans (pairSalts_target_le i (x.extractLsb' 576 192))
    intro rand _ heq
    have hc := congrArg (fun v : BitVec COMPRESSION_INPUT_LENGTH => v.extractLsb' 576 192) heq
    unfold hiddenCall3 leafFinalInput at hc
    rw [extractLsb'_cast_eq, ite_eq_left_of_eq_true _ _ (eq_true he), leafFinalEven_salt] at hc
    exact hc
  · refine (prEvent_mono_of_support _ _ _ ?_).trans (pairSalts_target_le i (x.extractLsb' 0 192))
    intro rand _ heq
    have hc := congrArg (fun v : BitVec COMPRESSION_INPUT_LENGTH => v.extractLsb' 0 192) heq
    unfold hiddenCall3 leafFinalInput at hc
    rw [extractLsb'_cast_eq, ite_eq_right_of_eq_false _ _ (eq_false he), leafFinalOdd_salt] at hc
    exact hc

/-- For ANY two distinct indices `i ≠ i'`, `Pr_{rand}[hiddenCall3 i = hiddenCall3 i'] ≤ 1 / 2^192`!
Handles BOTH same-pair (`pairOf i = pairOf i'`, opposite parity!) and different-pair (`pairOf i ≠ pairOf i'`). -/
theorem hiddenCall3_pair_collision_le (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (aVec bVec : Index → Digest) (i i' : Index) (hne : i ≠ i') :
    prEvent ((fun rand : PairIdx → PairRand =>
      hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
      ($ᵗ (PairIdx → PairRand))) ≤ (1 : ENNReal) / 2 ^ 192 := by
  by_cases hpair : pairOf i = pairOf i'
  · -- Same pair, distinct indices => one is even and the other is odd!
    by_cases he : i.val % 2 = 0
    · have ho' : i'.val % 2 ≠ 0 := by
        intro he'
        apply hne
        have hv : i.val / 2 = i'.val / 2 := congrArg Fin.val hpair
        exact Fin.ext (by omega)
      -- Even `i` has high 192 bits = `pairSalts rand i`; odd `i'` has high 192 bits = `(bVec i')[64..256)`!
      refine (prEvent_mono_of_support _ _ _ ?_).trans (pairSalts_target_le i ((bVec i').extractLsb' 64 192))
      intro rand _ heq
      have hc := congrArg (fun v : BitVec COMPRESSION_INPUT_LENGTH => v.extractLsb' 576 192) heq
      unfold hiddenCall3 leafFinalInput at hc
      rw [extractLsb'_cast_eq, extractLsb'_cast_eq,
        ite_eq_left_of_eq_true _ _ (eq_true he), ite_eq_right_of_eq_false _ _ (eq_false ho'),
        leafFinalEven_salt] at hc
      have hodd576 : (leafFinalOdd (aVec i') (bVec i') (pairSalts rand i')).extractLsb' 576 192 =
          (bVec i').extractLsb' 64 192 := by
        apply BitVec.eq_of_getLsbD_eq; intro b hb
        unfold leafFinalOdd
        simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and,
          show ¬ (576 + b < 192) by omega, show ¬ (576 + b - 192 < 64) by omega,
          show ¬ (576 + b - 192 - 64 < 256) by omega, ite_false,
          show 576 + b - 192 - 64 - 256 = 64 + b by omega]
      rwa [hodd576] at hc
    · have he' : i'.val % 2 = 0 := by
        by_contra ho'
        apply hne
        have hv : i.val / 2 = i'.val / 2 := congrArg Fin.val hpair
        exact Fin.ext (by omega)
      -- Odd `i` has low 192 bits = `pairSalts rand i`; even `i'` has low 192 bits = `(aVec i')[0..192)`!
      refine (prEvent_mono_of_support _ _ _ ?_).trans (pairSalts_target_le i ((aVec i').extractLsb' 0 192))
      intro rand _ heq
      have hc := congrArg (fun v : BitVec COMPRESSION_INPUT_LENGTH => v.extractLsb' 0 192) heq
      unfold hiddenCall3 leafFinalInput at hc
      rw [extractLsb'_cast_eq, extractLsb'_cast_eq,
        ite_eq_right_of_eq_false _ _ (eq_false he), ite_eq_left_of_eq_true _ _ (eq_true he'),
        leafFinalOdd_salt] at hc
      have heven0 : (leafFinalEven (aVec i') (bVec i') (pairSalts rand i')).extractLsb' 0 192 =
          (aVec i').extractLsb' 0 192 := by
        unfold leafFinalEven; exact extractLsb'_0_192_append_digest _ _
      rwa [heven0] at hc
  · -- Different pairs: resample `rand (pairOf i)` while keeping `rand (pairOf i')` fixed!
    apply prEvent_uniform_coord_cond_le (D := PairIdx) (R := PairRand) (pairOf i)
    intro rand
    have hfixed : ∀ r : PairRand,
        hiddenCall3 h768 aVec bVec (pairSalts (Function.update rand (pairOf i) r)) i' =
          hiddenCall3 h768 aVec bVec (pairSalts rand) i' := by
      intro r
      have hps : pairSalts (Function.update rand (pairOf i) r) i' = pairSalts rand i' := by
        unfold pairSalts
        change (if i'.val % 2 = 0 then pairSaltEven (Function.update rand (pairOf i) r (pairOf i'))
                else pairSaltOdd (Function.update rand (pairOf i) r (pairOf i'))) = _
        rw [Function.update_of_ne (Ne.symm hpair)]
        rfl
      unfold hiddenCall3; rw [hps]
    simp only [hfixed]
    let target := hiddenCall3 h768 aVec bVec (pairSalts rand) i'
    by_cases he : i.val % 2 = 0
    · refine (prEvent_mono_of_support _ _ _ ?_).trans (pairSaltEven_uniform_target (target.extractLsb' 576 192))
      intro r _ heq
      have hlhs : (hiddenCall3 h768 aVec bVec (pairSalts (Function.update rand (pairOf i) r)) i).extractLsb' 576 192 =
          pairSaltEven r := by
        unfold hiddenCall3 leafFinalInput pairSalts
        rw [extractLsb'_cast_eq, ite_eq_left_of_eq_true _ _ (eq_true he), leafFinalEven_salt,
          ite_eq_left_of_eq_true _ _ (eq_true he)]
        exact congrArg pairSaltEven (Function.update_self (pairOf i) r rand)
      exact hlhs.symm.trans (congrArg (fun v : BitVec COMPRESSION_INPUT_LENGTH => v.extractLsb' 576 192) heq)
    · refine (prEvent_mono_of_support _ _ _ ?_).trans (pairSaltOdd_uniform_target (target.extractLsb' 0 192))
      intro r _ heq
      have hlhs : (hiddenCall3 h768 aVec bVec (pairSalts (Function.update rand (pairOf i) r)) i).extractLsb' 0 192 =
          pairSaltOdd r := by
        unfold hiddenCall3 leafFinalInput pairSalts
        rw [extractLsb'_cast_eq, ite_eq_right_of_eq_false _ _ (eq_false he), leafFinalOdd_salt,
          ite_eq_right_of_eq_false _ _ (eq_false he)]
        exact congrArg pairSaltOdd (Function.update_self (pairOf i) r rand)
      exact hlhs.symm.trans (congrArg (fun v : BitVec COMPRESSION_INPUT_LENGTH => v.extractLsb' 0 192) heq)


/-- Midpoint bad event: some 64-bit value appears in 5 or more pairs of `sM`. -/
def BadMidpoint (sM : PairIdx → BitVec 64) : Prop :=
  ∃ m : BitVec 64, 5 ≤ (Finset.univ.filter (fun j : PairIdx => sM j = m)).card

private theorem five_distinct_of_card_ge_five {α : Type} [DecidableEq α] {S : Finset α}
    (h : 5 ≤ S.card) :
    ∃ a0 a1 a2 a3 a4 : α, a0 ∈ S ∧ a1 ∈ S ∧ a2 ∈ S ∧ a3 ∈ S ∧ a4 ∈ S ∧
      a0 ≠ a1 ∧ a0 ≠ a2 ∧ a0 ≠ a3 ∧ a0 ≠ a4 ∧
      a1 ≠ a2 ∧ a1 ≠ a3 ∧ a1 ≠ a4 ∧
      a2 ≠ a3 ∧ a2 ≠ a4 ∧ a3 ≠ a4 := by
  have h0 : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a0, ha0⟩ := h0
  let S1 := S.erase a0
  have hc1 : 4 ≤ S1.card := by dsimp only [S1]; rw [Finset.card_erase_of_mem ha0]; omega
  obtain ⟨a1, ha1⟩ := Finset.card_pos.mp (by omega : 0 < S1.card)
  let S2 := S1.erase a1
  have hc2 : 3 ≤ S2.card := by dsimp only [S2]; rw [Finset.card_erase_of_mem ha1]; omega
  obtain ⟨a2, ha2⟩ := Finset.card_pos.mp (by omega : 0 < S2.card)
  let S3 := S2.erase a2
  have hc3 : 2 ≤ S3.card := by dsimp only [S3]; rw [Finset.card_erase_of_mem ha2]; omega
  obtain ⟨a3, ha3⟩ := Finset.card_pos.mp (by omega : 0 < S3.card)
  let S4 := S3.erase a3
  have hc4 : 1 ≤ S4.card := by dsimp only [S4]; rw [Finset.card_erase_of_mem ha3]; omega
  obtain ⟨a4, ha4⟩ := Finset.card_pos.mp (by omega : 0 < S4.card)
  have m1 := Finset.mem_erase.mp ha1
  have m2 := Finset.mem_erase.mp ha2
  have m2' := Finset.mem_erase.mp m2.2
  have m3 := Finset.mem_erase.mp ha3
  have m3' := Finset.mem_erase.mp m3.2
  have m3'' := Finset.mem_erase.mp m3'.2
  have m4 := Finset.mem_erase.mp ha4
  have m4' := Finset.mem_erase.mp m4.2
  have m4'' := Finset.mem_erase.mp m4'.2
  have m4''' := Finset.mem_erase.mp m4''.2
  exact ⟨a0, a1, a2, a3, a4, ha0, m1.2, m2'.2, m3''.2, m4'''.2,
    Ne.symm m1.1, Ne.symm m2'.1, Ne.symm m3''.1, Ne.symm m4'''.1,
    Ne.symm m2.1, Ne.symm m3'.1, Ne.symm m4''.1,
    Ne.symm m3.1, Ne.symm m4'.1, Ne.symm m4.1⟩


private theorem prEvent_uniform_bv64_eq_and (t : BitVec 64) (q : ProbComp Prop) {r : ENNReal}
    (hq : prEvent (id <$> q) ≤ r) :
    prEvent (id <$> (do let v ← $ᵗ BitVec 64; let p ← q; pure (v = t ∧ p))) ≤
      ((1 : ENNReal) / 2 ^ 64) * r := by
  rw [prEvent_bind_eq_sum_fintype]
  have hterm : ∀ v : BitVec 64,
      Pr{let x ← $ᵗ BitVec 64}[x = v] *
        prEvent (id <$> (do let p ← q; pure (v = t ∧ p))) ≤
      (if v = t then ((1 : ENNReal) / 2 ^ 64) * r else 0) := by
    intro v
    by_cases hv : v = t
    · subst hv
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      have hv1 : Pr{let x ← $ᵗ BitVec 64}[x = v] = (1 : ENNReal) / 2 ^ 64 := by
        have h := prEvent_uniform_eq_target (α := BitVec 64) v
        rw [Fintype.card_bitVec 64, Nat.cast_pow, Nat.cast_ofNat] at h
        exact h
      have hq' : prEvent (id <$> (do let p ← q; pure (v = v ∧ p))) ≤ r := by
        have heq : (do let p ← q; pure (v = v ∧ p)) = q := by
          rw [show (fun p : Prop => (pure (v = v ∧ p) : ProbComp Prop)) = pure from
            funext (fun p => congrArg pure (propext ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩)), bind_pure]
        rw [heq]; exact hq
      rw [hv1]
      exact mul_le_mul_of_nonneg_left hq' zero_le
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
      have hz : prEvent (id <$> (do let p ← q; pure (v = t ∧ p))) ≤ 0 := by
        apply prEvent_bind_le_of_forall_le; intro p
        rw [map_pure]
        exact (prEvent_pure_mono (Q := False) (fun h => hv h.1)).trans
          (le_of_eq (by rw [prEvent_pure_prop, ite_eq_right_of_eq_false _ _ (eq_false not_false)]))
      exact (mul_le_mul_of_nonneg_left hz zero_le).trans (le_of_eq (mul_zero _))
  refine (Finset.sum_le_sum (fun v _ => hterm v)).trans ?_
  rw [Finset.sum_eq_single t
    (fun v _ hne => ite_eq_right_of_eq_false _ _ (eq_false hne))
    (fun h => (h (Finset.mem_univ t)).elim),
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]


private theorem four_eq_64_le {D : Type} [DecidableEq D] [Finite D]
    [SampleableType (D → BitVec 64)] (j0 j1 j2 j3 j4 : D)
    (h01 : j0 ≠ j1) (h02 : j0 ≠ j2) (h03 : j0 ≠ j3) (h04 : j0 ≠ j4)
    (h12 : j1 ≠ j2) (h13 : j1 ≠ j3) (h14 : j1 ≠ j4)
    (h23 : j2 ≠ j3) (h24 : j2 ≠ j4) (h34 : j3 ≠ j4) :
    prEvent ((fun sM : D → BitVec 64 =>
      sM j1 = sM j0 ∧ sM j2 = sM j0 ∧ sM j3 = sM j0 ∧ sM j4 = sM j0) <$>
      ($ᵗ (D → BitVec 64))) ≤ (1 : ENNReal) / 2 ^ 256 := by
  let P (f : D → BitVec 64) : Prop :=
    f j1 = f j0 ∧ f j2 = f j0 ∧ f j3 = f j0 ∧ f j4 = f j0
  let c0 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => pure (P f)
  let c1 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => ($ᵗ BitVec 64) >>= fun v1 =>
    pure (P (Function.update f j1 v1))
  let c2 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => ($ᵗ BitVec 64) >>= fun v2 =>
    ($ᵗ BitVec 64) >>= fun v1 => pure (P (Function.update (Function.update f j2 v2) j1 v1))
  let c3 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => ($ᵗ BitVec 64) >>= fun v3 =>
    ($ᵗ BitVec 64) >>= fun v2 => ($ᵗ BitVec 64) >>= fun v1 =>
    pure (P (Function.update (Function.update (Function.update f j3 v3) j2 v2) j1 v1))
  let c4 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => ($ᵗ BitVec 64) >>= fun v4 =>
    ($ᵗ BitVec 64) >>= fun v3 => ($ᵗ BitVec 64) >>= fun v2 => ($ᵗ BitVec 64) >>= fun v1 =>
    pure (P (Function.update (Function.update (Function.update (Function.update f j4 v4) j3 v3) j2 v2) j1 v1))
  let q0 : ProbComp Prop := pure True
  let q1 (t : BitVec 64) : ProbComp Prop := ($ᵗ BitVec 64) >>= fun v1 => q0 >>= fun p0 => pure (v1 = t ∧ p0)
  let q2 (t : BitVec 64) : ProbComp Prop := ($ᵗ BitVec 64) >>= fun v2 => q1 t >>= fun p1 => pure (v2 = t ∧ p1)
  let q3 (t : BitVec 64) : ProbComp Prop := ($ᵗ BitVec 64) >>= fun v3 => q2 t >>= fun p2 => pure (v3 = t ∧ p2)
  let q4 (t : BitVec 64) : ProbComp Prop := ($ᵗ BitVec 64) >>= fun v4 => q3 t >>= fun p3 => pure (v4 = t ∧ p3)
  let c5 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => q4 (f j0)
  rw [prEvent_map_eq_id_bind]
  change prEvent (id <$> c0) ≤ _
  have h1 : 𝒟[c0] = 𝒟[c1] :=
    (uniform_coordinate_bind (D := D) (R := BitVec 64) j1 (fun f => pure (P f))).symm
  have h2 : 𝒟[c1] = 𝒟[c2] :=
    (uniform_coordinate_bind (D := D) (R := BitVec 64) j2 (fun f =>
      ($ᵗ BitVec 64) >>= fun v1 => pure (P (Function.update f j1 v1)))).symm
  have h3 : 𝒟[c2] = 𝒟[c3] :=
    (uniform_coordinate_bind (D := D) (R := BitVec 64) j3 (fun f =>
      ($ᵗ BitVec 64) >>= fun v2 => ($ᵗ BitVec 64) >>= fun v1 =>
        pure (P (Function.update (Function.update f j2 v2) j1 v1)))).symm
  have h4 : 𝒟[c3] = 𝒟[c4] :=
    (uniform_coordinate_bind (D := D) (R := BitVec 64) j4 (fun f =>
      ($ᵗ BitVec 64) >>= fun v3 => ($ᵗ BitVec 64) >>= fun v2 => ($ᵗ BitVec 64) >>= fun v1 =>
        pure (P (Function.update (Function.update (Function.update f j3 v3) j2 v2) j1 v1)))).symm
  have h5 : 𝒟[c4] = 𝒟[c5] := by
    dsimp only [c4, c5, q4, q3, q2, q1, q0]
    apply _root_.evalDist_bind_congr; intro f
    apply _root_.evalDist_bind_congr; intro v4
    simp only [bind_assoc, pure_bind]
    apply _root_.evalDist_bind_congr; intro v3
    apply _root_.evalDist_bind_congr; intro v2
    apply _root_.evalDist_bind_congr; intro v1
    simp only [P, Function.update_self, Function.update_of_ne h01, Function.update_of_ne h02,
      Function.update_of_ne h03, Function.update_of_ne h04,
      Function.update_of_ne (Ne.symm h12), Function.update_of_ne (Ne.symm h13),
      Function.update_of_ne (Ne.symm h14), Function.update_of_ne (Ne.symm h23),
      Function.update_of_ne (Ne.symm h24), Function.update_of_ne (Ne.symm h34)]
    exact congrArg (fun q : Prop => 𝒟[(pure q : ProbComp Prop)])
      (propext ⟨fun ⟨a, b, c, d⟩ => ⟨d, c, b, a, trivial⟩, fun ⟨d, c, b, a, _⟩ => ⟨a, b, c, d⟩⟩)
  have hchain := h1.trans (h2.trans (h3.trans (h4.trans h5)))
  rw [(EvalDistEq.of_evalDist_eq hchain).prEvent_eq id]
  apply prEvent_bind_le_of_forall_le; intro f
  have h0 : prEvent (id <$> q0) ≤ 1 := by
    dsimp only [q0]
    rw [map_pure]
    change prEvent (pure True) ≤ 1
    rw [prEvent_pure_prop, ite_eq_left_of_eq_true _ _ (eq_true trivial)]
  have b1 := prEvent_uniform_bv64_eq_and (f j0) q0 h0
  have b2 := prEvent_uniform_bv64_eq_and (f j0) (q1 (f j0)) b1
  have b3 := prEvent_uniform_bv64_eq_and (f j0) (q2 (f j0)) b2
  have b4 := prEvent_uniform_bv64_eq_and (f j0) (q3 (f j0)) b3
  have hpow : ∀ a b : Nat, ((1 : ENNReal) / 2 ^ a) * ((1 : ENNReal) / 2 ^ b) = (1 : ENNReal) / 2 ^ (a + b) := fun a b => by
    rw [one_div, one_div, one_div, ← ENNReal.mul_inv (Or.inl (pow_ne_zero a two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), pow_add]
  refine b4.trans (le_of_eq ?_)
  rw [mul_one, hpow 64 64, hpow 64 (64 + 64), hpow 64 (64 + (64 + 64))]


theorem badMidpoint_le :
    prEvent ((fun sM : PairIdx → BitVec 64 => BadMidpoint sM) <$> ($ᵗ (PairIdx → BitVec 64))) ≤
      (((LENGTH / 2) ^ 5 : Nat) : ENNReal) / 2 ^ 256 := by
  let Tuple5 := PairIdx × PairIdx × PairIdx × PairIdx × PairIdx
  let distinct5 (q : Tuple5) : Prop :=
    let (j0, j1, j2, j3, j4) := q
    j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j0 ≠ j4 ∧
    j1 ≠ j2 ∧ j1 ≠ j3 ∧ j1 ≠ j4 ∧
    j2 ≠ j3 ∧ j2 ≠ j4 ∧ j3 ≠ j4
  let hit5 (q : Tuple5) (sM : PairIdx → BitVec 64) : Prop :=
    let (j0, j1, j2, j3, j4) := q
    distinct5 q ∧ sM j1 = sM j0 ∧ sM j2 = sM j0 ∧ sM j3 = sM j0 ∧ sM j4 = sM j0
  have hmono : prEvent ((fun sM => BadMidpoint sM) <$> ($ᵗ (PairIdx → BitVec 64))) ≤
      prEvent ((fun sM => ∃ q : Tuple5, hit5 q sM) <$> ($ᵗ (PairIdx → BitVec 64))) := by
    apply prEvent_mono_of_support
    intro sM _ ⟨m, hcard⟩
    obtain ⟨j0, j1, j2, j3, j4, m0, m1, m2, m3, m4, d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ :=
      five_distinct_of_card_ge_five hcard
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at m0 m1 m2 m3 m4
    exact ⟨(j0, j1, j2, j3, j4), ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩,
      m1.trans m0.symm, m2.trans m0.symm, m3.trans m0.symm, m4.trans m0.symm⟩
  refine hmono.trans ((prEvent_exists_le_sum ($ᵗ (PairIdx → BitVec 64)) hit5).trans ?_)
  have hterm : ∀ q : Tuple5, prEvent ((fun sM => hit5 q sM) <$> ($ᵗ (PairIdx → BitVec 64))) ≤
      (1 : ENNReal) / 2 ^ 256 := by
    rintro ⟨j0, j1, j2, j3, j4⟩
    by_cases hd : distinct5 (j0, j1, j2, j3, j4)
    · rcases hd with ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩
      exact (prEvent_mono_of_support _ _ _ (fun _ _ h => h.2)).trans
        (four_eq_64_le j0 j1 j2 j3 j4 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34)
    · have hz : prEvent ((fun sM => hit5 (j0, j1, j2, j3, j4) sM) <$> ($ᵗ (PairIdx → BitVec 64))) = 0 :=
        prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ h => hd h.1)
      rw [hz]; exact zero_le
  refine (Finset.sum_le_sum (fun q _ => hterm q)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  have hcard : Fintype.card Tuple5 = (LENGTH / 2) ^ 5 := by
    simp only [Tuple5, PairIdx, Fintype.card_prod, Fintype.card_fin]; ring
  rw [hcard]


theorem badMidpoint_pairRand_le :
    prEvent ((fun rand : PairIdx → PairRand => BadMidpoint (fun j => pairSM (rand j))) <$>
      ($ᵗ (PairIdx → PairRand))) ≤ (((LENGTH / 2) ^ 5 : Nat) : ENNReal) / 2 ^ 256 := by
  rw [prEvent_map_eq_id_bind]
  have hcb := (EvalDistEq.of_evalDist_eq
    (combinePairRand_uniform_bind (fun rand => pure (BadMidpoint (fun j => pairSM (rand j)))))).prEvent_eq id
  rw [← hcb]
  have hsimp : (do let sL ← $ᵗ (PairIdx → BitVec 128)
                   let sM ← $ᵗ (PairIdx → BitVec 64)
                   let sR ← $ᵗ (PairIdx → BitVec 128)
                   pure (BadMidpoint (fun j => pairSM (combinePairRand sL sM sR j)))) =
      (do let _ ← $ᵗ (PairIdx → BitVec 128)
          let sM ← $ᵗ (PairIdx → BitVec 64)
          let _ ← $ᵗ (PairIdx → BitVec 128)
          pure (BadMidpoint sM)) := by
    apply bind_congr; intro sL
    apply bind_congr; intro sM
    apply bind_congr; intro sR
    simp only [pairSM_combine]
  rw [hsimp]
  exact prEvent_bind_fst_mid_snd (A := PairIdx → BitVec 128) (B := PairIdx → BitVec 64)
    (C := PairIdx → BitVec 128) BadMidpoint badMidpoint_le


def hiddenOddSalts (positions : Positions) (salts : Index → Salt192) : Finset (BitVec 192) :=
  ((Finset.univ \ positions).filter (fun i : Index => i.val % 2 ≠ 0)).image salts

def hiddenEvenSalts (positions : Positions) (salts : Index → Salt192) : Finset (BitVec 192) :=
  ((Finset.univ \ positions).filter (fun i : Index => i.val % 2 = 0)).image salts

theorem hiddenOddSalts_card_le (positions : Positions) (salts : Index → Salt192) :
    (hiddenOddSalts positions salts).card ≤ LENGTH := by
  calc
    (hiddenOddSalts positions salts).card
      ≤ ((Finset.univ \ positions).filter (fun i : Index => i.val % 2 ≠ 0)).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset Index).card := Finset.card_le_card (Finset.subset_univ _)
    _ = LENGTH := by rw [Finset.card_univ]; exact Fintype.card_fin LENGTH

theorem hiddenEvenSalts_card_le (positions : Positions) (salts : Index → Salt192) :
    (hiddenEvenSalts positions salts).card ≤ LENGTH := by
  calc
    (hiddenEvenSalts positions salts).card
      ≤ ((Finset.univ \ positions).filter (fun i : Index => i.val % 2 = 0)).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset Index).card := Finset.card_le_card (Finset.subset_univ _)
    _ = LENGTH := by rw [Finset.card_univ]; exact Fintype.card_fin LENGTH

/-- Combined salt-only bad event for fixed `(cache1, aVec, bVec, positions)`. -/
def BadRand (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache1 : CompressionCache) (aVec bVec : Index → Digest)
    (positions : Positions) (rand : PairIdx → PairRand) : Prop :=
  BadMidpoint (fun j => pairSM (rand j)) ∨
  (∃ i ∉ positions, cache1 (hiddenCall3 h768 aVec bVec (pairSalts rand) i) ≠ none) ∨
  (∃ i ∉ positions, ∃ i' ∉ positions, i ≠ i' ∧
    hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') ∨
  (∃ i ∈ positions, ∃ i' ∉ positions,
    hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') ∨
  (∃ i ∉ positions, i.val % 2 = 0 ∧ pairSalts rand i = 0#192) ∨
  CacheHitsSlice192 0 cache1 (hiddenOddSalts positions (pairSalts rand)) ∨
  CacheHitsSlice192 64 cache1 (hiddenEvenSalts positions (pairSalts rand))

private theorem badRand_t2_le (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache1 : CompressionCache) (keys1 : Finset (BitVec COMPRESSION_INPUT_LENGTH))
    (covered : ∀ k, cache1 k ≠ none → k ∈ keys1)
    (aVec bVec : Index → Digest) (positions : Positions) :
    prEvent ((fun rand : PairIdx → PairRand =>
      ∃ i ∉ positions, cache1 (hiddenCall3 h768 aVec bVec (pairSalts rand) i) ≠ none) <$>
      ($ᵗ (PairIdx → PairRand))) ≤
      ((keys1.card * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  let S2 : Finset (BitVec COMPRESSION_INPUT_LENGTH × Index) := keys1 ×ˢ (Finset.univ : Finset Index)
  have hle : prEvent ((fun rand : PairIdx → PairRand =>
        ∃ i ∉ positions, cache1 (hiddenCall3 h768 aVec bVec (pairSalts rand) i) ≠ none) <$>
        ($ᵗ (PairIdx → PairRand))) ≤
      prEvent ((fun rand : PairIdx → PairRand => ∃ p ∈ S2,
        hiddenCall3 h768 aVec bVec (pairSalts rand) p.2 = p.1) <$> ($ᵗ (PairIdx → PairRand))) := by
    apply prEvent_mono_of_support
    intro rand _ ⟨i, _, hne⟩
    exact ⟨(hiddenCall3 h768 aVec bVec (pairSalts rand) i, i),
      Finset.mem_product.mpr ⟨covered _ hne, Finset.mem_univ i⟩, rfl⟩
  have hsum : prEvent ((fun rand : PairIdx → PairRand => ∃ p ∈ S2,
        hiddenCall3 h768 aVec bVec (pairSalts rand) p.2 = p.1) <$> ($ᵗ (PairIdx → PairRand))) ≤
      ∑ p ∈ S2, prEvent ((fun rand : PairIdx → PairRand =>
        hiddenCall3 h768 aVec bVec (pairSalts rand) p.2 = p.1) <$> ($ᵗ (PairIdx → PairRand))) :=
    prEvent_exists_finset_le_sum ($ᵗ (PairIdx → PairRand)) S2
      (fun p rand => hiddenCall3 h768 aVec bVec (pairSalts rand) p.2 = p.1)
  have hbd : ∑ p ∈ S2, prEvent ((fun rand : PairIdx → PairRand =>
        hiddenCall3 h768 aVec bVec (pairSalts rand) p.2 = p.1) <$> ($ᵗ (PairIdx → PairRand))) ≤
      ∑ _p ∈ S2, ((1 : ENNReal) / 2 ^ 192) :=
    Finset.sum_le_sum (fun p _ => hiddenCall3_eq_fixed_le h768 aVec bVec p.2 p.1)
  refine hle.trans (hsum.trans (hbd.trans ?_))
  rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

private theorem badRand_pairColl_le (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (aVec bVec : Index → Digest) :
    prEvent ((fun rand : PairIdx → PairRand => ∃ i : Index, ∃ i' : Index, i ≠ i' ∧
      hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
      ($ᵗ (PairIdx → PairRand))) ≤
      ((LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  have houter : prEvent ((fun rand : PairIdx → PairRand => ∃ i : Index, ∃ i' : Index, i ≠ i' ∧
        hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
        ($ᵗ (PairIdx → PairRand))) ≤
      ∑ i : Index, prEvent ((fun rand : PairIdx → PairRand => ∃ i' : Index, i ≠ i' ∧
        hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
        ($ᵗ (PairIdx → PairRand))) :=
    prEvent_exists_le_sum (ι := Index) ($ᵗ (PairIdx → PairRand))
      (fun i rand => ∃ i' : Index, i ≠ i' ∧
        hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i')
  have hrow : ∀ i : Index, prEvent ((fun rand : PairIdx → PairRand => ∃ i' : Index, i ≠ i' ∧
      hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
      ($ᵗ (PairIdx → PairRand))) ≤ (LENGTH : ENNReal) / 2 ^ 192 := by
    intro i
    have hinner : prEvent ((fun rand : PairIdx → PairRand => ∃ i' : Index, i ≠ i' ∧
          hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
          ($ᵗ (PairIdx → PairRand))) ≤
        ∑ i' : Index, prEvent ((fun rand : PairIdx → PairRand => i ≠ i' ∧
          hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
          ($ᵗ (PairIdx → PairRand))) :=
      prEvent_exists_le_sum (ι := Index) ($ᵗ (PairIdx → PairRand))
        (fun i' rand => i ≠ i' ∧
          hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i')
    have hterm : ∀ i' : Index, prEvent ((fun rand : PairIdx → PairRand => i ≠ i' ∧
        hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
        ($ᵗ (PairIdx → PairRand))) ≤ (1 : ENNReal) / 2 ^ 192 := by
      intro i'
      by_cases hne : i ≠ i'
      · exact (prEvent_mono_of_support ($ᵗ (PairIdx → PairRand))
          (fun rand => i ≠ i' ∧ hiddenCall3 h768 aVec bVec (pairSalts rand) i =
            hiddenCall3 h768 aVec bVec (pairSalts rand) i')
          (fun rand => hiddenCall3 h768 aVec bVec (pairSalts rand) i =
            hiddenCall3 h768 aVec bVec (pairSalts rand) i')
          (fun _ _ h => h.2)).trans (hiddenCall3_pair_collision_le h768 aVec bVec i i' hne)
      · have hz : prEvent ((fun rand : PairIdx → PairRand => i ≠ i' ∧
            hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
            ($ᵗ (PairIdx → PairRand))) = 0 :=
          prEvent_eq_zero_of_forall_mem_support ($ᵗ (PairIdx → PairRand))
            (fun rand => i ≠ i' ∧ hiddenCall3 h768 aVec bVec (pairSalts rand) i =
              hiddenCall3 h768 aVec bVec (pairSalts rand) i')
            (fun _ _ h => hne h.1)
        exact (le_of_eq hz).trans zero_le
    have hbd : ∑ i' : Index, prEvent ((fun rand : PairIdx → PairRand => i ≠ i' ∧
          hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
          ($ᵗ (PairIdx → PairRand))) ≤
        ∑ _i' : Index, ((1 : ENNReal) / 2 ^ 192) :=
      Finset.sum_le_sum (fun i' _ => hterm i')
    refine hinner.trans (hbd.trans ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
  have hbd2 : ∑ i : Index, prEvent ((fun rand : PairIdx → PairRand => ∃ i' : Index, i ≠ i' ∧
        hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
        ($ᵗ (PairIdx → PairRand))) ≤
      ∑ _i : Index, ((LENGTH : ENNReal) / 2 ^ 192) :=
    Finset.sum_le_sum (fun i _ => hrow i)
  refine houter.trans (hbd2.trans ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv, div_eq_mul_inv,
    ← mul_assoc, ← Nat.cast_mul]

private theorem badRand_t5_le (positions : Positions) :
    prEvent ((fun rand : PairIdx → PairRand =>
      ∃ i ∉ positions, i.val % 2 = 0 ∧ pairSalts rand i = 0#192) <$>
      ($ᵗ (PairIdx → PairRand))) ≤
      (LENGTH : ENNReal) / 2 ^ 192 := by
  have hle : prEvent ((fun rand : PairIdx → PairRand =>
        ∃ i ∉ positions, i.val % 2 = 0 ∧ pairSalts rand i = 0#192) <$> ($ᵗ (PairIdx → PairRand))) ≤
      prEvent ((fun rand : PairIdx → PairRand => ∃ i : Index, pairSalts rand i = 0#192) <$>
        ($ᵗ (PairIdx → PairRand))) :=
    prEvent_mono_of_support ($ᵗ (PairIdx → PairRand)) _ _ (fun _ _ ⟨i, _, _, h0⟩ => ⟨i, h0⟩)
  have hsum : prEvent ((fun rand : PairIdx → PairRand => ∃ i : Index, pairSalts rand i = 0#192) <$>
        ($ᵗ (PairIdx → PairRand))) ≤
      ∑ i : Index, prEvent ((fun rand : PairIdx → PairRand => pairSalts rand i = 0#192) <$>
        ($ᵗ (PairIdx → PairRand))) :=
    prEvent_exists_le_sum (ι := Index) ($ᵗ (PairIdx → PairRand)) (fun i rand => pairSalts rand i = 0#192)
  have hbd : ∑ i : Index, prEvent ((fun rand : PairIdx → PairRand => pairSalts rand i = 0#192) <$>
        ($ᵗ (PairIdx → PairRand))) ≤
      ∑ _i : Index, ((1 : ENNReal) / 2 ^ 192) :=
    Finset.sum_le_sum (fun i _ => pairSalts_target_le i 0#192)
  refine hle.trans (hsum.trans (hbd.trans ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

private theorem badRand_slice_le (cache1 : CompressionCache)
    (keys1 : Finset (BitVec COMPRESSION_INPUT_LENGTH))
    (covered : ∀ k, cache1 k ≠ none → k ∈ keys1)
    (start : Nat) (mkSet : (Index → Salt192) → Finset (BitVec 192))
    (hmem : ∀ rand v, v ∈ mkSet (pairSalts rand) → ∃ i : Index, pairSalts rand i = v) :
    prEvent ((fun rand : PairIdx → PairRand =>
      CacheHitsSlice192 start cache1 (mkSet (pairSalts rand))) <$> ($ᵗ (PairIdx → PairRand))) ≤
      ((keys1.card * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  let S2 : Finset (BitVec COMPRESSION_INPUT_LENGTH × Index) := keys1 ×ˢ (Finset.univ : Finset Index)
  have hle : prEvent ((fun rand : PairIdx → PairRand =>
        CacheHitsSlice192 start cache1 (mkSet (pairSalts rand))) <$> ($ᵗ (PairIdx → PairRand))) ≤
      prEvent ((fun rand : PairIdx → PairRand => ∃ p ∈ S2,
        pairSalts rand p.2 = ((cache1 p.1).getD 0).extractLsb' start 192) <$> ($ᵗ (PairIdx → PairRand))) := by
    apply prEvent_mono_of_support
    intro rand _ ⟨k, ans, hkans, hmv⟩
    obtain ⟨i, hi⟩ := hmem rand _ hmv
    refine ⟨(k, i), Finset.mem_product.mpr ⟨covered k (by rw [hkans]; exact Option.some_ne_none _), Finset.mem_univ i⟩, ?_⟩
    change pairSalts rand i = ((cache1 k).getD 0).extractLsb' start 192
    rw [hkans]; exact hi
  have hsum : prEvent ((fun rand : PairIdx → PairRand => ∃ p ∈ S2,
        pairSalts rand p.2 = ((cache1 p.1).getD 0).extractLsb' start 192) <$> ($ᵗ (PairIdx → PairRand))) ≤
      ∑ p ∈ S2, prEvent ((fun rand : PairIdx → PairRand =>
        pairSalts rand p.2 = ((cache1 p.1).getD 0).extractLsb' start 192) <$> ($ᵗ (PairIdx → PairRand))) :=
    prEvent_exists_finset_le_sum ($ᵗ (PairIdx → PairRand)) S2
      (fun p rand => pairSalts rand p.2 = ((cache1 p.1).getD 0).extractLsb' start 192)
  have hbd : ∑ p ∈ S2, prEvent ((fun rand : PairIdx → PairRand =>
        pairSalts rand p.2 = ((cache1 p.1).getD 0).extractLsb' start 192) <$> ($ᵗ (PairIdx → PairRand))) ≤
      ∑ _p ∈ S2, ((1 : ENNReal) / 2 ^ 192) :=
    Finset.sum_le_sum (fun p _ => pairSalts_target_le p.2 _)
  refine hle.trans (hsum.trans (hbd.trans ?_))
  rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

theorem badRand_prob_le (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cache1 : CompressionCache) (keys1 : Finset (BitVec COMPRESSION_INPUT_LENGTH))
    (covered : ∀ k, cache1 k ≠ none → k ∈ keys1)
    (aVec bVec : Index → Digest) (positions : Positions) :
    prEvent ((fun rand : PairIdx → PairRand => BadRand h768 cache1 aVec bVec positions rand) <$>
      ($ᵗ (PairIdx → PairRand))) ≤
      (((LENGTH / 2) ^ 5 : Nat) : ENNReal) / 2 ^ 256 +
      (((3 * keys1.card + 2 * LENGTH + 1) * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  have hT1 := badMidpoint_pairRand_le
  have hT2 := badRand_t2_le h768 cache1 keys1 covered aVec bVec positions
  have hPC := badRand_pairColl_le h768 aVec bVec
  have hT3 : prEvent ((fun rand : PairIdx → PairRand => ∃ i ∉ positions, ∃ i' ∉ positions, i ≠ i' ∧
      hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
      ($ᵗ (PairIdx → PairRand))) ≤ ((LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 :=
    (prEvent_mono_of_support ($ᵗ (PairIdx → PairRand)) _ _
      (fun _ _ ⟨i, _, i', _, hne, heq⟩ => ⟨i, i', hne, heq⟩)).trans hPC
  have hT4 : prEvent ((fun rand : PairIdx → PairRand => ∃ i ∈ positions, ∃ i' ∉ positions,
      hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') <$>
      ($ᵗ (PairIdx → PairRand))) ≤ ((LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 :=
    (prEvent_mono_of_support ($ᵗ (PairIdx → PairRand)) _ _
      (fun _ _ ⟨i, hi, i', hi', heq⟩ => ⟨i, i', fun h => hi' (by subst h; exact hi), heq⟩)).trans hPC
  have hT5 := badRand_t5_le positions
  have hT6 := badRand_slice_le cache1 keys1 covered 0 (hiddenOddSalts positions) (fun rand v hv => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv; exact ⟨i, hi⟩)
  have hT7 := badRand_slice_le cache1 keys1 covered 64 (hiddenEvenSalts positions) (fun rand v hv => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv; exact ⟨i, hi⟩)
  unfold BadRand
  have hcomb : prEvent ((fun rand : PairIdx → PairRand =>
      BadMidpoint (fun j => pairSM (rand j)) ∨
      (∃ i ∉ positions, cache1 (hiddenCall3 h768 aVec bVec (pairSalts rand) i) ≠ none) ∨
      (∃ i ∉ positions, ∃ i' ∉ positions, i ≠ i' ∧
        hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') ∨
      (∃ i ∈ positions, ∃ i' ∉ positions,
        hiddenCall3 h768 aVec bVec (pairSalts rand) i = hiddenCall3 h768 aVec bVec (pairSalts rand) i') ∨
      (∃ i ∉ positions, i.val % 2 = 0 ∧ pairSalts rand i = 0#192) ∨
      CacheHitsSlice192 0 cache1 (hiddenOddSalts positions (pairSalts rand)) ∨
      CacheHitsSlice192 64 cache1 (hiddenEvenSalts positions (pairSalts rand))) <$> ($ᵗ (PairIdx → PairRand))) ≤
      (((LENGTH / 2) ^ 5 : Nat) : ENNReal) / 2 ^ 256 +
      (((keys1.card * LENGTH : Nat) : ENNReal) / 2 ^ 192 +
       (((LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 +
        (((LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 +
         ((LENGTH : ENNReal) / 2 ^ 192 +
          (((keys1.card * LENGTH : Nat) : ENNReal) / 2 ^ 192 +
           ((keys1.card * LENGTH : Nat) : ENNReal) / 2 ^ 192))))) := by
    refine (prEvent_or_le ($ᵗ (PairIdx → PairRand)) _ _).trans (add_le_add hT1 ?_)
    refine (prEvent_or_le ($ᵗ (PairIdx → PairRand)) _ _).trans (add_le_add hT2 ?_)
    refine (prEvent_or_le ($ᵗ (PairIdx → PairRand)) _ _).trans (add_le_add hT3 ?_)
    refine (prEvent_or_le ($ᵗ (PairIdx → PairRand)) _ _).trans (add_le_add hT4 ?_)
    refine (prEvent_or_le ($ᵗ (PairIdx → PairRand)) _ _).trans (add_le_add hT5 ?_)
    exact (prEvent_or_le ($ᵗ (PairIdx → PairRand)) _ _).trans (add_le_add hT6 hT7)
  refine hcomb.trans ?_
  apply add_le_add le_rfl
  simp only [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  simp only [← Nat.cast_add]
  exact le_of_eq (congrArg (Nat.cast : Nat → ENNReal) (by ring))


private theorem extractLsb'_extractLsb'_of_le {n : Nat} (x : BitVec n)
    (s1 l1 s2 l2 : Nat) (h : s2 + l2 ≤ l1) :
    (x.extractLsb' s1 l1).extractLsb' s2 l2 = x.extractLsb' (s1 + s2) l2 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
    show s2 + k < l1 by omega, Nat.add_assoc]

/-- Under `¬ BadMidpoint sM`, any fixed 768-bit query hits `{hiddenCall3 i | i ∉ positions}`
over uniform secret `(sLHid, sRHid)` with probability at most `8 / 2^128`! -/
theorem single_query_hit_given_good_sM (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (aVec bVec : Index → Digest) (positions : Positions)
    (sLOpen : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64) (sROpen : PairIdx → BitVec 128)
    (hgood : ¬ BadMidpoint sM) (x : BitVec COMPRESSION_INPUT_LENGTH) :
    prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
      ∃ i ∉ positions, hiddenCall3 h768 aVec bVec
        (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x) <$>
      ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128)))) ≤ (8 : ENNReal) / 2 ^ 128 := by
  let E : Finset PairIdx := Finset.univ.filter (fun j : PairIdx => sM j = x.extractLsb' 704 64)
  let O : Finset PairIdx := Finset.univ.filter (fun j : PairIdx => sM j = x.extractLsb' 0 64)
  have hEcard : E.card ≤ 4 := by
    by_contra h; exact hgood ⟨x.extractLsb' 704 64, by dsimp only [E] at h; omega⟩
  have hOcard : O.card ≤ 4 := by
    by_contra h; exact hgood ⟨x.extractLsb' 0 64, by dsimp only [O] at h; omega⟩
  let μ := $ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128))
  have hsplit : prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
      ∃ i ∉ positions, hiddenCall3 h768 aVec bVec
        (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x) <$> μ) ≤
      prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
        ∃ j ∈ E, p.1 j = x.extractLsb' 576 128) <$> μ) +
      prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
        ∃ j ∈ O, p.2 j = x.extractLsb' 64 128) <$> μ) := by
    refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_or_le μ _ _)
    rintro ⟨sLHid, sRHid⟩ _ ⟨i, hi, heq⟩
    by_cases he : i.val % 2 = 0
    · left
      have hsalt : pairSalts (mergePairRand positions sLOpen sM sROpen sLHid sRHid) i =
          sM (pairOf i) ++ sLHid (pairOf i) :=
        mergePairRand_hidden_even positions sLOpen sM sROpen sLHid sRHid i hi he
      have hc := congrArg (fun v : BitVec COMPRESSION_INPUT_LENGTH => v.extractLsb' 576 192) heq
      unfold hiddenCall3 leafFinalInput at hc
      rw [extractLsb'_cast_eq, ite_eq_left_of_eq_true _ _ (eq_true he), leafFinalEven_salt, hsalt] at hc
      have h64 : sM (pairOf i) = x.extractLsb' 704 64 := by
        have h := congrArg (fun v : Salt192 => v.extractLsb' 128 64) hc
        rw [BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 128), Nat.sub_self,
          BitVec.extractLsb'_eq_self, extractLsb'_extractLsb'_of_le _ _ _ _ _ (by decide)] at h
        simpa only [show 576 + 128 = 704 by decide] using h
      have h128 : sLHid (pairOf i) = x.extractLsb' 576 128 := by
        have h := congrArg (fun v : Salt192 => v.extractLsb' 0 128) hc
        rw [BitVec.extractLsb'_append_eq_right, extractLsb'_extractLsb'_of_le _ _ _ _ _ (by decide)] at h
        simpa only [Nat.add_zero] using h
      exact ⟨pairOf i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h64⟩, h128⟩
    · right
      have hsalt : pairSalts (mergePairRand positions sLOpen sM sROpen sLHid sRHid) i =
          sRHid (pairOf i) ++ sM (pairOf i) :=
        mergePairRand_hidden_odd positions sLOpen sM sROpen sLHid sRHid i hi he
      have hc := congrArg (fun v : BitVec COMPRESSION_INPUT_LENGTH => v.extractLsb' 0 192) heq
      unfold hiddenCall3 leafFinalInput at hc
      rw [extractLsb'_cast_eq, ite_eq_right_of_eq_false _ _ (eq_false he), leafFinalOdd_salt, hsalt] at hc
      have h64 : sM (pairOf i) = x.extractLsb' 0 64 := by
        have h := congrArg (fun v : Salt192 => v.extractLsb' 0 64) hc
        rw [BitVec.extractLsb'_append_eq_right, extractLsb'_extractLsb'_of_le _ _ _ _ _ (by decide)] at h
        simpa only [Nat.add_zero] using h
      have h128 : sRHid (pairOf i) = x.extractLsb' 64 128 := by
        have h := congrArg (fun v : Salt192 => v.extractLsb' 64 128) hc
        rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64), Nat.sub_self,
          BitVec.extractLsb'_eq_self, extractLsb'_extractLsb'_of_le _ _ _ _ _ (by decide)] at h
        simpa only [Nat.zero_add] using h
      exact ⟨pairOf i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h64⟩, h128⟩
  have hFst : ∀ j : PairIdx, prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
      p.1 j = x.extractLsb' 576 128) <$> μ) ≤ (1 : ENNReal) / 2 ^ 128 := by
    intro j
    apply prEvent_prod_fst_le (A := PairIdx → BitVec 128) (B := PairIdx → BitVec 128)
      (fun f => f j = x.extractLsb' 576 128)
    refine prEvent_uniform_coord_le (D := PairIdx) (R := BitVec 128) j
      (fun v => v = x.extractLsb' 576 128) ?_
    rw [prEvent_uniform_eq_target, Fintype.card_bitVec 128]
    simp only [Nat.cast_pow, Nat.cast_ofNat, le_refl]
  have hSnd : ∀ j : PairIdx, prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
      p.2 j = x.extractLsb' 64 128) <$> μ) ≤ (1 : ENNReal) / 2 ^ 128 := by
    intro j
    apply prEvent_prod_snd_le (A := PairIdx → BitVec 128) (B := PairIdx → BitVec 128)
      (fun f => f j = x.extractLsb' 64 128)
    refine prEvent_uniform_coord_le (D := PairIdx) (R := BitVec 128) j
      (fun v => v = x.extractLsb' 64 128) ?_
    rw [prEvent_uniform_eq_target, Fintype.card_bitVec 128]
    simp only [Nat.cast_pow, Nat.cast_ofNat, le_refl]
  have hEbd : prEvent ((fun p => ∃ j ∈ E, p.1 j = x.extractLsb' 576 128) <$> μ) ≤ (4 : ENNReal) / 2 ^ 128 := by
    refine (prEvent_exists_finset_le_sum μ E _).trans ((Finset.sum_le_sum (fun j _ => hFst j)).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr hEcard) _
  have hObd : prEvent ((fun p => ∃ j ∈ O, p.2 j = x.extractLsb' 64 128) <$> μ) ≤ (4 : ENNReal) / 2 ^ 128 := by
    refine (prEvent_exists_finset_le_sum μ O _).trans ((Finset.sum_le_sum (fun j _ => hSnd j)).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr hOcard) _
  refine (hsplit.trans (add_le_add hEbd hObd)).trans ?_
  rw [← ENNReal.add_div]; norm_num

theorem trace_hit_given_good_sM (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (aVec bVec : Index → Digest) (positions : Positions)
    (sLOpen : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64) (sROpen : PairIdx → BitVec 128)
    (hgood : ¬ BadMidpoint sM) (tr : List (BitVec COMPRESSION_INPUT_LENGTH)) :
    prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
      tr.any (fun x => decide (∃ i ∉ positions, hiddenCall3 h768 aVec bVec
        (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x)) = true) <$>
      ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128)))) ≤
      ((8 * tr.length : Nat) : ENNReal) / 2 ^ 128 := by
  induction tr with
  | nil =>
    have hz : prEvent ((fun _ : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) => false = true) <$>
        ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128)))) = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ h => Bool.false_ne_true h)
    simpa only [List.any_nil, List.length_nil, Nat.mul_zero, Nat.cast_zero, ENNReal.zero_div] using hz.le
  | cons x rest ih =>
    have hsplit : prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
        (x :: rest).any (fun y => decide (∃ i ∉ positions, hiddenCall3 h768 aVec bVec
          (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = y)) = true) <$>
        ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128)))) ≤
        prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
          ∃ i ∉ positions, hiddenCall3 h768 aVec bVec
            (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x) <$>
          ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128)))) +
        prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
          rest.any (fun y => decide (∃ i ∉ positions, hiddenCall3 h768 aVec bVec
            (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = y)) = true) <$>
          ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128)))) := by
      refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_or_le _ _ _)
      intro p _ hany
      simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at hany
      exact hany
    refine (hsplit.trans (add_le_add (single_query_hit_given_good_sM h768 aVec bVec positions sLOpen sM sROpen hgood x) ih)).trans ?_
    rw [← ENNReal.add_div, List.length_cons]
    apply ENNReal.div_le_div_right
    push_cast
    exact le_of_eq (by ring)

/-! ### 5. One-Shot Distance `Real ↔ Ideal` Conditioned on `(aVec, bVec, cache1)` -/


def marksHidden3 (h768 : COMPRESSION_INPUT_LENGTH = 768) (aVec bVec : Index → Digest)
    (positions : Positions) (salts : Index → Salt192) : World.Domain → Bool
  | .inr (.inl x) => decide (∃ i ∉ positions, hiddenCall3 h768 aVec bVec salts i = x)
  | _ => false

def realObsAB (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache1 : CompressionCache) (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let rand ← $ᵗ (PairIdx → PairRand)
  let table ← $ᵗ Compression
  let tr := referenceTranscript h768 (tableExtending cache1 table) msg (pairSalts rand) positions
  fixedOracleRun ⟨tableExtending cache1 table, permutation⟩ (observe tr.1 tr.2)

def idealObsAB (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache1 : CompressionCache) (aVec bVec : Index → Digest) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let rand ← $ᵗ (PairIdx → PairRand)
  let leafRand ← $ᵗ (Index → Digest)
  let table ← $ᵗ Compression
  let tr := idealTranscriptFromAB h768 (tableExtending cache1 table) aVec bVec (pairSalts rand) leafRand positions
  fixedOracleRun ⟨tableExtending cache1 table, permutation⟩ (observe tr.1 tr.2)

private noncomputable def treeHitProbOf (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache1 : CompressionCache)
    (aVec bVec : Index → Digest) (positions : Positions) (rand : PairIdx → PairRand) : ENNReal :=
  prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
    (do let leafRand ← $ᵗ (Index → Digest)
        let table ← $ᵗ Compression
        flaggedRun ⟨tableExtending cache1 table, permutation⟩
          (marksHidden3 h768 aVec bVec positions (pairSalts rand))
          (queryTreeFromLeafFn h768 (idealLeafFn h768 aVec bVec (pairSalts rand) leafRand positions))))

private noncomputable def obsHitProbOf (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache1 : CompressionCache)
    (aVec bVec : Index → Digest) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (rand : PairIdx → PairRand) : ENNReal :=
  prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
    (do let leafRand ← $ᵗ (Index → Digest)
        let table ← $ᵗ Compression
        let tr := idealTranscriptFromAB h768 (tableExtending cache1 table) aVec bVec (pairSalts rand) leafRand positions
        flaggedRun ⟨tableExtending cache1 table, permutation⟩
          (marksHidden3 h768 aVec bVec positions (pairSalts rand))
          (observe tr.1 tr.2)))

private theorem tree_hit_given_good_rand (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache1 : CompressionCache)
    (aVec bVec : Index → Digest) (positions : Positions) (rand : PairIdx → PairRand)
    (hgood : ¬ BadRand h768 cache1 aVec bVec positions rand) :
    treeHitProbOf h768 permutation cache1 aVec bVec positions rand ≤
      (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  classical
  let Oset := hiddenOddSalts positions (pairSalts rand)
  let Eset := hiddenEvenSalts positions (pairSalts rand)
  have hnoOpen : ∀ i ∈ positions, ∀ i' ∉ positions,
      hiddenCall3 h768 aVec bVec (pairSalts rand) i ≠ hiddenCall3 h768 aVec bVec (pairSalts rand) i' :=
    fun i hi i' hi' heq => hgood (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, i', hi', heq⟩))))
  have hnoZero : ∀ i ∉ positions, i.val % 2 = 0 → pairSalts rand i ≠ 0#192 :=
    fun i hi he hz => hgood (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, he, hz⟩)))))
  have hclean0 : ¬ CacheHitsSlice192 0 cache1 Oset :=
    fun h => hgood (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  have hclean64 : ¬ CacheHitsSlice192 64 cache1 Eset :=
    fun h => hgood (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  let lrBad (lr : Index → Digest) : Prop :=
    (∃ j ∉ positions, (lr j).extractLsb' 0 192 ∈ Oset) ∨
    (∃ j ∉ positions, (lr j).extractLsb' 64 192 ∈ Eset)
  have hlrBad_prob : prEvent (lrBad <$> ($ᵗ (Index → Digest))) ≤
      ((2 * LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
    have hside : ∀ (start : Nat) (hst : start = 0 ∨ start = 64) (T : Finset (BitVec 192)) (hT : T.card ≤ LENGTH),
        prEvent ((fun lr : Index → Digest => ∃ j ∉ positions, (lr j).extractLsb' start 192 ∈ T) <$>
          ($ᵗ (Index → Digest))) ≤ ((LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
      intro start hst T hT
      refine (prEvent_mono_of_support ($ᵗ (Index → Digest))
        (fun lr : Index → Digest => ∃ j ∉ positions, (lr j).extractLsb' start 192 ∈ T)
        (fun lr : Index → Digest => ∃ j : Index, (lr j).extractLsb' start 192 ∈ T)
        (fun _ _ ⟨j, _, hm⟩ => ⟨j, hm⟩)).trans ((prEvent_exists_le_sum ($ᵗ (Index → Digest)) _).trans ?_)
      have h1 : ∀ j : Index, prEvent ((fun lr : Index → Digest => (lr j).extractLsb' start 192 ∈ T) <$>
          ($ᵗ (Index → Digest))) ≤ (LENGTH : ENNReal) / 2 ^ 192 := fun j =>
        prEvent_uniform_coord_le (D := Index) (R := Digest) j
          (fun d => d.extractLsb' start 192 ∈ T)
          ((uniform_digest_hits_slice192_le start hst T).trans
            (ENNReal.div_le_div_right (Nat.cast_le.mpr hT) _))
      refine (Finset.sum_le_sum (fun j _ => h1 j)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_div_assoc]
      push_cast; rfl
    refine (prEvent_or_le ($ᵗ (Index → Digest)) _ _).trans
      ((add_le_add (hside 0 (Or.inl rfl) Oset (hiddenOddSalts_card_le positions _))
        (hside 64 (Or.inr rfl) Eset (hiddenEvenSalts_card_le positions _))).trans ?_)
    rw [← ENNReal.add_div]; apply ENNReal.div_le_div_right; push_cast; exact le_of_eq (by ring)
  have hlrClean : ∀ lr : Index → Digest, ¬ lrBad lr →
      prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
        (($ᵗ Compression) >>= fun table =>
          flaggedRun ⟨tableExtending cache1 table, permutation⟩
            (marksHidden3 h768 aVec bVec positions (pairSalts rand))
            (queryTreeFromLeafFn h768 (idealLeafFn h768 aVec bVec (pairSalts rand) lr positions)))) ≤
      ((2 * IDEAL_TREE_BUDGET * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
    intro lr hlr_ok
    let comp := queryTreeFromLeafFn h768 (idealLeafFn h768 aVec bVec (pairSalts rand) lr positions)
    have hcomp_bd : PublicQueryBound comp IDEAL_TREE_BUDGET :=
      queryTreeFromLeafFn_bound_one h768 _ (idealLeafFn_bound h768 aVec bVec (pairSalts rand) lr positions)
    let trBad (tr : CompressionReplies) : Prop :=
      (∃ q ∈ tr, q.2.extractLsb' 0 192 ∈ Oset) ∨ (∃ q ∈ tr, q.2.extractLsb' 64 192 ∈ Eset)
    have hhit_le_tr :
        prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
          (($ᵗ Compression) >>= fun table =>
            flaggedRun ⟨tableExtending cache1 table, permutation⟩
              (marksHidden3 h768 aVec bVec positions (pairSalts rand)) comp)) ≤
        prEvent ((fun res : (Nat → Nat → Digest) × CompressionReplies => trBad res.2) <$>
          (($ᵗ Compression) >>= fun table =>
            fixedOracleRun ⟨tableExtending cache1 table, permutation⟩ (traceCompressionReplies comp))) := by
      simp only [map_bind, prEvent_bind_eq_tsum_prEvent]
      apply ENNReal.tsum_le_tsum; intro table
      apply mul_le_mul_of_nonneg_left _ zero_le
      let o : Oracle := ⟨tableExtending cache1 table, permutation⟩
      obtain ⟨nodes, trace, htr_run, hgoodTr⟩ :=
        queryIdealTree_good_trace h768 o aVec bVec (pairSalts rand) lr positions
      have hflag_tr : ∀ {β : Type} (c : OracleComp World β) (f : Bool),
          flaggedRun o (marksHidden3 h768 aVec bVec positions (pairSalts rand)) c f =
          (fun r : β × CompressionReplies =>
            (r.1, (), f || r.2.any (fun p => decide (∃ i ∉ positions, hiddenCall3 h768 aVec bVec (pairSalts rand) i = p.1)))) <$>
            fixedOracleRun o (traceCompressionReplies c) := by
        intro β c; induction c using OracleComp.inductionOn with
        | pure v =>
          intro f
          change pure (v, ((), f)) = _ <$> fixedOracleRun o (pure (v, []))
          rw [fixed_oracle_run_pure, map_pure]; simp only [List.any_nil, Bool.or_false]
        | query_bind q k ih =>
          intro f; rw [flagged_run_query_bind]
          rcases q with coins | pq
          · change (o.world (.inl coins) >>= fun ans =>
                flaggedRun o _ (k ans) (f || false)) =
              _ <$> fixedOracleRun o ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun ans =>
                traceCompressionReplies (k ans))
            rw [fixed_run_query_bind, map_bind]
            apply bind_congr; intro ans; rw [Bool.or_false, ih ans f]
          · rcases pq with x | permq
            · let ans0 : Digest := o.compression x
              have hcomp :
                  fixedOracleRun o ((liftM (World.query (.inr (.inl x))) : OracleComp World Digest) >>=
                    fun (ans : Digest) => traceCompressionReplies (k ans) >>= fun (v, tr) => pure (v, (x, ans) :: tr)) =
                  fixedOracleRun o (traceCompressionReplies (k ans0) >>= fun (v, tr) => pure (v, (x, ans0) :: tr)) :=
                fixed_oracle_run_compress o x _
              change ((pure ans0 : ProbComp Digest) >>= fun (ans : Digest) =>
                    flaggedRun o _ (k ans)
                      (f || decide (∃ i ∉ positions, hiddenCall3 h768 aVec bVec (pairSalts rand) i = x))) =
                  _ <$> fixedOracleRun o ((liftM (World.query (.inr (.inl x))) : OracleComp World Digest) >>=
                    fun (ans : Digest) => traceCompressionReplies (k ans) >>= fun (v, tr) => pure (v, (x, ans) :: tr))
              rw [pure_bind, hcomp, ih ans0, fixed_oracle_run_bind, map_bind, map_eq_bind_pure_comp]
              apply bind_congr; rintro ⟨v, tr⟩
              rw [fixed_oracle_run_pure, map_pure]
              simp only [List.any_cons, Bool.or_assoc]; rfl
            · change (o.world (.inr (.inr permq)) >>= fun ans =>
                  flaggedRun o _ (k ans) (f || false)) =
                _ <$> fixedOracleRun o ((liftM (World.query (.inr (.inr permq))) : OracleComp World _) >>= fun ans =>
                  traceCompressionReplies (k ans))
              rw [fixed_run_query_bind, map_bind]
              apply bind_congr; intro ans; rw [Bool.or_false, ih ans f]
      rw [hflag_tr comp false, htr_run, map_pure]
      apply prEvent_pure_le_pure
      intro hhit
      simp only [Bool.false_or] at hhit
      obtain ⟨p, hp, hdec⟩ := List.any_eq_true.mp hhit
      obtain ⟨i', hi', hpeq⟩ := decide_eq_true_eq.mp hdec
      rcases hgoodTr p hp with ⟨i, hi, hiEq⟩ | ⟨hlo, hhi⟩
      · exact (hnoOpen i hi i' hi' (hiEq.symm.trans hpeq.symm)).elim
      · by_cases he : i'.val % 2 = 0
        · have hp576 : p.1.extractLsb' 576 192 = pairSalts rand i' := by
            rw [← hpeq]; unfold hiddenCall3 leafFinalInput
            simp only [extractLsb'_cast_eq, he, ite_true, leafFinalEven_salt]
          have hmemE : pairSalts rand i' ∈ Eset :=
            Finset.mem_image.mpr ⟨i', Finset.mem_filter.mpr
              ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i', hi'⟩, he⟩, rfl⟩
          rcases hhi with hz | ⟨j, hj, hjeq⟩ | ⟨q, hq, hqeq⟩
          · exact (hnoZero i' hi' he (hp576.symm.trans hz)).elim
          · exact (hlr_ok (Or.inr ⟨j, hj, hjeq ▸ hp576 ▸ hmemE⟩)).elim
          · exact Or.inr ⟨q, hq, hqeq ▸ hp576 ▸ hmemE⟩
        · have hp0 : p.1.extractLsb' 0 192 = pairSalts rand i' := by
            rw [← hpeq]; unfold hiddenCall3 leafFinalInput
            simp only [extractLsb'_cast_eq, he, ite_false, leafFinalOdd_salt]
          have hmemO : pairSalts rand i' ∈ Oset :=
            Finset.mem_image.mpr ⟨i', Finset.mem_filter.mpr
              ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i', hi'⟩, he⟩, rfl⟩
          rcases hlo with ⟨j, hj, hjeq⟩ | ⟨q, hq, hqeq⟩
          · exact (hlr_ok (Or.inl ⟨j, hj, hjeq ▸ hp0 ▸ hmemO⟩)).elim
          · exact Or.inl ⟨q, hq, hqeq ▸ hp0 ▸ hmemO⟩
    have heq_rom := (EvalDistEq.of_evalDist_eq
      (compression_sampling_equivalence permutation (traceCompressionReplies comp) cache1)).prEvent_eq
        (fun res : (Nat → Nat → Digest) × CompressionReplies => trBad res.2)
    simp only [Functor.map_map] at heq_rom
    rw [← heq_rom] at hhit_le_tr
    have hin_cache :
        prEvent ((fun res : ((Nat → Nat → Digest) × CompressionReplies) × CompressionCache => trBad res.1.2) <$>
          compressionRun permutation (traceCompressionReplies comp) cache1) ≤
        prEvent ((fun res => CacheHitsSlice192 0 res.2 Oset ∨ CacheHitsSlice192 64 res.2 Eset) <$>
          compressionRun permutation (traceCompressionReplies comp) cache1) := by
      apply prEvent_mono_of_support
      intro res hreach htb
      rcases htb with ⟨q, hq, hmo⟩ | ⟨q, hq, hme⟩
      · exact Or.inl ⟨q.1, q.2, (traceReplies_compressionRun_cache permutation comp cache1 res hreach).2 q hq, hmo⟩
      · exact Or.inr ⟨q.1, q.2, (traceReplies_compressionRun_cache permutation comp cache1 res hreach).2 q hq, hme⟩
    have h0 := compression_run_hits_slice192_bound 0 (Or.inl rfl) permutation (traceCompressionReplies comp)
      IDEAL_TREE_BUDGET (traceReplies_bound comp IDEAL_TREE_BUDGET hcomp_bd) cache1 Oset hclean0
    have h64 := compression_run_hits_slice192_bound 64 (Or.inr rfl) permutation (traceCompressionReplies comp)
      IDEAL_TREE_BUDGET (traceReplies_bound comp IDEAL_TREE_BUDGET hcomp_bd) cache1 Eset hclean64
    have hor := (prEvent_or_le (compressionRun permutation (traceCompressionReplies comp) cache1)
      (fun res => CacheHitsSlice192 0 res.2 Oset) (fun res => CacheHitsSlice192 64 res.2 Eset)).trans
      (add_le_add h0 h64)
    refine hhit_le_tr.trans (hin_cache.trans (hor.trans ?_))
    have hO : (Oset.card : ENNReal) ≤ LENGTH := Nat.cast_le.mpr (hiddenOddSalts_card_le positions _)
    have hE : (Eset.card : ENNReal) ≤ LENGTH := Nat.cast_le.mpr (hiddenEvenSalts_card_le positions _)
    have hm0 : (IDEAL_TREE_BUDGET : ENNReal) * ((Oset.card : ENNReal) / 2 ^ 192) ≤
        ((IDEAL_TREE_BUDGET * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
      rw [← mul_div_assoc]; push_cast
      exact ENNReal.div_le_div_right (mul_le_mul_of_nonneg_left hO zero_le) _
    have hm64 : (IDEAL_TREE_BUDGET : ENNReal) * ((Eset.card : ENNReal) / 2 ^ 192) ≤
        ((IDEAL_TREE_BUDGET * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
      rw [← mul_div_assoc]; push_cast
      exact ENNReal.div_le_div_right (mul_le_mul_of_nonneg_left hE zero_le) _
    refine (add_le_add hm0 hm64).trans ?_
    rw [← ENNReal.add_div]; apply ENNReal.div_le_div_right; push_cast; exact le_of_eq (by ring)
  have hcomb := prEvent_bind_le_prEvent_add_of_support
    ($ᵗ (Index → Digest))
    (fun lr => ($ᵗ Compression) >>= fun table =>
      flaggedRun ⟨tableExtending cache1 table, permutation⟩
        (marksHidden3 h768 aVec bVec positions (pairSalts rand))
        (queryTreeFromLeafFn h768 (idealLeafFn h768 aVec bVec (pairSalts rand) lr positions)))
    lrBad (fun res => res.2.2 = true) (fun lr _ hok => hlrClean lr hok)
  refine (hcomb.trans (add_le_add hlrBad_prob le_rfl)).trans ?_
  simp only [← ENNReal.add_div]; apply ENNReal.div_le_div_right; push_cast; exact le_of_eq (by ring)

private noncomputable def obsGoodTerm (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache1 : CompressionCache)
    (aVec bVec : Index → Digest) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α)
    (rand : PairIdx → PairRand) : ENNReal :=
  @ite _ (¬ BadMidpoint (fun j => pairSM (rand j))) (Classical.propDecidable _)
    (obsHitProbOf h768 permutation cache1 aVec bVec positions observe rand) 0

private def obsGoodEv (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache1 : CompressionCache)
    (aVec bVec : Index → Digest) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α)
    (rand : PairIdx → PairRand) : ProbComp Prop := do
  let lr ← $ᵗ (Index → Digest)
  let tbl ← $ᵗ Compression
  let tr := idealTranscriptFromAB h768 (tableExtending cache1 tbl) aVec bVec (pairSalts rand) lr positions
  let res ← flaggedRun ⟨tableExtending cache1 tbl, permutation⟩
    (marksHidden3 h768 aVec bVec positions (pairSalts rand)) (observe tr.1 tr.2)
  pure (¬ BadMidpoint (fun j => pairSM (rand j)) ∧ res.2.2 = true)

private theorem obs_ev_swap (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache1 : CompressionCache)
    (aVec bVec : Index → Digest) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α)
    (sLOpen : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64) (sROpen : PairIdx → BitVec 128) :
    let sOpen := pairSalts (combinePairRand sLOpen sM sROpen)
    𝒟[do let sLHid ← $ᵗ (PairIdx → BitVec 128)
         let sRHid ← $ᵗ (PairIdx → BitVec 128)
         obsGoodEv h768 permutation cache1 aVec bVec positions observe
           (mergePairRand positions sLOpen sM sROpen sLHid sRHid)] =
    𝒟[do let lr ← $ᵗ (Index → Digest)
         let tbl ← $ᵗ Compression
         let tr := idealTranscriptFromAB h768 (tableExtending cache1 tbl) aVec bVec sOpen lr positions
         let traced ← fixedOracleRun ⟨tableExtending cache1 tbl, permutation⟩ (traceCompression (observe tr.1 tr.2))
         let p ← $ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128))
         pure (¬ BadMidpoint sM ∧ traced.2.any (fun x => decide (∃ i ∉ positions,
           hiddenCall3 h768 aVec bVec (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x)) = true)] := by
  intro sOpen
  have htr_indep : ∀ (sLHid sRHid : PairIdx → BitVec 128) (tbl : Compression) (lr : Index → Digest),
      idealTranscriptFromAB h768 (tableExtending cache1 tbl) aVec bVec
        (pairSalts (mergePairRand positions sLOpen sM sROpen sLHid sRHid)) lr positions =
      idealTranscriptFromAB h768 (tableExtending cache1 tbl) aVec bVec sOpen lr positions :=
    fun sLHid sRHid tbl lr =>
      idealTranscript_congr_opened_salts h768 (tableExtending cache1 tbl) aVec bVec _ sOpen lr positions
        (fun i hi => mergePairRand_opened_salt positions sLOpen sM sROpen sLHid sRHid i hi)
  have hft : ∀ (o : Oracle) (comp : OracleComp World α) (salts : Index → Salt192) (f : Bool),
      flaggedRun o (marksHidden3 h768 aVec bVec positions salts) comp f =
      (fun r : α × List (BitVec COMPRESSION_INPUT_LENGTH) =>
        (r.1, (), f || r.2.any (fun x => decide (∃ i ∉ positions, hiddenCall3 h768 aVec bVec salts i = x)))) <$>
        fixedOracleRun o (traceCompression comp) := by
    intro o comp salts f
    induction comp using OracleComp.inductionOn generalizing f with
    | pure v =>
      simp only [flaggedRun, simulateQ_pure, StateT.run_pure, trace_compression_pure,
        fixed_oracle_run_pure, map_pure, List.any_nil, Bool.or_false]
    | query_bind q k ih =>
      rw [flagged_run_query_bind, trace_run_query_bind, map_bind]
      apply bind_congr; intro ans; rw [ih]; simp only [bind_pure_comp, Functor.map_map]
      apply congrArg (fun g => g <$> fixedOracleRun o (traceCompression (k ans)))
      funext r
      have hhd : (compressionHead q).any (fun x => decide (∃ i ∉ positions, hiddenCall3 h768 aVec bVec salts i = x)) =
          marksHidden3 h768 aVec bVec positions salts q := by
        rcases q with _ | pq
        · rfl
        · rcases pq with x | permq
          · change (decide (∃ i ∉ positions, hiddenCall3 h768 aVec bVec salts i = x) || false) = _
            exact Bool.or_false _
          · rcases permq <;> rfl
      simp only [List.any_append, hhd, Bool.or_assoc]
  have hpair :
      𝒟[do let sLHid ← $ᵗ (PairIdx → BitVec 128)
           let sRHid ← $ᵗ (PairIdx → BitVec 128)
           obsGoodEv h768 permutation cache1 aVec bVec positions observe
             (mergePairRand positions sLOpen sM sROpen sLHid sRHid)] =
      𝒟[do let p ← $ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128))
           let lr ← $ᵗ (Index → Digest)
           let tbl ← $ᵗ Compression
           let tr := idealTranscriptFromAB h768 (tableExtending cache1 tbl) aVec bVec sOpen lr positions
           let traced ← fixedOracleRun ⟨tableExtending cache1 tbl, permutation⟩ (traceCompression (observe tr.1 tr.2))
           pure (¬ BadMidpoint sM ∧ traced.2.any (fun x => decide (∃ i ∉ positions,
             hiddenCall3 h768 aVec bVec (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x)) = true)] := by
    rw [← prod_uniform_bind (fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
      do let lr ← $ᵗ (Index → Digest)
         let tbl ← $ᵗ Compression
         let tr := idealTranscriptFromAB h768 (tableExtending cache1 tbl) aVec bVec sOpen lr positions
         let traced ← fixedOracleRun ⟨tableExtending cache1 tbl, permutation⟩ (traceCompression (observe tr.1 tr.2))
         pure (¬ BadMidpoint sM ∧ traced.2.any (fun x => decide (∃ i ∉ positions,
           hiddenCall3 h768 aVec bVec (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x)) = true))]
    apply _root_.evalDist_bind_congr; intro sLHid
    apply _root_.evalDist_bind_congr; intro sRHid
    have hsmeq : (fun j => pairSM (mergePairRand positions sLOpen sM sROpen sLHid sRHid j)) = sM := by
      funext j; exact pairSM_combine _ sM _ j
    simp only [obsGoodEv, htr_indep, hsmeq]
    apply _root_.evalDist_bind_congr; intro lr
    apply _root_.evalDist_bind_congr; intro tbl
    rw [hft]
    simp only [Bool.false_or, map_eq_bind_pure_comp, bind_assoc]
    rfl
  rw [hpair, distribution_bind_comm ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128))) ($ᵗ (Index → Digest))]
  apply _root_.evalDist_bind_congr; intro lr
  rw [distribution_bind_comm ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128))) ($ᵗ Compression)]
  apply _root_.evalDist_bind_congr; intro tbl
  exact distribution_bind_comm ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128))) _ _

private theorem obs_hit_given_good_sM (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache1 : CompressionCache)
    (aVec bVec : Index → Digest) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (budget : Nat)
    (hobs : ∀ rt pf, PublicQueryBound (observe rt pf) budget) :
    (∑ rand : PairIdx → PairRand,
      Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] *
        obsGoodTerm h768 permutation cache1 aVec bVec positions observe rand) ≤
    ((8 * budget : Nat) : ENNReal) / 2 ^ 128 := by
  let ev := obsGoodEv h768 permutation cache1 aVec bVec positions observe
  have hsum_eq :
      (∑ rand : PairIdx → PairRand,
        Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] *
          obsGoodTerm h768 permutation cache1 aVec bVec positions observe rand) =
      prEvent (id <$> (($ᵗ (PairIdx → PairRand)) >>= ev)) := by
    rw [prEvent_bind_eq_sum_fintype]
    apply Finset.sum_congr rfl; intro rand _
    apply congrArg (Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] * ·)
    by_cases hgm : ¬ BadMidpoint (fun j => pairSM (rand j))
    · unfold obsGoodTerm
      rw [ite_eq_left_of_eq_true _ _ (eq_true hgm)]
      unfold obsHitProbOf ev obsGoodEv
      simp only [hgm, not_false_eq_true, true_and, id_eq, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc, pure_bind]
    · unfold obsGoodTerm
      rw [ite_eq_right_of_eq_false _ _ (eq_false hgm)]
      symm
      rw [← le_zero_iff]
      unfold ev obsGoodEv
      apply prEvent_bind_le_of_forall_le; intro lr
      apply prEvent_bind_le_of_forall_le; intro tbl
      apply prEvent_bind_le_of_forall_le; intro res
      rw [map_pure]
      exact (prEvent_pure_mono (Q := False) (fun h => hgm h.1)).trans (by rw [prEvent_pure_prop]; simp)
  rw [hsum_eq]
  have hmrg := (EvalDistEq.of_evalDist_eq (mergePairRand_uniform_bind positions ev)).prEvent_eq id
  rw [← hmrg]
  apply prEvent_bind_le_of_forall_le; intro sLOpen
  apply prEvent_bind_le_of_forall_le; intro sM
  apply prEvent_bind_le_of_forall_le; intro sROpen
  by_cases hgm : ¬ BadMidpoint sM
  · have hswap := obs_ev_swap h768 permutation cache1 aVec bVec positions observe sLOpen sM sROpen
    rw [(EvalDistEq.of_evalDist_eq hswap).prEvent_eq id]
    apply prEvent_bind_le_of_forall_le; intro lr
    apply prEvent_bind_le_of_forall_le; intro tbl
    apply prEvent_bind_le_of_forall_le_of_support; intro traced htraced
    have hlen := trace_run_length ⟨tableExtending cache1 tbl, permutation⟩ _ budget (hobs _ _) traced htraced
    have hle : prEvent (id <$> (($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128))) >>= fun p =>
        pure (¬ BadMidpoint sM ∧ traced.2.any (fun x => decide (∃ i ∉ positions,
          hiddenCall3 h768 aVec bVec (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x)) = true))) ≤
        prEvent ((fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
          traced.2.any (fun x => decide (∃ i ∉ positions,
            hiddenCall3 h768 aVec bVec (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x)) = true) <$>
          ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128)))) := by
      have hmp : (($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128))) >>= fun p =>
          pure (¬ BadMidpoint sM ∧ traced.2.any (fun x => decide (∃ i ∉ positions,
            hiddenCall3 h768 aVec bVec (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x)) = true)) =
          (fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 128) =>
            ¬ BadMidpoint sM ∧ traced.2.any (fun x => decide (∃ i ∉ positions,
              hiddenCall3 h768 aVec bVec (pairSalts (mergePairRand positions sLOpen sM sROpen p.1 p.2)) i = x)) = true) <$>
          ($ᵗ ((PairIdx → BitVec 128) × (PairIdx → BitVec 128))) := by
        rw [map_eq_bind_pure_comp]; rfl
      rw [hmp, prEvent_map]
      exact prEvent_mono_of_support _ _ _ (fun _ _ h => h.2)
    exact hle.trans ((trace_hit_given_good_sM h768 aVec bVec positions sLOpen sM sROpen hgm traced.2).trans
      (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left 8 hlen)) _))
  · refine le_trans ?_ zero_le
    apply prEvent_bind_le_of_forall_le; intro sLHid
    apply prEvent_bind_le_of_forall_le; intro sRHid
    unfold ev obsGoodEv
    apply prEvent_bind_le_of_forall_le; intro lr
    apply prEvent_bind_le_of_forall_le; intro tbl
    apply prEvent_bind_le_of_forall_le; intro res
    have hsmeq : (fun j => pairSM (mergePairRand positions sLOpen sM sROpen sLHid sRHid j)) = sM := by
      funext j; exact pairSM_combine _ sM _ j
    rw [map_pure, hsmeq]
    exact (prEvent_pure_mono (Q := False) (fun h => hgm h.1)).trans (by rw [prEvent_pure_prop]; simp)

private theorem prEvent_eq_tsum_ite_classical {α : Type} [DecidableEq α]
    (oa : ProbComp α) (p : α → Prop) :
    Pr{let y ← oa}[p y] = ∑' x, @ite _ (p x) (Classical.propDecidable _) (Pr{let y ← oa}[y = x]) 0 := by
  let _ : DecidablePred p := Classical.decPred p
  exact prEvent_eq_tsum_ite oa p

theorem real_ideal_ab_distance (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache1 : CompressionCache)
    (keys1 : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache1 k ≠ none → k ∈ keys1)
    (msg : Message) (aVec bVec : Index → Digest)
    (hab : ∀ (table : Compression) (i : Index),
      let c : Comp96 := fun x => tableExtending cache1 table (x.cast h768.symm)
      leafA c (msg i) = aVec i ∧ leafB c (msg i) = bVec i)
    (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (budget : Nat)
    (hobs : ∀ rt pf, PublicQueryBound (observe rt pf) budget) :
    measureTVDist
      (realObsAB h768 permutation cache1 msg positions observe)
      (idealObsAB h768 permutation cache1 aVec bVec positions observe) ≤
      2 * ((((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
           (((3 * keys1.card + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
      (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 +
      ((8 * budget : Nat) : ℝ) / 2 ^ 128 := by
  let H : Finset Index := Finset.univ \ positions
  let badEps : ENNReal :=
    (((LENGTH / 2) ^ 5 : Nat) : ENNReal) / 2 ^ 256 +
    (((3 * keys1.card + 2 * LENGTH + 1) * LENGTH : Nat) : ENNReal) / 2 ^ 192
  let treeEps : ENNReal :=
    (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ENNReal) / 2 ^ 192
  have hbad_prob : prEvent ((fun rand => BadRand h768 cache1 aVec bVec positions rand) <$>
      ($ᵗ (PairIdx → PairRand))) ≤ badEps :=
    badRand_prob_le h768 cache1 keys1 covered aVec bVec positions
  let progComp (rand : PairIdx → PairRand) (leafRand : Index → Digest) (table : Compression) : ProbComp α :=
    let tbl' := tableExtending cache1 (reprogramFinset (hiddenCall3 h768 aVec bVec (pairSalts rand)) table leafRand H)
    let tr := idealTranscriptFromAB h768 tbl' aVec bVec (pairSalts rand) leafRand positions
    fixedOracleRun ⟨tbl', permutation⟩ (observe tr.1 tr.2)
  let idealComp (rand : PairIdx → PairRand) (leafRand : Index → Digest) (table : Compression) : ProbComp α :=
    let tbl := tableExtending cache1 table
    let tr := idealTranscriptFromAB h768 tbl aVec bVec (pairSalts rand) leafRand positions
    fixedOracleRun ⟨tbl, permutation⟩ (observe tr.1 tr.2)
  let progGame : ProbComp α := do
    let rand ← $ᵗ (PairIdx → PairRand)
    let leafRand ← $ᵗ (Index → Digest)
    let table ← $ᵗ Compression
    progComp rand leafRand table
  -- Part A: `TV(realObsAB, progGame) ≤ badEps.toReal`!
  have hRealProg : measureTVDist (realObsAB h768 permutation cache1 msg positions observe) progGame ≤
      badEps.toReal := by
    have hRealEq : 𝒟[realObsAB h768 permutation cache1 msg positions observe] =
        𝒟[do let rand ← $ᵗ (PairIdx → PairRand)
             let _leafRand ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             let tr := referenceTranscript h768 (tableExtending cache1 table) msg (pairSalts rand) positions
             fixedOracleRun ⟨tableExtending cache1 table, permutation⟩ (observe tr.1 tr.2)] := by
      unfold realObsAB
      apply _root_.evalDist_bind_congr; intro rand
      exact (OracleComp.evalDist_bind_const ($ᵗ (Index → Digest)) _).symm
    rw [measureTVDist, hRealEq, ← measureTVDist]
    refine (measureTVDist_bind_left_le_prEvent_of_evalDistEq ($ᵗ (PairIdx → PairRand)) _ _
      (BadRand h768 cache1 aVec bVec positions) ?_).trans (ENNReal.toReal_mono (by finiteness) hbad_prob)
    intro rand hgood
    have hdisj : ∀ i ∉ positions, cache1 (hiddenCall3 h768 aVec bVec (pairSalts rand) i) = none := by
      intro i hi; by_contra hne; exact hgood (Or.inr (Or.inl ⟨i, hi, hne⟩))
    have hinj : Set.InjOn (hiddenCall3 h768 aVec bVec (pairSalts rand)) (H : Set Index) := by
      intro i hi i' hi' heq
      by_contra hne
      exact hgood (Or.inr (Or.inr (Or.inl ⟨i, (Finset.mem_sdiff.mp hi).2, i', (Finset.mem_sdiff.mp hi').2, hne, heq⟩)))
    apply EvalDistEq.of_evalDist_eq
    have hrep := reprogramFinset_dist (hiddenCall3 h768 aVec bVec (pairSalts rand)) H hinj
      (fun tbl lr =>
        let t := tableExtending cache1 tbl
        let tr := idealTranscriptFromAB h768 t aVec bVec (pairSalts rand) lr positions
        fixedOracleRun ⟨t, permutation⟩ (observe tr.1 tr.2))
    rw [hrep]
    apply _root_.evalDist_bind_congr; intro leafRand
    apply _root_.evalDist_bind_congr; intro table
    have htr :
        idealTranscriptFromAB h768 (tableExtending cache1 table) aVec bVec (pairSalts rand)
          (fun i => if i ∈ H then fromOut (table (hiddenCall3 h768 aVec bVec (pairSalts rand) i)) else leafRand i) positions =
        referenceTranscript h768 (tableExtending cache1 table) msg (pairSalts rand) positions := by
      rw [← idealTranscriptFromAB_eq_reference h768 (tableExtending cache1 table) msg aVec bVec (pairSalts rand) positions (hab table)]
      unfold idealTranscriptFromAB
      have hlv :
          idealLeavesFromAB (fun x => tableExtending cache1 table (x.cast h768.symm)) aVec bVec (pairSalts rand)
            (fun i => if i ∈ H then fromOut (table (hiddenCall3 h768 aVec bVec (pairSalts rand) i)) else leafRand i) positions =
          idealLeavesFromAB (fun x => tableExtending cache1 table (x.cast h768.symm)) aVec bVec (pairSalts rand)
            (fun i => tableExtending cache1 table (hiddenCall3 h768 aVec bVec (pairSalts rand) i)) positions := by
        funext i; unfold idealLeavesFromAB
        by_cases hi : i ∈ positions
        · simp [hi]
        · have hiH : i ∈ H := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
          simp only [hi, ite_false, hiH, ite_true]
          have hnone := hdisj i hi
          change fromOut (table _) = (cache1 _).getD (table _)
          rw [hnone]; rfl
      exact congrArg
        (fun lv =>
          let c : Comp96 := fun x => tableExtending cache1 table (x.cast h768.symm)
          (nodeValFromLeaves c lv 24 0, referenceProof (nodeValFromLeaves c lv) (pairSalts rand) positions))
        hlv
    dsimp only
    rw [htr]
  -- Part B: `TV(idealObsAB, progGame) ≤ badEps.toReal + treeEps.toReal + (8*budget / 2^128).toReal`!
  have hIdealProg : measureTVDist (idealObsAB h768 permutation cache1 aVec bVec positions observe) progGame ≤
      badEps.toReal + treeEps.toReal + (((8 * budget : Nat) : ENNReal) / 2 ^ 128).toReal := by
    let fullComp (salts : Index → Salt192) (leafRand : Index → Digest) : OracleComp World α := do
      let nodes ← queryTreeFromLeafFn h768 (idealLeafFn h768 aVec bVec salts leafRand positions)
      observe (nodes 24 0) (referenceProof nodes salts positions)
    have hfull_fixed : ∀ (o : Oracle) (salts : Index → Salt192) (leafRand : Index → Digest),
        fixedOracleRun o (fullComp salts leafRand) =
          let tr := idealTranscriptFromAB h768 o.compression aVec bVec salts leafRand positions
          fixedOracleRun o (observe tr.1 tr.2) := by
      intro o salts leafRand
      obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 o
        (idealLeafFn h768 aVec bVec salts leafRand positions)
        (idealLeavesFromAB (fun x => o.compression (x.cast h768.symm)) aVec bVec salts leafRand positions)
        (idealLeafFn_fixed h768 o aVec bVec salts leafRand positions)
      unfold fullComp
      rw [fixed_oracle_run_bind, hrun, pure_bind]
      have hrt : nodes 24 0 = (idealTranscriptFromAB h768 o.compression aVec bVec salts leafRand positions).1 :=
        hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega)
      have hpf : referenceProof nodes salts positions =
          (idealTranscriptFromAB h768 o.compression aVec bVec salts leafRand positions).2 :=
        referenceProof_congr_nodes _ _ hval salts positions
      rw [hrt, hpf]
    -- Pointwise hit bound for any fixed `(rand, leafRand, table)`:
    have hpt : ∀ (rand : PairIdx → PairRand) (leafRand : Index → Digest) (table : Compression),
        measureTVDist (idealComp rand leafRand table) (progComp rand leafRand table) ≤
        (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
          flaggedRun ⟨tableExtending cache1 table, permutation⟩
            (marksHidden3 h768 aVec bVec positions (pairSalts rand))
            (fullComp (pairSalts rand) leafRand))).toReal := by
      intro rand leafRand table
      unfold idealComp progComp
      rw [← hfull_fixed ⟨tableExtending cache1 table, permutation⟩ (pairSalts rand) leafRand,
        ← hfull_fixed ⟨tableExtending cache1 (reprogramFinset (hiddenCall3 h768 aVec bVec (pairSalts rand)) table leafRand H), permutation⟩ (pairSalts rand) leafRand]
      apply oracle_change_distance_le_hit
      intro query hunm
      rcases query with coins | pq
      · simp only [Oracle.world, QueryImpl.add_apply_inl]
      · rcases pq with x | permq
        · simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr, pure_inj]
          have hnot : ∀ i ∈ H, hiddenCall3 h768 aVec bVec (pairSalts rand) i ≠ x := by
            intro i hi heq
            have hni : i ∉ positions := (Finset.mem_sdiff.mp hi).2
            simp [marksHidden3] at hunm
            exact hunm i hni heq
          change (cache1 x).getD (table x) = (cache1 x).getD (reprogramFinset _ table leafRand H x)
          rw [reprogramFinset_not_mem _ table leafRand H x hnot]
        · rcases permq <;> simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr]
    -- Split `flaggedRun` on `fullComp` into `treeFlag` + `obsFlag`!
    let treeHitProb := treeHitProbOf h768 permutation cache1 aVec bVec positions
    let obsHitProb := obsHitProbOf h768 permutation cache1 aVec bVec positions observe
    have hsplit_rand : ∀ rand : PairIdx → PairRand,
        measureTVDist
          (do let leafRand ← $ᵗ (Index → Digest); let table ← $ᵗ Compression; idealComp rand leafRand table)
          (do let leafRand ← $ᵗ (Index → Digest); let table ← $ᵗ Compression; progComp rand leafRand table) ≤
        (treeHitProb rand).toReal + (obsHitProb rand).toReal := by
      intro rand
      have havg := distance_bind_le_averaged_bad
        (do let leafRand ← $ᵗ (Index → Digest); let table ← $ᵗ Compression; pure (leafRand, table))
        (fun p => idealComp rand p.1 p.2)
        (fun p => progComp rand p.1 p.2)
        (fun p => flaggedRun ⟨tableExtending cache1 p.2, permutation⟩
          (marksHidden3 h768 aVec bVec positions (pairSalts rand)) (fullComp (pairSalts rand) p.1))
        (fun ⟨lr, tbl⟩ => hpt rand lr tbl)
      have hfl1 : 𝒟[do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; idealComp rand lr tbl] =
          𝒟[(do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; pure (lr, tbl)) >>= fun p => idealComp rand p.1 p.2] := by
        simp [bind_assoc]
      have hfl2 : 𝒟[do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; progComp rand lr tbl] =
          𝒟[(do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; pure (lr, tbl)) >>= fun p => progComp rand p.1 p.2] := by
        simp [bind_assoc]
      rw [measureTVDist, hfl1, hfl2, ← measureTVDist]
      refine havg.trans ?_
      simp only [treeHitProb, obsHitProb, treeHitProbOf, obsHitProbOf]
      rw [← ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)]
      apply ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩)
      have hbind_eq :
          ((do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; pure (lr, tbl)) >>= fun p =>
            flaggedRun ⟨tableExtending cache1 p.2, permutation⟩
              (marksHidden3 h768 aVec bVec positions (pairSalts rand)) (fullComp (pairSalts rand) p.1)) =
          (do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression
              flaggedRun ⟨tableExtending cache1 tbl, permutation⟩
                (marksHidden3 h768 aVec bVec positions (pairSalts rand)) (fullComp (pairSalts rand) lr)) := by
        simp [bind_assoc]
      rw [hbind_eq]
      simp only [map_bind, prEvent_bind_eq_tsum_prEvent]
      rw [← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum; intro lr
      rw [← mul_add, ← ENNReal.tsum_add]
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply ENNReal.tsum_le_tsum; intro tbl
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ zero_le
      let o : Oracle := ⟨tableExtending cache1 tbl, permutation⟩
      let m := marksHidden3 h768 aVec bVec positions (pairSalts rand)
      have hbind_flag : ∀ {β γ : Type} (A : OracleComp World β) (B : β → OracleComp World γ) (f : Bool),
          flaggedRun o m (A >>= B) f = (do let r1 ← flaggedRun o m A f; flaggedRun o m (B r1.1) r1.2.2) := by
        intro β γ A B f; simp [flaggedRun, simulateQ_bind, StateT.run_bind]
      obtain ⟨nodes, htrun, hv⟩ := queryTreeFromLeafFn_fixed h768 o
        (idealLeafFn h768 aVec bVec (pairSalts rand) lr positions)
        (idealLeavesFromAB (fun x => o.compression (x.cast h768.symm)) aVec bVec (pairSalts rand) lr positions)
        (idealLeafFn_fixed h768 o aVec bVec (pairSalts rand) lr positions)
      have htrEq : (nodes 24 0, referenceProof nodes (pairSalts rand) positions) =
          idealTranscriptFromAB h768 o.compression aVec bVec (pairSalts rand) lr positions :=
        Prod.ext (hv 24 (le_refl _) 0 (by rw [levelSize_24]; omega))
          (referenceProof_congr_nodes _ _ hv (pairSalts rand) positions)
      change prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
        flaggedRun o m ((queryTreeFromLeafFn h768 (idealLeafFn h768 aVec bVec (pairSalts rand) lr positions)) >>= fun nd =>
          observe (nd 24 0) (referenceProof nd (pairSalts rand) positions)) false) ≤ _
      rw [hbind_flag]
      exact prEvent_bind_le_prEvent_add_of_support
        (flaggedRun o m (queryTreeFromLeafFn h768 (idealLeafFn h768 aVec bVec (pairSalts rand) lr positions)))
        (fun r1 => flaggedRun o m (observe (r1.1 24 0) (referenceProof r1.1 (pairSalts rand) positions)) r1.2.2)
        (fun r1 => r1.2.2 = true) (fun r2 => r2.2.2 = true)
        (fun r1 hr1 hnot => by
          have hfalse : r1.2.2 = false := Bool.eq_false_iff.mpr hnot
          rw [hfalse]
          have hproj : r1.1 ∈ support (Prod.fst <$> flaggedRun o m
              (queryTreeFromLeafFn h768 (idealLeafFn h768 aVec bVec (pairSalts rand) lr positions))) := by
            rw [support_map]; exact ⟨r1, hr1, rfl⟩
          rw [flagged_run_projection, htrun, support_pure, Set.mem_singleton_iff] at hproj
          have h1 : r1.1 24 0 = (idealTranscriptFromAB h768 o.compression aVec bVec (pairSalts rand) lr positions).1 := by
            rw [hproj]; exact congrArg Prod.fst htrEq
          have h2 : referenceProof r1.1 (pairSalts rand) positions =
              (idealTranscriptFromAB h768 o.compression aVec bVec (pairSalts rand) lr positions).2 := by
            rw [hproj]; exact congrArg Prod.snd htrEq
          rw [h1, h2])
    -- Bound `treeHitProb rand ≤ treeEps` and averaged `¬BadMidpoint sM ∧ ObsHit ≤ 8 * budget / 2^128`!
    have hTreeGood : ∀ rand : PairIdx → PairRand, ¬ BadRand h768 cache1 aVec bVec positions rand →
        treeHitProb rand ≤ treeEps :=
      fun rand hgood => tree_hit_given_good_rand h768 permutation cache1 aVec bVec positions rand hgood
    let badInd (rand : PairIdx → PairRand) : ENNReal :=
      @ite _ (BadRand h768 cache1 aVec bVec positions rand) (Classical.propDecidable _) 1 0
    let obsGood (rand : PairIdx → PairRand) : ENNReal :=
      obsGoodTerm h768 permutation cache1 aVec bVec positions observe rand
    have hObsGood :
        (∑ rand : PairIdx → PairRand,
          Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] * obsGood rand) ≤
        ((8 * budget : Nat) : ENNReal) / 2 ^ 128 :=
      obs_hit_given_good_sM h768 permutation cache1 aVec bVec positions observe budget hobs
    -- Put the 3-term sum over `rand` together!
    refine (measureTVDist_bind_left_le_tsum ($ᵗ (PairIdx → PairRand))
      (fun rand => do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; idealComp rand lr tbl)
      (fun rand => do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; progComp rand lr tbl)).trans ?_
    rw [tsum_fintype]
    have hpt_rand : ∀ rand : PairIdx → PairRand,
        (Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand]).toReal *
          measureTVDist
            (do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; idealComp rand lr tbl)
            (do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; progComp rand lr tbl) ≤
        (Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] * badInd rand).toReal +
        (Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] * treeEps).toReal +
        (Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] * obsGood rand).toReal := by
      intro rand
      have h2nz : ∀ n : Nat, (2 : ENNReal) ^ n ≠ 0 := fun n => pow_ne_zero n (by norm_num)
      have ht_ne : treeEps ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (h2nz 192)
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_add, ← mul_add]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      by_cases hb : BadRand h768 cache1 aVec bVec positions rand
      · have hbi : badInd rand = 1 := ite_eq_left_of_eq_true _ _ (eq_true hb)
        rw [hbi, ENNReal.toReal_one]
        have hle1 : measureTVDist
            (do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; idealComp rand lr tbl)
            (do let lr ← $ᵗ (Index → Digest); let tbl ← $ᵗ Compression; progComp rand lr tbl) ≤ 1 :=
          measureTVDist_le_one _ _
        linarith [ENNReal.toReal_nonneg (a := treeEps), ENNReal.toReal_nonneg (a := obsGood rand)]
      · have hgm : ¬ BadMidpoint (fun j => pairSM (rand j)) := fun hm => hb (Or.inl hm)
        have hbi : badInd rand = 0 := ite_eq_right_of_eq_false _ _ (eq_false hb)
        have hog : obsGood rand = obsHitProb rand := ite_eq_left_of_eq_true _ _ (eq_true hgm)
        rw [hbi, hog, ENNReal.toReal_zero, zero_add]
        exact (hsplit_rand rand).trans
          (add_le_add (ENNReal.toReal_mono ht_ne (hTreeGood rand hb)) le_rfl)
    refine (Finset.sum_le_sum (fun rand _ => hpt_rand rand)).trans ?_
    have h2nz : ∀ n : Nat, (2 : ENNReal) ^ n ≠ 0 := fun n => pow_ne_zero n (by norm_num)
    have htree_ne : treeEps ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (h2nz 192)
    have hbadEps_ne : badEps ≠ ⊤ := ENNReal.add_ne_top.mpr
      ⟨ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (h2nz 256),
       ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (h2nz 192)⟩
    have hobsEps_ne : ((8 * budget : Nat) : ENNReal) / 2 ^ 128 ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (h2nz 128)
    have hbad_ne : ∀ rand, badInd rand ≠ ⊤ := fun rand => by
      unfold badInd
      by_cases hb : BadRand h768 cache1 aVec bVec positions rand
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]; exact ENNReal.one_ne_top
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]; exact ENNReal.zero_ne_top
    have hogs_ne : ∀ rand, obsGood rand ≠ ⊤ := fun rand => by
      unfold obsGood obsGoodTerm obsHitProbOf
      by_cases hgm : ¬ BadMidpoint (fun j => pairSM (rand j))
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hgm)]; exact prEvent_ne_top _
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hgm)]; exact ENNReal.zero_ne_top
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← ENNReal.toReal_sum (fun rand _ => ENNReal.mul_ne_top (prEvent_ne_top _) (hbad_ne rand)),
      ← ENNReal.toReal_sum (fun _ _ => ENNReal.mul_ne_top (prEvent_ne_top _) htree_ne),
      ← ENNReal.toReal_sum (fun rand _ => ENNReal.mul_ne_top (prEvent_ne_top _) (hogs_ne rand))]
    have hsum1 : (∑ rand : PairIdx → PairRand,
        Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] * badInd rand) ≤ badEps := by
      have heq : (∑ rand : PairIdx → PairRand,
          Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] * badInd rand) =
          prEvent ((fun rand => BadRand h768 cache1 aVec bVec positions rand) <$> ($ᵗ (PairIdx → PairRand))) := by
        rw [prEvent_eq_tsum_ite_classical ($ᵗ (PairIdx → PairRand))
          (BadRand h768 cache1 aVec bVec positions), tsum_fintype]
        apply Finset.sum_congr rfl; intro rand _
        unfold badInd
        by_cases hb : BadRand h768 cache1 aVec bVec positions rand
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hb), ite_eq_left_of_eq_true _ _ (eq_true hb), mul_one]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hb), ite_eq_right_of_eq_false _ _ (eq_false hb), mul_zero]
      rw [heq]; exact hbad_prob
    have hsum2 : (∑ rand : PairIdx → PairRand,
        Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand] * treeEps) = treeEps := by
      rw [← Finset.sum_mul]
      have htot : (∑ rand : PairIdx → PairRand, Pr{let x ← $ᵗ (PairIdx → PairRand)}[x = rand]) = 1 :=
        (tsum_fintype _).symm.trans (OracleComp.tsum_prEvent_eq_one ($ᵗ (PairIdx → PairRand)))
      rw [htot, one_mul]
    exact add_le_add
      (add_le_add (ENNReal.toReal_mono hbadEps_ne hsum1) (by rw [hsum2]))
      (ENNReal.toReal_mono hobsEps_ne hObsGood)
  -- Triangle inequality: `TV(Real, Ideal) ≤ TV(Real, Prog) + TV(Prog, Ideal)`!
  rw [measureTVDist_comm] at hIdealProg
  refine ((measureTVDist_triangle _ progGame _).trans (add_le_add hRealProg hIdealProg)).trans ?_
  have hbad_toReal : badEps.toReal =
      (((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
      (((3 * keys1.card + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192 := by
    simp only [badEps]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have htree_toReal : treeEps.toReal =
      (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 := by
    simp only [treeEps, ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have hobs_toReal : (((8 * budget : Nat) : ENNReal) / 2 ^ 128).toReal =
      ((8 * budget : Nat) : ℝ) / 2 ^ 128 := by
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  rw [hbad_toReal, htree_toReal, hobs_toReal]
  exact le_of_eq (by ring)

/-! ### 6. Lift to Stage-1 `cache0`, Zero Ideal Distance, Arithmetic, & Master Theorem -/


def realObs0 (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache0 : CompressionCache) (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let rand ← $ᵗ (PairIdx → PairRand)
  let tr := referenceTranscript h768 (tableExtending cache0 table) msg (pairSalts rand) positions
  fixedOracleRun ⟨tableExtending cache0 table, permutation⟩ (observe tr.1 tr.2)

def idealObs0 (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache0 : CompressionCache) (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let rand ← $ᵗ (PairIdx → PairRand)
  let leafRand ← $ᵗ (Index → Digest)
  let tr := idealTranscript h768 (tableExtending cache0 table) msg (pairSalts rand) leafRand positions
  fixedOracleRun ⟨tableExtending cache0 table, permutation⟩ (observe tr.1 tr.2)

theorem idealObs0_eq_of_agree (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache0 : CompressionCache) (m0 m1 : Message) (positions : Positions)
    (hagree : ∀ i ∈ positions, m0 i = m1 i)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) :
    idealObs0 h768 permutation cache0 m0 positions observe =
      idealObs0 h768 permutation cache0 m1 positions observe := by
  unfold idealObs0
  apply bind_congr; intro table
  apply bind_congr; intro rand
  apply bind_congr; intro leafRand
  rw [idealTranscript_congr_opened_msg h768 (tableExtending cache0 table) m0 m1 (pairSalts rand) leafRand positions hagree]

private theorem realObs0_stage (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache0 : CompressionCache) (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) :
    𝒟[realObs0 h768 permutation cache0 msg positions observe] =
      𝒟[do let (_, cache1) ← compressionRun permutation (queryAllUnsalted h768 msg) cache0
           realObsAB h768 permutation cache1 msg positions observe] := by
  let realCont : OracleComp World α := do
    let rand ← (liftM ($ᵗ (PairIdx → PairRand)) : OracleComp World (PairIdx → PairRand))
    let nodes ← queryTreeFromLeafFn h768 (fun i => do
      let (a, b) ← queryUnsaltedLeaf h768 (msg i)
      queryCompress h768 (leafFinalInput i a b (pairSalts rand i)))
    observe (nodes 24 0) (referenceProof nodes (pairSalts rand) positions)
  have hreal_cont_fixed : ∀ (o : Oracle),
      fixedOracleRun o realCont =
        ($ᵗ (PairIdx → PairRand)) >>= fun rand =>
          let tr := referenceTranscript h768 o.compression msg (pairSalts rand) positions
          fixedOracleRun o (observe tr.1 tr.2) := by
    intro o
    unfold realCont
    rw [fixed_oracle_run_bind, fixed_oracle_run_coins]
    apply bind_congr; intro rand
    obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 o
      (fun i => do let (a, b) ← queryUnsaltedLeaf h768 (msg i); queryCompress h768 (leafFinalInput i a b (pairSalts rand i)))
      (fun i => leafDigest (fun x => o.compression (x.cast h768.symm)) i (pairSalts rand i) (msg i))
      (fun i => by
        rw [fixed_oracle_run_bind, queryUnsaltedLeaf_fixed, pure_bind, queryCompress_fixed]; rfl)
    rw [fixed_oracle_run_bind, hrun, pure_bind]
    have hrt : nodes 24 0 = (referenceTranscript h768 o.compression msg (pairSalts rand) positions).1 :=
      hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega)
    have hpf : referenceProof nodes (pairSalts rand) positions =
        (referenceTranscript h768 o.compression msg (pairSalts rand) positions).2 :=
      referenceProof_congr_nodes _ _ hval (pairSalts rand) positions
    rw [hrt, hpf]
  have h1 : 𝒟[realObs0 h768 permutation cache0 msg positions observe] =
      𝒟[do let table ← $ᵗ Compression
           fixedOracleRun ⟨tableExtending cache0 table, permutation⟩
             (queryAllUnsalted h768 msg >>= fun _ => realCont)] := by
    unfold realObs0
    apply _root_.evalDist_bind_congr; intro table
    rw [fixed_oracle_run_bind, queryAllUnsalted_fixed, pure_bind, hreal_cont_fixed]
  rw [h1, ← compression_sampling_equivalence permutation (queryAllUnsalted h768 msg >>= fun _ => realCont) cache0,
    compression_run_bind, map_bind]
  apply _root_.evalDist_bind_congr; rintro ⟨ab, cache1⟩
  rw [compression_sampling_equivalence permutation realCont cache1]
  unfold realObsAB
  trans 𝒟[do let table ← $ᵗ Compression
             let rand ← $ᵗ (PairIdx → PairRand)
             let tr := referenceTranscript h768 (tableExtending cache1 table) msg (pairSalts rand) positions
             fixedOracleRun ⟨tableExtending cache1 table, permutation⟩ (observe tr.1 tr.2)]
  · apply _root_.evalDist_bind_congr; intro table; rw [hreal_cont_fixed]
  · exact distribution_bind_comm ($ᵗ Compression) ($ᵗ (PairIdx → PairRand)) _

private theorem idealObs0_stage (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache0 : CompressionCache) (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) :
    𝒟[idealObs0 h768 permutation cache0 msg positions observe] =
      𝒟[do let (ab, cache1) ← compressionRun permutation (queryAllUnsalted h768 msg) cache0
           idealObsAB h768 permutation cache1 ab.1 ab.2 positions observe] := by
  let idealCont : ((Index → Digest) × (Index → Digest)) → OracleComp World α := fun ab => do
    let rand ← (liftM ($ᵗ (PairIdx → PairRand)) : OracleComp World (PairIdx → PairRand))
    let leafRand ← (liftM ($ᵗ (Index → Digest)) : OracleComp World (Index → Digest))
    let nodes ← queryTreeFromLeafFn h768 (idealLeafFn h768 ab.1 ab.2 (pairSalts rand) leafRand positions)
    observe (nodes 24 0) (referenceProof nodes (pairSalts rand) positions)
  have hideal_cont_fixed : ∀ (o : Oracle) (ab : (Index → Digest) × (Index → Digest)),
      fixedOracleRun o (idealCont ab) =
        (do let rand ← $ᵗ (PairIdx → PairRand)
            let leafRand ← $ᵗ (Index → Digest)
            let tr := idealTranscriptFromAB h768 o.compression ab.1 ab.2 (pairSalts rand) leafRand positions
            fixedOracleRun o (observe tr.1 tr.2)) := by
    intro o ab
    unfold idealCont
    rw [fixed_oracle_run_bind, fixed_oracle_run_coins]
    apply bind_congr; intro rand
    rw [fixed_oracle_run_bind, fixed_oracle_run_coins]
    apply bind_congr; intro leafRand
    obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 o
      (idealLeafFn h768 ab.1 ab.2 (pairSalts rand) leafRand positions)
      (idealLeavesFromAB (fun x => o.compression (x.cast h768.symm)) ab.1 ab.2 (pairSalts rand) leafRand positions)
      (idealLeafFn_fixed h768 o ab.1 ab.2 (pairSalts rand) leafRand positions)
    rw [fixed_oracle_run_bind, hrun, pure_bind]
    have hrt : nodes 24 0 = (idealTranscriptFromAB h768 o.compression ab.1 ab.2 (pairSalts rand) leafRand positions).1 :=
      hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega)
    have hpf : referenceProof nodes (pairSalts rand) positions =
        (idealTranscriptFromAB h768 o.compression ab.1 ab.2 (pairSalts rand) leafRand positions).2 :=
      referenceProof_congr_nodes _ _ hval (pairSalts rand) positions
    rw [hrt, hpf]
  have h1 : 𝒟[idealObs0 h768 permutation cache0 msg positions observe] =
      𝒟[do let table ← $ᵗ Compression
           fixedOracleRun ⟨tableExtending cache0 table, permutation⟩
             (queryAllUnsalted h768 msg >>= idealCont)] := by
    unfold idealObs0
    apply _root_.evalDist_bind_congr; intro table
    rw [fixed_oracle_run_bind, queryAllUnsalted_fixed, pure_bind, hideal_cont_fixed]
    apply _root_.evalDist_bind_congr; intro rand
    apply _root_.evalDist_bind_congr; intro leafRand
    dsimp only
    have htrEq :
        idealTranscriptFromAB h768 (tableExtending cache0 table)
          (fun i => leafA (oracleComp96 h768 ⟨tableExtending cache0 table, permutation⟩) (msg i))
          (fun i => leafB (oracleComp96 h768 ⟨tableExtending cache0 table, permutation⟩) (msg i))
          (pairSalts rand) leafRand positions =
        idealTranscript h768 (tableExtending cache0 table) msg (pairSalts rand) leafRand positions :=
      idealTranscriptFromAB_eq_ideal h768 (tableExtending cache0 table) msg _ _ (pairSalts rand) leafRand positions
        (fun i => ⟨rfl, rfl⟩)
    rw [htrEq]
  rw [h1, ← compression_sampling_equivalence permutation (queryAllUnsalted h768 msg >>= idealCont) cache0,
    compression_run_bind, map_bind]
  apply _root_.evalDist_bind_congr; rintro ⟨ab, cache1⟩
  rw [compression_sampling_equivalence permutation (idealCont ab) cache1]
  unfold idealObsAB
  trans 𝒟[do let table ← $ᵗ Compression
             let rand ← $ᵗ (PairIdx → PairRand)
             let leafRand ← $ᵗ (Index → Digest)
             let tr := idealTranscriptFromAB h768 (tableExtending cache1 table) ab.1 ab.2 (pairSalts rand) leafRand positions
             fixedOracleRun ⟨tableExtending cache1 table, permutation⟩ (observe tr.1 tr.2)]
  · apply _root_.evalDist_bind_congr; intro table; rw [hideal_cont_fixed]
  · rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ (PairIdx → PairRand))]
    apply _root_.evalDist_bind_congr; intro rand
    exact distribution_bind_comm ($ᵗ Compression) ($ᵗ (Index → Digest)) _

private theorem measureTVDist_bind_left_le_of_support {α β : Type} (mx : ProbComp α)
    (f g : α → ProbComp β) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ x ∈ support mx, measureTVDist (f x) (g x) ≤ δ) :
    measureTVDist (mx >>= f) (mx >>= g) ≤ δ := by
  rw [bind_eq_attach_bind mx, bind_eq_attach_bind mx]
  exact measureTVDist_bind_left_le_of_forall_le _ _ _ hδ (fun x => h x.1 x.2)

theorem real_ideal_from_cache0 (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache0 : CompressionCache) (keys0 : Finset (BitVec COMPRESSION_INPUT_LENGTH))
    (covered0 : ∀ k, cache0 k ≠ none → k ∈ keys0)
    (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (budget : Nat)
    (hobs : ∀ rt pf, PublicQueryBound (observe rt pf) budget) :
    measureTVDist
      (realObs0 h768 permutation cache0 msg positions observe)
      (idealObs0 h768 permutation cache0 msg positions observe) ≤
      2 * ((((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
           (((3 * (keys0.card + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
      (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 +
      ((8 * budget : Nat) : ℝ) / 2 ^ 128 := by
  rw [measureTVDist, realObs0_stage h768 permutation cache0 msg positions observe,
    idealObs0_stage h768 permutation cache0 msg positions observe, ← measureTVDist]
  have h2nn : ∀ n : Nat, (0 : ℝ) ≤ (2 : ℝ) ^ n := fun n => pow_nonneg zero_le_two n
  have hnonneg :
      (0 : ℝ) ≤
        2 * ((((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
             (((3 * (keys0.card + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
        (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 +
        ((8 * budget : Nat) : ℝ) / 2 ^ 128 :=
    add_nonneg
      (add_nonneg
        (mul_nonneg zero_le_two
          (add_nonneg
            (div_nonneg (Nat.cast_nonneg _) (h2nn 256))
            (div_nonneg (Nat.cast_nonneg _) (h2nn 192))))
        (div_nonneg (Nat.cast_nonneg _) (h2nn 192)))
      (div_nonneg (Nat.cast_nonneg _) (h2nn 128))
  apply measureTVDist_bind_left_le_of_support _ _ _ hnonneg
  rintro ⟨⟨aVec, bVec⟩, cache1⟩ hreach
  obtain ⟨keys1, hcard1, hcov1⟩ := compression_cache_covered permutation (queryAllUnsalted h768 msg)
    (3 * LENGTH) (queryAllUnsalted_bound h768 msg) cache0 keys0 covered0 ((aVec, bVec), cache1) hreach
  have hab := queryAllUnsalted_compressionRun_agrees h768 permutation msg cache0 ((aVec, bVec), cache1) hreach
  have hd := real_ideal_ab_distance h768 permutation cache1 keys1 hcov1 msg aVec bVec hab positions observe budget hobs
  refine hd.trans ?_
  have hnat : (3 * keys1.card + 2 * LENGTH + 1) * LENGTH ≤
      (3 * (keys0.card + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH :=
    Nat.mul_le_mul_right LENGTH (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hcard1) _) 1)
  have hdiv : (((3 * keys1.card + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192 ≤
      (((3 * (keys0.card + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192 :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hnat) (h2nn 192)
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hdiv) zero_le_two) le_rfl) le_rfl

theorem smpls40_hiding_arithmetic (known budget : Nat) (hknown : known ≤ budget) :
    2 * (2 * ((((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
              (((3 * (known + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
         (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 +
         ((8 * budget : Nat) : ℝ) / 2 ^ 128) ≤
    ((budget : ℝ) + 1) / 2 ^ HIDING_SECURITY_BITS := by
  have hk : (known : ℝ) ≤ budget := Nat.cast_le.mpr hknown
  have hb : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  have h2pos : ∀ n : Nat, (0 : ℝ) < (2 : ℝ) ^ n := fun n => by positivity
  have hL : (LENGTH : ℝ) = (2 : ℝ) ^ 24 := by norm_num [LENGTH, LOG_LENGTH]
  have hL2 : ((LENGTH / 2 : Nat) : ℝ) = (2 : ℝ) ^ 23 := by norm_num [LENGTH, LOG_LENGTH]
  have hT_nat : 2 * LENGTH + 2 * IDEAL_TREE_BUDGET ≤ 2 ^ 27 := by
    unfold IDEAL_TREE_BUDGET LENGTH LOG_LENGTH; omega
  have hT : ((2 * LENGTH + 2 * IDEAL_TREE_BUDGET : Nat) : ℝ) ≤ (2 : ℝ) ^ 27 := by exact_mod_cast hT_nat
  have hC_nat : 11 * LENGTH + 1 ≤ 2 ^ 28 := by unfold LENGTH LOG_LENGTH; omega
  have hC : ((11 * LENGTH + 1 : Nat) : ℝ) ≤ (2 : ℝ) ^ 28 := by exact_mod_cast hC_nat
  have hstep :
      2 * (2 * ((((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
                (((3 * (known + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
           (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 +
           ((8 * budget : Nat) : ℝ) / 2 ^ 128) ≤
      4 * (((LENGTH / 2 : Nat) : ℝ) ^ 5 / 2 ^ 256) +
      12 * ((budget : ℝ) * (LENGTH : ℝ) / 2 ^ 192) +
      4 * (((11 * LENGTH + 1 : Nat) : ℝ) * (LENGTH : ℝ) / 2 ^ 192) +
      2 * (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET : Nat) : ℝ) * (LENGTH : ℝ) / 2 ^ 192) +
      16 * ((budget : ℝ) / 2 ^ 128) := by
    have hlin : ((3 * (known + 3 * LENGTH) + 2 * LENGTH + 1 : Nat) : ℝ) ≤
        3 * (budget : ℝ) + ((11 * LENGTH + 1 : Nat) : ℝ) := by push_cast; linarith
    have hmul : (((3 * (known + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) ≤
        (3 * (budget : ℝ) + ((11 * LENGTH + 1 : Nat) : ℝ)) * (LENGTH : ℝ) := by
      rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_right hlin (Nat.cast_nonneg _)
    have hdiv := div_le_div_of_nonneg_right hmul (h2pos 192).le
    push_cast at hdiv ⊢
    linarith
  refine hstep.trans ?_
  have hp128 : (2 : ℝ) ^ 128 = 2 ^ 8 * 2 ^ 120 := by rw [← pow_add]
  have hp192 : (2 : ℝ) ^ 192 = 2 ^ 72 * 2 ^ 120 := by rw [← pow_add]
  have hp256 : (2 : ℝ) ^ 256 = 2 ^ 136 * 2 ^ 120 := by rw [← pow_add]
  -- Budget terms: 16 * b / 2^128 + 12 * b * 2^24 / 2^192 ≤ b / 2^120!
  have hB1 : 16 * ((budget : ℝ) / 2 ^ 128) ≤ (1 / 2) * ((budget : ℝ) / 2 ^ 120) := by
    rw [hp128]
    have hc : (16 : ℝ) / (2 : ℝ) ^ 8 ≤ 1 / 2 := by norm_num
    have heq : 16 * ((budget : ℝ) / ((2 : ℝ) ^ 8 * (2 : ℝ) ^ 120)) =
        ((16 : ℝ) / (2 : ℝ) ^ 8) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by ring
    rw [heq]; exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hB2 : 12 * ((budget : ℝ) * (LENGTH : ℝ) / 2 ^ 192) ≤ (1 / 2) * ((budget : ℝ) / 2 ^ 120) := by
    rw [hL, hp192]
    have hnum : (12 : ℝ) * (2 : ℝ) ^ 24 ≤ (2 : ℝ) ^ 28 := by
      have : (16 : ℝ) * (2 : ℝ) ^ 24 = (2 : ℝ) ^ 28 := by
        have h16 : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
        rw [h16, ← pow_add]
      linarith [h2pos 24]
    have h72 : (2 : ℝ) ^ 28 / (2 : ℝ) ^ 72 ≤ 1 / 2 := by
      have : (2 : ℝ) ^ 72 = (2 : ℝ) ^ 28 * (2 : ℝ) ^ 44 := by rw [← pow_add]
      rw [this, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 28))]
      have h44 : (2 : ℝ) ≤ (2 : ℝ) ^ 44 := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 1 ≤ 44)
      exact one_div_le_one_div_of_le (by norm_num) h44
    have heq : 12 * ((budget : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120)) =
        (((12 : ℝ) * (2 : ℝ) ^ 24) / (2 : ℝ) ^ 72) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right hnum (h2pos 72).le).trans h72) (by positivity)
  -- Constant terms: each ≤ (1 / 4) * (1 / 2^120)!
  have hK1 : 4 * (((LENGTH / 2 : Nat) : ℝ) ^ 5 / 2 ^ 256) ≤ (1 / 4) * (1 / (2 : ℝ) ^ 120) := by
    rw [hL2, hp256]
    have hnum : (4 : ℝ) * ((2 : ℝ) ^ 23) ^ 5 = (2 : ℝ) ^ 117 := by
      rw [← pow_mul, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add]
    have h136 : (2 : ℝ) ^ 117 / (2 : ℝ) ^ 136 ≤ 1 / 4 := by
      have : (2 : ℝ) ^ 136 = (2 : ℝ) ^ 117 * (2 : ℝ) ^ 19 := by rw [← pow_add]
      rw [this, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 117))]
      have h19 : (4 : ℝ) ≤ (2 : ℝ) ^ 19 := by
        have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        rw [this]; exact pow_le_pow_right₀ (by norm_num) (by decide)
      exact one_div_le_one_div_of_le (by norm_num) h19
    have heq : 4 * (((2 : ℝ) ^ 23) ^ 5 / ((2 : ℝ) ^ 136 * (2 : ℝ) ^ 120)) =
        ((4 * ((2 : ℝ) ^ 23) ^ 5) / (2 : ℝ) ^ 136) * (1 / (2 : ℝ) ^ 120) := by ring
    rw [heq, hnum]
    exact mul_le_mul_of_nonneg_right h136 (by positivity)
  have hK2 : 4 * (((11 * LENGTH + 1 : Nat) : ℝ) * (LENGTH : ℝ) / 2 ^ 192) ≤ (1 / 4) * (1 / (2 : ℝ) ^ 120) := by
    rw [hL, hp192]
    have hnum : 4 * (((11 * LENGTH + 1 : Nat) : ℝ) * (2 : ℝ) ^ 24) ≤ (2 : ℝ) ^ 54 := by
      have h54 : (4 : ℝ) * ((2 : ℝ) ^ 28 * (2 : ℝ) ^ 24) = (2 : ℝ) ^ 54 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add, ← pow_add]
      linarith [mul_le_mul_of_nonneg_right hC (h2pos 24).le]
    have h72 : (2 : ℝ) ^ 54 / (2 : ℝ) ^ 72 ≤ 1 / 4 := by
      have : (2 : ℝ) ^ 72 = (2 : ℝ) ^ 54 * (2 : ℝ) ^ 18 := by rw [← pow_add]
      rw [this, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 54))]
      have h18 : (4 : ℝ) ≤ (2 : ℝ) ^ 18 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) (by decide)
      exact one_div_le_one_div_of_le (by norm_num) h18
    have heq : 4 * (((11 * LENGTH + 1 : Nat) : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120)) =
        ((4 * (((11 * LENGTH + 1 : Nat) : ℝ) * (2 : ℝ) ^ 24)) / (2 : ℝ) ^ 72) * (1 / (2 : ℝ) ^ 120) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right hnum (h2pos 72).le).trans h72) (by positivity)
  have hK3 : 2 * (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET : Nat) : ℝ) * (LENGTH : ℝ) / 2 ^ 192) ≤
      (1 / 4) * (1 / (2 : ℝ) ^ 120) := by
    rw [hL, hp192]
    have hnum : 2 * (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24) ≤ (2 : ℝ) ^ 52 := by
      have h52 : (2 : ℝ) * ((2 : ℝ) ^ 27 * (2 : ℝ) ^ 24) = (2 : ℝ) ^ 52 := by
        rw [← pow_add, ← pow_succ']
      linarith [mul_le_mul_of_nonneg_right hT (h2pos 24).le]
    have h72 : (2 : ℝ) ^ 52 / (2 : ℝ) ^ 72 ≤ 1 / 4 := by
      have : (2 : ℝ) ^ 72 = (2 : ℝ) ^ 52 * (2 : ℝ) ^ 20 := by rw [← pow_add]
      rw [this, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 52))]
      have h20 : (4 : ℝ) ≤ (2 : ℝ) ^ 20 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) (by decide)
      exact one_div_le_one_div_of_le (by norm_num) h20
    have heq : 2 * (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120)) =
        ((2 * (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24)) / (2 : ℝ) ^ 72) * (1 / (2 : ℝ) ^ 120) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right hnum (h2pos 72).le).trans h72) (by positivity)
  have hRHS : ((budget : ℝ) + 1) / (2 : ℝ) ^ HIDING_SECURITY_BITS =
      ((1 / 2) * ((budget : ℝ) / (2 : ℝ) ^ 120) + (1 / 2) * ((budget : ℝ) / (2 : ℝ) ^ 120)) +
      ((1 / 4) * (1 / (2 : ℝ) ^ 120) + (1 / 4) * (1 / (2 : ℝ) ^ 120) +
       (1 / 4) * (1 / (2 : ℝ) ^ 120) + (1 / 4) * (1 / (2 : ℝ) ^ 120)) := by
    unfold HIDING_SECURITY_BITS; ring
  rw [hRHS]
  linarith [hB1, hB2, hK1, hK2, hK3, h2pos 120]

/-- Master Hiding Theorem: once `MoonCommitRef` + `MoonOpenRef` establish `HonestTranscriptRefines`,
the submitted RISC-V scheme satisfies the full two-stage adaptive `Hiding HIDING_ERROR` property. -/
theorem hiding_of_refines (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (href : HonestTranscriptRefines h768) :
    submission.scheme.Hiding HIDING_ERROR := by
  constructor
  · intro _ budget; unfold HIDING_ERROR; exact le_min (by norm_num) (by positivity)
  · intro openingSize budget _ State Output adversary bounded
    apply le_min (measureTVDist_le_one _ _)
    let staged (perm : Perm) (sel : Bool) : ProbComp Output := do
      let (ch, cache0) ← compressionRun perm adversary.choose ∅
      realObs0 h768 perm cache0 (if sel then ch.message₁ else ch.message₀)
        ch.positions (adversary.observe ch.aux)
    have hstaged_eq : ∀ sel : Bool,
        𝒟[Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary sel)] =
        𝒟[($ᵗ Perm) >>= fun perm => staged perm sel] := by
      intro sel
      have hexp : Hiding.hidingExperiment submission.scheme adversary sel = (do
          let ch ← adversary.choose
          let msg := if sel then ch.message₁ else ch.message₀
          let tr ← honestTranscript msg ch.positions
          adversary.observe ch.aux tr.1 tr.2) := by
        simp only [Hiding.hidingExperiment, honestTranscript, bind_assoc, pure_bind]
      let toCommit : Digest → Commitment := fun d => d
      let refComp : OracleComp World Output := do
        let ch ← adversary.choose
        let msg := if sel then ch.message₁ else ch.message₀
        let rand ← (liftM ($ᵗ (PairIdx → PairRand)) : OracleComp World (PairIdx → PairRand))
        let nodes ← queryTreeFromLeafFn h768 (fun i => do
          let (a, b) ← queryUnsaltedLeaf h768 (msg i)
          queryCompress h768 (leafFinalInput i a b (pairSalts rand i)))
        adversary.observe ch.aux (toCommit (nodes 24 0)) (referenceProof nodes (pairSalts rand) ch.positions)
      have href_run : ∀ o : Oracle,
          𝒟[fixedOracleRun o (Hiding.hidingExperiment submission.scheme adversary sel)] =
          𝒟[fixedOracleRun o refComp] := by
        intro o
        rw [hexp, fixed_oracle_run_bind]
        unfold refComp
        rw [fixed_oracle_run_bind]
        apply _root_.evalDist_bind_congr; intro ch
        rw [fixed_oracle_run_bind, fixed_oracle_run_bind, fixed_oracle_run_coins]
        let msg := if sel then ch.message₁ else ch.message₀
        have href_ch := ((href o msg ch.positions).bind_left
          (fun tr => fixedOracleRun o (adversary.observe ch.aux tr.1 tr.2))).evalDist_eq
        rw [href_ch, bind_assoc]
        apply _root_.evalDist_bind_congr; intro rand
        simp only [pure_bind]
        obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 o
          (fun i => do let (a, b) ← queryUnsaltedLeaf h768 (msg i); queryCompress h768 (leafFinalInput i a b (pairSalts rand i)))
          (fun i => leafDigest (fun x => o.compression (x.cast h768.symm)) i (pairSalts rand i) (msg i))
          (fun i => by rw [fixed_oracle_run_bind, queryUnsaltedLeaf_fixed, pure_bind, queryCompress_fixed]; rfl)
        rw [fixed_oracle_run_bind, hrun, pure_bind]
        have hrt : toCommit (nodes 24 0) = (referenceTranscript h768 o.compression msg (pairSalts rand) ch.positions).1 :=
          hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega)
        have hpf : referenceProof nodes (pairSalts rand) ch.positions =
            (referenceTranscript h768 o.compression msg (pairSalts rand) ch.positions).2 :=
          referenceProof_congr_nodes _ _ hval (pairSalts rand) ch.positions
        rw [hrt, hpf]
      unfold Hiding.runHiding
      have hfst : ∀ o : Oracle,
          (do let (out, _) ← o.run (Hiding.hidingExperiment submission.scheme adversary sel); pure out) =
          fixedOracleRun o (Hiding.hidingExperiment submission.scheme adversary sel) := by
        intro o; unfold fixedOracleRun; rw [map_eq_bind_pure_comp]; apply bind_congr; rintro ⟨a, b⟩; rfl
      simp only [hfst]
      trans 𝒟[Oracle.sample >>= fun o => fixedOracleRun o refComp]
      · exact _root_.evalDist_bind_congr _ _ _ href_run
      · simp only [Oracle.sample, bind_assoc, pure_bind]
        rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)]
        apply _root_.evalDist_bind_congr; intro perm
        unfold refComp
        rw [staged_compression_sampling]
        unfold staged realObs0
        apply _root_.evalDist_bind_congr; rintro ⟨ch, cache0⟩
        apply _root_.evalDist_bind_congr; intro table
        rw [fixed_oracle_run_bind, fixed_oracle_run_coins]
        apply _root_.evalDist_bind_congr; intro rand
        let o : Oracle := ⟨tableExtending cache0 table, perm⟩
        let msg := if sel then ch.message₁ else ch.message₀
        obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 o
          (fun i => do let (a, b) ← queryUnsaltedLeaf h768 (msg i); queryCompress h768 (leafFinalInput i a b (pairSalts rand i)))
          (fun i => leafDigest (fun x => o.compression (x.cast h768.symm)) i (pairSalts rand i) (msg i))
          (fun i => by rw [fixed_oracle_run_bind, queryUnsaltedLeaf_fixed, pure_bind, queryCompress_fixed]; rfl)
        rw [fixed_oracle_run_bind, hrun, pure_bind]
        have hrt : toCommit (nodes 24 0) = (referenceTranscript h768 o.compression msg (pairSalts rand) ch.positions).1 :=
          hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega)
        have hpf : referenceProof nodes (pairSalts rand) ch.positions =
            (referenceTranscript h768 o.compression msg (pairSalts rand) ch.positions).2 :=
          referenceProof_congr_nodes _ _ hval (pairSalts rand) ch.positions
        rw [hrt, hpf]
    rw [measureTVDist, hstaged_eq false, hstaged_eq true, ← measureTVDist]
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Perm) _ _ (by positivity)
    intro perm
    unfold staged
    rw [bind_eq_attach_bind (compressionRun perm adversary.choose ∅)]
    rw [bind_eq_attach_bind (compressionRun perm adversary.choose ∅)]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    rintro ⟨⟨ch, cache0⟩, hreach⟩
    obtain ⟨keys0, hkeys_card, hcov0⟩ := first_stage_cache_bound perm adversary.choose budget
      (hiding_choose_query_bound adversary bounded) (ch, cache0) hreach
    have hobs_bd := staged_observe_query_bound perm adversary bounded (ch, cache0) hreach
    have hagree : ∀ i ∈ ch.positions, ch.message₀ i = ch.message₁ i :=
      fun i hi => congrFun ch.agree ⟨i, hi⟩
    have hd0 := real_ideal_from_cache0 h768 perm cache0 keys0 hcov0 ch.message₀ ch.positions
      (adversary.observe ch.aux) budget hobs_bd
    have hd1 := real_ideal_from_cache0 h768 perm cache0 keys0 hcov0 ch.message₁ ch.positions
      (adversary.observe ch.aux) budget hobs_bd
    rw [idealObs0_eq_of_agree h768 perm cache0 ch.message₀ ch.message₁ ch.positions hagree] at hd0
    rw [measureTVDist_comm] at hd1
    have htri := (measureTVDist_triangle _ _ _).trans (add_le_add hd0 hd1)
    refine htri.trans ?_
    have htwo :
        (2 * ((((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
              (((3 * (keys0.card + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
         (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 +
         ((8 * budget : Nat) : ℝ) / 2 ^ 128) +
        (2 * ((((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
              (((3 * (keys0.card + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
         (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 +
         ((8 * budget : Nat) : ℝ) / 2 ^ 128) =
        2 * (2 * ((((LENGTH / 2) ^ 5 : Nat) : ℝ) / 2 ^ 256 +
                  (((3 * (keys0.card + 3 * LENGTH) + 2 * LENGTH + 1) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
             (((2 * LENGTH + 2 * IDEAL_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 +
             ((8 * budget : Nat) : ℝ) / 2 ^ 128) := by ring
    rw [htwo]
    exact smpls40_hiding_arithmetic keys0.card budget hkeys_card

end CommitGolfCandidate
