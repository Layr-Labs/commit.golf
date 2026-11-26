import CommitGolfCandidate.MidHidingSplit

/-! Programming a finite set of compression cells at once.

`reprogramFinset cell table fresh S` answers `fresh i` at the cell of every
leaf `i ∈ S` and `table` elsewhere. If the cells of `S` are pairwise distinct,
a uniform table programmed with independent uniform digests is a uniform
table, jointly with those digests read back from it. One application replaces
every leaf digest of a tree by a fresh one.

This is dadon's b4f31491 `reprogramFinset` and `reprogramFinset_dist`
(`MoonHiding`, section 3), for `Late.Block` cells. -/
namespace CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance programDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec

abbrev toOut (d : Late.Digest) : BitVec COMPRESSION_OUTPUT_LENGTH := d
abbrev fromOut (d : BitVec COMPRESSION_OUTPUT_LENGTH) : Late.Digest := d

noncomputable def reprogramFinset (cell : Index → Late.Block)
    (table : Compression) (fresh : Index → Late.Digest) (S : Finset Index) : Compression :=
  fun x =>
    if h : ∃ i ∈ S, cell i = x then
      toOut (fresh (Classical.choose h))
    else table x

theorem reprogramFinset_mem (cell : Index → Late.Block)
    (table : Compression) (fresh : Index → Late.Digest) (S : Finset Index)
    (hinj : Set.InjOn cell (S : Set Index)) (i : Index) (hi : i ∈ S) :
    reprogramFinset cell table fresh S (cell i) = toOut (fresh i) := by
  unfold reprogramFinset
  split_ifs with h
  · have hsp := Classical.choose_spec h
    rw [hinj hsp.1 hi hsp.2]
  · exact (h ⟨i, hi, rfl⟩).elim

theorem reprogramFinset_not_mem (cell : Index → Late.Block)
    (table : Compression) (fresh : Index → Late.Digest) (S : Finset Index)
    (x : Late.Block) (hnot : ∀ i ∈ S, cell i ≠ x) :
    reprogramFinset cell table fresh S x = table x := by
  unfold reprogramFinset
  split_ifs with h
  · obtain ⟨i, hi, heq⟩ := h
    exact (hnot i hi heq).elim
  · rfl

theorem reprogramFinset_insert (cell : Index → Late.Block)
    (table : Compression) (fresh : Index → Late.Digest) (a : Index) (S : Finset Index)
    (hinj : Set.InjOn cell ((insert a S : Finset Index) : Set Index)) :
    reprogramFinset cell table fresh (insert a S) =
      Function.update (reprogramFinset cell table fresh S) (cell a) (toOut (fresh a)) := by
  have hinjS : Set.InjOn cell (S : Set Index) :=
    hinj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
  funext x
  by_cases hx : x = cell a
  · subst hx
    rw [Function.update_self, reprogramFinset_mem cell _ _ _ hinj a (Finset.mem_insert_self a S)]
  · rw [Function.update_of_ne hx]
    by_cases hS : ∃ i ∈ S, cell i = x
    · obtain ⟨i, hi, rfl⟩ := hS
      rw [reprogramFinset_mem cell _ _ _ hinj i (Finset.mem_insert_of_mem hi),
        reprogramFinset_mem cell _ _ _ hinjS i hi]
    · rw [reprogramFinset_not_mem cell _ _ (insert a S), reprogramFinset_not_mem cell _ _ S]
      · intro i hi heq; exact hS ⟨i, hi, heq⟩
      · intro i hi heq
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · exact hx heq.symm
        · exact hS ⟨i, hiS, heq⟩

/-- **Simultaneous programming.** A uniform table with fresh digests written
into pairwise distinct cells has the distribution of a uniform table whose
digests at those cells are read back. -/
theorem reprogramFinset_dist (cell : Index → Late.Block) (S : Finset Index)
    (hinj : Set.InjOn cell (S : Set Index)) {α : Type}
    (F : Compression → (Index → Late.Digest) → ProbComp α) :
    𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
         let table ← $ᵗ Compression
         F (reprogramFinset cell table fresh S) fresh] =
    𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
         let table ← $ᵗ Compression
         F table (fun i => if i ∈ S then fromOut (table (cell i)) else fresh i)] := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
    apply _root_.evalDist_bind_congr; intro fresh
    apply _root_.evalDist_bind_congr; intro table
    have h1 : reprogramFinset cell table fresh ∅ = table := by
      funext x; exact reprogramFinset_not_mem cell _ _ ∅ x (by simp)
    have h2 : (fun i => if i ∈ (∅ : Finset Index) then fromOut (table (cell i)) else fresh i) =
        fresh := by
      funext i; exact ite_eq_right_of_eq_false _ _ (eq_false (Finset.notMem_empty i))
    rw [h1]
    exact congrArg (fun lr => 𝒟[F table lr]) h2.symm
  | @insert a S ha ih =>
    have hinjS : Set.InjOn cell (S : Set Index) :=
      hinj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
    let F' : Compression → (Index → Late.Digest) → ProbComp α := fun tbl lr =>
      do let ans ← $ᵗ Late.Digest
         F (Function.update tbl (cell a) (toOut ans)) (Function.update lr a ans)
    have hlhs :
        𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
             let table ← $ᵗ Compression
             F (reprogramFinset cell table fresh (insert a S)) fresh] =
        𝒟[do let fresh ← $ᵗ (Index → Late.Digest)
             let table ← $ᵗ Compression
             F' (reprogramFinset cell table fresh S) fresh] := by
      rw [← uniform_coordinate_bind a (fun fresh =>
        ($ᵗ Compression) >>= fun table => F (reprogramFinset cell table fresh (insert a S)) fresh)]
      apply _root_.evalDist_bind_congr; intro fresh
      rw [distribution_bind_comm ($ᵗ Late.Digest) ($ᵗ Compression)]
      apply _root_.evalDist_bind_congr; intro table
      apply _root_.evalDist_bind_congr; intro ans
      have hrep : reprogramFinset cell table (Function.update fresh a ans) (insert a S) =
          Function.update (reprogramFinset cell table fresh S) (cell a) (toOut ans) := by
        rw [reprogramFinset_insert cell _ _ a S hinj, Function.update_self]
        apply congrArg (fun f : Compression => Function.update f (cell a) (toOut ans))
        funext x
        by_cases hS : ∃ i ∈ S, cell i = x
        · obtain ⟨i, hi, rfl⟩ := hS
          rw [reprogramFinset_mem cell _ _ S hinjS i hi,
            reprogramFinset_mem cell _ _ S hinjS i hi,
            Function.update_of_ne (fun h => ha (by subst h; exact hi))]
        · rw [reprogramFinset_not_mem cell _ _ S x (fun i hi heq => hS ⟨i, hi, heq⟩),
            reprogramFinset_not_mem cell _ _ S x (fun i hi heq => hS ⟨i, hi, heq⟩)]
      simp only [hrep]
    rw [hlhs, ih hinjS F']
    apply _root_.evalDist_bind_congr; intro fresh
    rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ Late.Digest)]
    have hupd := compression_table_update_bind (cell a)
      (fun table => F table (fun i => if i ∈ insert a S then fromOut (table (cell i)) else fresh i))
    rw [← hupd]
    apply _root_.evalDist_bind_congr; intro ans
    apply _root_.evalDist_bind_congr; intro table
    have hlr : Function.update (fun i => if i ∈ S then fromOut (table (cell i)) else fresh i) a ans =
        (fun i => if i ∈ insert a S then
          fromOut ((Function.update table (cell a) (toOut ans)) (cell i))
        else fresh i) := by
      funext i
      by_cases hia : i = a
      · subst hia
        rw [Function.update_self,
          ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_insert_self i S)), Function.update_self]
      · rw [Function.update_of_ne hia]
        by_cases hiS : i ∈ S
        · have hne : cell i ≠ cell a :=
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
    exact congrArg (fun lr => 𝒟[F (Function.update table (cell a) (toOut ans)) lr]) hlr

end CommitGolfCandidate.LateHiding
