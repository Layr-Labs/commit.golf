import CommitGolfCandidate.TruncCap
import CommitGolfCandidate.BindingMachine
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
private theorem splitPath :
    List.range 24 = List.range 17 ++ (List.range 7).map (· + 17) := by
  decide

private theorem capImpliesRoot (compress : Compression) (value : Entry) (salt : Salt)
    (index : Index) (cap : Nat → Digest) (siblings : Nat → Digest) (commitment : Digest)
    (upper : ∀ k < 7, siblings (k + 17) =
      referenceHeap compress 128 cap (((128 + index.val / 2 ^ 17) / 2 ^ k) ^^^ 1))
    (hLow : recordAncestor compress 17 value salt index siblings = cap (index.val / 2 ^ 17))
    (hTop : referenceHeap compress 128 cap 1 = commitment) :
    recordRoot compress value salt index siblings = commitment := by
  let q := index.val / 2 ^ 17
  have hq : q < 128 := by
    have hlt : index.val < 2 ^ 24 := index.isLt
    change index.val / 2 ^ 17 < 128; omega
  let upperPath := (List.range 7).map fun k => (index.val.testBit (k + 17), siblings (k + 17))
  have pathSplit : recordPath index siblings = recordPathPrefix 17 index siblings ++ upperPath := by
    simp only [recordPath, recordPathPrefix, upperPath, splitPath, List.map_append, List.map_map,
      Function.comp_def]
  have upperEq : upperPath = heapPath (referenceHeap compress 128 cap) (128 + q) 7 := by
    apply List.ext_getElem
    · simp only [upperPath, List.length_map, List.length_range, heap_path_length]
    · intro k hk1 hk2
      have hk : k < 7 := by simp only [upperPath, List.length_map, List.length_range] at hk1; exact hk1
      rw [heap_path_get _ (128 + q) 7 k hk]
      simp only [upperPath, List.getElem_map, List.getElem_range]
      refine Prod.ext ?_ (upper k hk)
      have hdir := heap_leaf_direction 7 q k hq hk
      change index.val.testBit (k + 17) = (2 ^ 7 + q).testBit k
      rw [hdir]
      dsimp only [q]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
        Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm 17 k]
  unfold recordRoot
  rw [pathSplit,climb_append,record_path_prefix_length]
  have idx : (LENGTH+index.val)/2^17=128+q := by change (16777216+index.val)/131072=128+index.val/131072;omega
  rw [idx]
  change climb compress (128+q) (recordAncestor compress 17 value salt index siblings) upperPath = commitment
  rw [hLow, upperEq]
  have leafEq : cap q = referenceHeap compress 128 cap (2 ^ 7 + q) :=
    (reference_heap_leaf compress 128 cap q hq).symm
  rw [show (128 : Nat) = 2 ^ 7 by decide, leafEq]
  exact (reconstruct_heap_root compress (referenceHeap compress 128 cap) 7 q hq (fun p pos hi =>
    reference_heap_parent compress 128 cap p pos hi)).trans hTop


theorem batchImpliesRoot (o : Oracle) (input : CheckInput) (good : BatchValid o.compression input)
    (r : Nat) (hr : r < 128) :
    recordRoot o.compression (recordValue input r) (batchSalt input r) (recordIndex input r)
      (fullSibling o.compression input r) = input.commitment := by
  have b := opening_index_bound input.positions r
  change openingIndex input.positions r < 16777216 at b
  have low := fromPair o.compression input good r hr
  apply capImpliesRoot _ _ _ _ (capTable o.compression input) _ _ _
    (by simpa only [capTable, recordIndex, show openingIndex input.positions r / 2^17 < 128 by omega, ↓reduceIte] using (show _ = parentAt o.compression input (openingIndex input.positions r / 2^17) from low)) good.root
  intro j small
  simp only [fullSibling,if_neg (by omega : ¬ j+17 < 16), if_neg (by omega : ¬j+17 = 16),
    Nat.add_sub_cancel]
  rfl

end CommitGolfCandidate.Trunc
