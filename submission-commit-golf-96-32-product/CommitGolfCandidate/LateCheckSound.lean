import CommitGolfCandidate.LateCheckModel

namespace CommitGolfCandidate.Late.Check
open CommitGolf

def authPath (h : Compression) (input : CheckInput) (r : Nat) : List (Bool × Digest) :=
  if input.positions.card = BATCH then capPath h input r else path (recordIndex input.positions r) 24 (sibling input r)

theorem accepted_root (law : AcceptsValid) (o : Oracle) (input : CheckInput)
    (accepted : (evaluation o input).1 = true) (r : Nat) (hr : r < input.positions.card) :
    let i := recordIndex input.positions r
    climbAt o.compression 0 (leaf o.compression (i.val.testBit 0) (salt input r) (recordValue input r))
      (authPath o.compression input r) = input.commitment := by
  have valid := law o input accepted
  by_cases b : input.positions.card = BATCH
  · rw [authPath,if_pos b]
    exact batch_path_root o input (by simpa only [Valid, if_pos b] using valid) r (by simpa only [b,BATCH] using hr)
  · rw [authPath,if_neg b]
    simp only [Valid,if_neg b] at valid
    exact valid.2 r hr

private theorem upper_dirs (heap : Nat → Digest) (i : Index) :
    (heapPath heap (128+i.val/131072) 7).map Prod.fst =
      (List.range 7).map fun k => i.val.testBit (17+k) := by
  apply List.ext_getElem
  · simp [heap_path_length]
  · intro k hk _
    have small : k < 7 := by simpa only [List.length_map,heap_path_length] using hk
    have hi := i.isLt
    change i.val < 16777216 at hi
    rw [List.getElem_map, heap_path_get _ _ _ _ small, List.getElem_map, List.getElem_range]
    change (2^7+i.val/131072).testBit k = _
    rw [heap_leaf_direction 7 _ _ (by omega) small, Nat.testBit_eq_decide_div_mod_eq,
      Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul]
    change decide (i.val / (2^17*2^k)%2=1) = _
    rw [← Nat.pow_add]

theorem auth_dirs (h : Compression) (input : CheckInput) (r : Nat) :
    (authPath h input r).map Prod.fst =
      (List.range 24).map fun l => (recordIndex input.positions r).val.testBit l := by
  unfold authPath
  split
  · let i := recordIndex input.positions r
    simp only [capPath, path, List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
      upper_dirs]
    rw [show List.range 24 = List.range 17 ++ (List.range 7).map (17+·) by decide,
      List.range_succ (n := 16)]
    simp only [List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def]
  · simp [path,List.map_map, Function.comp_def]

theorem selected (input : CheckInput) (i : Index) (mem : i ∈ input.positions) :
    ∃ r < input.positions.card, recordIndex input.positions r = i ∧ recordValue input r = input.values ⟨i,mem⟩ := by
  let ps := input.positions
  let xs := ps.attach.sort (fun a b => a.val ≤ b.val)
  have mapped : xs.map Subtype.val = ps.sort (· ≤ ·) := by
    have law := Finset.map_sort (r := fun i j : {i // i ∈ ps} => i.val ≤ j.val)
      (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ ps))
      (s := ps.attach) (by intro a _ b _; rfl)
    simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using law
  have present : (⟨i,mem⟩ : {x // x ∈ ps}) ∈ xs := by simp [xs]
  obtain ⟨r,hr,atIndex⟩ := List.getElem_of_mem present
  have hit : xs[r]? = some ⟨i,mem⟩ := (List.getElem?_eq_getElem hr).trans (congrArg some atIndex)
  refine ⟨r, by simpa only [xs, Finset.length_sort, Finset.card_attach] using hr, ?_, ?_⟩
  · change ((ps.sort (· ≤ ·))[r]?.getD _) = _
    rw [← mapped, List.getElem?_map, hit]; rfl
  · change ((xs[r]?).map input.values).getD _ = _
    rw [hit]; rfl

end CommitGolfCandidate.Late.Check
