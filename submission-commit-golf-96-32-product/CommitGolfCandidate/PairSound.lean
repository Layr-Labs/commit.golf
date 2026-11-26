import CommitGolfCandidate.PairBatchModel
import CommitGolfCandidate.PairControl
import CommitGolfCandidate.BindingMachine
namespace CommitGolfCandidate.PairCap
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
  rw [pathSplit, climb, List.foldl_append]
  change climb compress (recordAncestor compress 17 value salt index siblings) upperPath = commitment
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

def authSalt (input : CheckInput) (r : Nat) :=
  if input.positions.card=BATCH then batchSalt input r else recordSalt input r
def authSibling (H : Compression) (input : CheckInput) (r : Nat) :=
  if input.positions.card=BATCH then fullSibling H input r else recordSibling H input r

theorem normalCheck (input : CheckInput) (normal : input.positions.card≠BATCH) :
    submission.scheme.check input.commitment input.positions input.values input.proof =
    CommitGolfCandidate.submission.scheme.check input.commitment input.positions input.values input.proof := by
  change (fun e => e.exit == Exit.success) <$> simulateQ checkHandler (submission.run .check input) = _
  rw [check_normal_run input normal]
  rfl

def batchSound : Prop :=
  ∀ (o : Oracle) (input : CheckInput), input.positions.card=BATCH →
    (o.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true →
    BatchValid o.compression input

theorem authRoot (sound : batchSound) (o : Oracle) (input : CheckInput)
    (accepted : (o.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true)
    (r : Nat) (hr : r < input.positions.card) :
    recordRoot o.compression (recordValue input r) (authSalt input r) (recordIndex input r)
      (authSibling o.compression input r) = input.commitment := by
  by_cases b : input.positions.card=BATCH
  · rw [authSalt,authSibling,if_pos b,if_pos b]
    exact batchImpliesRoot o input (sound o input b accepted) r (by simpa only [b,BATCH] using hr)
  · rw [authSalt,authSibling,if_neg b,if_neg b]
    rw [normalCheck input b] at accepted
    exact check_input_sound o input accepted r hr

def authInputs (H : Compression) (input : CheckInput) (r : Nat) :=
  openingInputs H (recordIndex input r) (authSalt input r) (recordValue input r)
    (recordPath (recordIndex input r) (authSibling H input r))

theorem authInputsLength (H : Compression) (input : CheckInput) (r : Nat) :
    (authInputs H input r).length=28 := by rw [authInputs,openingInputs_length,record_path_length]

theorem conflictingCollision (sound : batchSound) (o : Oracle) (c : Scheme.Claim)
    (broken : submission.scheme.Breaks o c) (l r : Nat) (records : ConflictingRecords c l r) :
    ∃ x ∈ authInputs o.compression (claimLeft c) l,
      ∃ y ∈ authInputs o.compression (claimRight c) r, x ≠ y ∧ o.compression x = o.compression y := by
  have left := authRoot sound o (claimLeft c) broken.2.1 l records.1
  have right := authRoot sound o (claimRight c) broken.2.2 r records.2.1
  unfold authInputs
  rw [← records.2.2.1]
  unfold recordRoot at left right
  rw [← records.2.2.1] at right
  apply collision_of_openings_eq
  · exact record_path_directions _ _ _
  · exact records.2.2.2
  · exact left.trans right.symm
end CommitGolfCandidate.PairCap
