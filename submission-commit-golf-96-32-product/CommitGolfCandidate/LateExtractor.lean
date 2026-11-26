import CommitGolfCandidate.LatePairReplay

namespace CommitGolfCandidate.Late.Check
open CommitGolf OracleComp OracleSpec

def authInputs (H : Compression) (input : CheckInput) (r : Nat) :=
  recordInputs H ((recordIndex input.positions r).val.testBit 0) (salt input r) (recordValue input r)
    (authPath H input r)

def extract (input : CheckInput) (r : Nat) : OracleComp World (List Block) := do
  let i := recordIndex input.positions r
  let pth ← if input.positions.card = BATCH then do
    let kids ← queryChildren input (i.val/131072)
    let tab ← parents input 128
    let high ← replayCapUpper tab i
    pure (path i 16 (sibling input r) ++
      [(i.val.testBit 16,kids.sibling (i.val.testBit 16) (supplied input (i.val/131072)))] ++ List.ofFn high)
    else pure (path i 24 (sibling input r))
  let lr ← Late.replay (i.val.testBit 0) (salt input r) (recordValue input r)
  let pr ← replayPath 0 lr.1 pth
  return lr.2 ++ pr.2

def cost (input : CheckInput) := if input.positions.card = BATCH then 5436 else 28

private theorem upper_list (H : Compression) (input : CheckInput) (i : Index) :
    (List.ofFn fun k : Fin 7 => (i.val.testBit (17+k.val),
      referenceHeap H 128 (capTable H input)
        (((128+i.val/2^17)/2^k.val) ^^^ 1))) =
      heapPath (upper H input) (128+i.val/131072) 7 := by
  apply List.ext_getElem
  · simp [heap_path_length]
  · intro k hk _
    have h : k < 7 := by simpa using hk
    rw [List.getElem_ofFn, heap_path_get _ _ _ _ h]
    apply Prod.ext
    · dsimp only
      have hi := i.isLt; change i.val < 16777216 at hi
      change i.val.testBit (17+k) = (2^7 + i.val/131072).testBit k
      rw [heap_leaf_direction 7 (i.val/131072) k (by omega) h, Nat.testBit_eq_decide_div_mod_eq,
        Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul]
      change _ = decide (i.val/(2^17*2^k)%2=1)
      rw [← Nat.pow_add]
    · rfl

theorem auth_length (H : Compression) (input : CheckInput) (r : Nat) :
    (authPath H input r).length = 24 := by
  unfold authPath; split <;> simp [capPath,path,heap_path_length]

attribute [local irreducible] children parents capTable replayCapUpper Late.replay replayPath

theorem extract_run (o : Oracle) (input : CheckInput) (r : Nat) :
    o.run (extract input r) = pure (authInputs o.compression input r,cost input) := by
  let i := recordIndex input.positions r
  by_cases b : input.positions.card = BATCH
  · simp only [extract,b,if_true,bind_assoc,pure_bind,oracle_run_bind,childrenRun,parentsRun,
      replay_cap_upper_run,Late.replay_run,replay_path_run,oracle_run_pure]
    have eq := upper_list o.compression input i
    unfold capTable at eq
    change List.ofFn _ = _ at eq
    rw [eq]
    simp [authInputs,recordInputs,authPath,b,capPath,cost,path,heap_path_length]
    rfl
  · simp only [extract,if_neg b,pure_bind,oracle_run_bind,Late.replay_run,replay_path_run,oracle_run_pure]
    simp [authInputs,recordInputs,authPath,b,cost,path]

theorem extract_bound (input : CheckInput) (r : Nat) :
    IsTotalQueryBound (extract input r) (cost input) := by
  let i := recordIndex input.positions r
  have endBound (pth : List (Bool × Digest)) (len : pth.length=24) :
      IsTotalQueryBound (do let lr ← Late.replay (i.val.testBit 0) (salt input r) (recordValue input r)
                            let pr ← replayPath 0 lr.1 pth
                            pure (lr.2 ++ pr.2)) (4+24) := by
    apply isTotalQueryBound_bind (replay_bound _ _ _)
    intro lr
    simp only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff]
    exact len ▸ replay_path_query_bound 0 lr.1 pth
  by_cases b : input.positions.card = BATCH
  · simp only [extract,cost,b,if_true,bind_assoc,pure_bind]
    change IsTotalQueryBound (_ >>= _) (40 + (41*128 + (120 + (4+24))))
    apply isTotalQueryBound_bind (childrenBound _ _)
    intro kids
    apply isTotalQueryBound_bind (parentsBound _ _)
    intro tab
    apply isTotalQueryBound_bind (replay_cap_upper_query_bound _ _)
    intro high
    apply endBound
    simp [path]
  · simp only [extract,cost,if_neg b,pure_bind]
    apply endBound
    simp [path]

def leftInput (c : Scheme.Claim) : CheckInput := ⟨c.root,c.positions₀,c.values₀,c.proof₀⟩
def rightInput (c : Scheme.Claim) : CheckInput := ⟨c.root,c.positions₁,c.values₁,c.proof₁⟩

def Differ (c : Scheme.Claim) (pair : Nat × Nat) :=
  pair.1 < c.positions₀.card ∧ pair.2 < c.positions₁.card ∧
  recordIndex c.positions₀ pair.1 = recordIndex c.positions₁ pair.2 ∧
  recordValue (leftInput c) pair.1 ≠ recordValue (rightInput c) pair.2

theorem differing {c : Scheme.Claim} (conflict : c.Conflicting) : ∃ p, Differ c p := by
  obtain ⟨i,hl,hr,diff⟩ := conflict
  obtain ⟨a,ha,ia,va⟩ := selected (leftInput c) i hl
  obtain ⟨b,hb,ib,vb⟩ := selected (rightInput c) i hr
  exact ⟨(a,b),ha,hb,ia.trans ib.symm,fun equal => diff (va.symm.trans (equal.trans vb))⟩

noncomputable def disputed (c : Scheme.Claim) : Nat × Nat := open Classical in
  if h : c.Conflicting then (differing h).choose else (0,0)

/-- Two distinct queried inputs whose replies agree on their low 240 bits (a full collision is one). -/
def collision (H : Compression) (xs : List Block) : Prop :=
  ∃ x ∈ xs, ∃ y ∈ xs, x ≠ y ∧ low240 (H x) = low240 (H y)

theorem breaks_collision (law : AcceptsValid) (o : Oracle) (c : Scheme.Claim) (win : submission.scheme.Breaks o c) :
    collision o.compression (authInputs o.compression (leftInput c) (disputed c).1 ++
      authInputs o.compression (rightInput c) (disputed c).2) := by
  have witness : Differ c (disputed c) := by simpa [disputed,win.1] using (differing win.1).choose_spec
  obtain ⟨ha,hb,index,diff⟩ := witness
  let p := disputed c
  let l := leftInput c
  let r := rightInput c
  have eqi : recordIndex l.positions p.1 = recordIndex r.positions p.2 := index
  have dir := (auth_dirs o.compression l p.1).trans ((congrArg
    (fun i : Index => (List.range 24).map fun k => i.val.testBit k) eqi).trans (auth_dirs o.compression r p.2).symm)
  have left := accepted_root law o l win.2.1 p.1 ha
  have right := accepted_root law o r win.2.2 p.2 hb
  change climbAt _ 0 (leaf _ ((recordIndex l.positions p.1).val.testBit 0) _ _) _ = c.root at left
  rw [eqi] at left
  have collide := record_collision _ _ _ _ _ _ _ _ dir diff (left.trans right.symm)
  obtain ⟨x,hx,y,hy,coll⟩ := collide
  refine ⟨x,List.mem_append_left _ ?_, y,List.mem_append_right _ hy,coll⟩
  unfold authInputs
  change _ ∈ recordInputs _ ((recordIndex l.positions p.1).val.testBit 0) _ _ _
  rw [eqi]
  exact hx

end CommitGolfCandidate.Late.Check
