import CommitGolfCandidate.CapBatchBudget

/-! Lengths of supported paid traces, independently of fixed-oracle evaluation.
These bounds are needed when a detector later queries the recorded inputs again;
query-count bounds alone would not constrain an arbitrary returned list. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

theorem cap_chain_trace_length (state : Digest) (blocks : List Digest)
    (root : Digest) (inputs : List (BitVec 512))
    (reached : (root, inputs) ∈ support (replayChain state blocks)) :
    inputs.length = blocks.length := by
  induction blocks generalizing state root inputs with
  | nil =>
      have same := eq_of_mem_support_pure (state, []) reached
      have trace := congrArg Prod.snd same
      simp only [Prod.snd] at trace
      rw [trace]
      rfl
  | cons block rest ih =>
      rw [replayChain] at reached
      obtain ⟨next, _, afterQuery⟩ := mem_support_bind_peel _ _ reached
      obtain ⟨⟨tailRoot, tailInputs⟩, tailReached, afterTail⟩ :=
        mem_support_bind_peel _ _ afterQuery
      have same := eq_of_mem_support_pure (tailRoot, (block ++ state) :: tailInputs) afterTail
      have trace := congrArg Prod.snd same
      simp only [Prod.snd] at trace
      rw [trace]
      simp [ih next tailRoot tailInputs tailReached]

theorem cap_path_trace_length (node : Digest) (path : List (Bool × Digest))
    (root : Digest) (inputs : List (BitVec 512))
    (reached : (root, inputs) ∈ support (replayPath node path)) :
    inputs.length = path.length := by
  induction path generalizing node root inputs with
  | nil =>
      have same := eq_of_mem_support_pure (node, []) reached
      have trace := congrArg Prod.snd same
      simp only [Prod.snd] at trace
      rw [trace]
      rfl
  | cons head rest ih =>
      rcases head with ⟨right, sibling⟩
      rw [replayPath] at reached
      obtain ⟨next, _, afterQuery⟩ := mem_support_bind_peel _ _ reached
      obtain ⟨⟨tailRoot, tailInputs⟩, tailReached, afterTail⟩ :=
        mem_support_bind_peel _ _ afterQuery
      have same := eq_of_mem_support_pure
        (tailRoot, (if right then node ++ sibling else sibling ++ node) :: tailInputs) afterTail
      have trace := congrArg Prod.snd same
      simp only [Prod.snd] at trace
      rw [trace]
      simp [ih next tailRoot tailInputs tailReached]

theorem cap_lower_trace_length (record : CapLowerRecord) (root : Digest)
    (inputs : List (BitVec 512))
    (reached : (root, inputs) ∈ support (capReplayLower record)) : inputs.length = 16 := by
  rw [capReplayLower] at reached
  obtain ⟨leaf, _, lowerReached⟩ := mem_support_bind_peel _ _ reached
  rw [cap_path_trace_length _ _ _ _ lowerReached, cap_lower_path_length]

theorem cap_lower_batch_trace_length (records : List CapLowerRecord)
    (roots finalRoots : CapRootMap) (inputs : List (BitVec 512))
    (reached : some (finalRoots, inputs) ∈ support (capReplayLowerBatch records roots)) :
    inputs.length = 16 * records.length := by
  induction records generalizing roots finalRoots inputs with
  | nil =>
      have same := eq_of_mem_support_pure (some (roots, [])) reached
      have trace : inputs = [] := by
        simpa using congrArg (fun result => result.map Prod.snd) same
      rw [trace]
      rfl
  | cons record rest ih =>
      rw [capReplayLowerBatch] at reached
      obtain ⟨⟨root, recordInputs⟩, recordReached, afterRecord⟩ := mem_support_bind_peel _ _ reached
      cases inserted : capInsert roots (capGroup record.index).val root with
      | none =>
          simp only [inserted] at afterRecord
          have impossible := eq_of_mem_support_pure
            (none : Option (CapRootMap × List (BitVec 512))) afterRecord
          contradiction
      | some next =>
          simp only [inserted] at afterRecord
          obtain ⟨result, tailReached, mapped⟩ := mem_support_bind_peel _ _ afterRecord
          have same := eq_of_mem_support_pure
            (result.map fun (tailRoots, tailInputs) => (tailRoots, recordInputs ++ tailInputs)) mapped
          cases result with
          | none => simp at same
          | some pair =>
              rcases pair with ⟨tailRoots, tailInputs⟩
              have trace : inputs = recordInputs ++ tailInputs := by
                simpa using congrArg (fun result => result.map Prod.snd) same
              rw [trace, List.length_append, cap_lower_trace_length _ _ _ recordReached,
                ih next tailRoots tailInputs tailReached]
              simp [Nat.mul_add, Nat.add_comm]

/-- Successful canonical cap reconstruction visits every occupied internal node.
Each contributes exactly one recorded input for every possible reply sequence. -/
theorem cap_cap_trace_length {height : Nat} (view : CapView height)
    (proof rest : List Digest) (root : Digest) (inputs : List (BitVec 512))
    (reached : some (root, rest, inputs) ∈ support (capReplayQ view proof)) :
    inputs.length = capCalls view := by
  induction view generalizing proof rest root inputs with
  | leaf known =>
      cases known with
      | none =>
          cases proof with
          | nil => simp [capReplayQ, capOccupied] at reached
          | cons value tail =>
              have same := eq_of_mem_support_pure (some (value, tail, [])) reached
              have trace : inputs = [] := by
                simpa using congrArg (fun result => result.map (fun result => result.2.2)) same
              rw [trace]
              rfl
      | some value =>
          have same := eq_of_mem_support_pure (some (value, proof, [])) reached
          have trace : inputs = [] := by
            simpa using congrArg (fun result => result.map (fun result => result.2.2)) same
          rw [trace]
          rfl
  | node left right ihLeft ihRight =>
      by_cases occupied : capOccupied (.node left right) = true
      · simp only [capReplayQ, occupied, ↓reduceIte] at reached
        obtain ⟨leftResult, leftReached, afterLeft⟩ := mem_support_bind_peel _ _ reached
        cases leftResult with
        | none =>
            have impossible := eq_of_mem_support_pure (none : Option CapReplayResult) afterLeft
            contradiction
        | some result =>
            rcases result with ⟨lroot, middle, leftInputs⟩
            obtain ⟨rightResult, rightReached, afterRight⟩ := mem_support_bind_peel _ _ afterLeft
            cases rightResult with
            | none =>
                have impossible := eq_of_mem_support_pure (none : Option CapReplayResult) afterRight
                contradiction
            | some result =>
                rcases result with ⟨rroot, endProof, rightInputs⟩
                obtain ⟨reply, _, afterQuery⟩ := mem_support_bind_peel _ _ afterRight
                have same := eq_of_mem_support_pure
                  (some (reply, endProof, leftInputs ++ rightInputs ++ [rroot ++ lroot])) afterQuery
                have trace : inputs = leftInputs ++ rightInputs ++ [rroot ++ lroot] := by
                  simpa using congrArg (fun result => result.map (fun result => result.2.2)) same
                rw [trace]
                simp [List.length_append, ihLeft _ _ _ _ leftReached,
                  ihRight _ _ _ _ rightReached, capCalls, occupied, Nat.add_assoc]
      · simp only [capReplayQ, occupied, ↓reduceIte] at reached
        cases proof with
        | nil => simp at reached
        | cons value tail =>
            have same := eq_of_mem_support_pure (some (value, tail, [])) reached
            have trace : inputs = [] := by
              simpa using congrArg (fun result => result.map (fun result => result.2.2)) same
            rw [trace]
            simp [capCalls, occupied]

/-- All supported accepted batch traces fit the conservative replay ceiling.
Strict root/suffix rejection cannot enlarge the returned trace. -/
theorem cap_batch_trace_bound (records : List CapLowerRecord) (proof : List Digest)
    (root : Digest) (inputs : List (BitVec 512))
    (reached : some inputs ∈ support (capReplayBatch records proof root)) :
    inputs.length ≤ 24 * records.length + 255 := by
  rw [capReplayBatch] at reached
  obtain ⟨lowerResult, lowerReached, afterLower⟩ := mem_support_bind_peel _ _ reached
  cases lowerResult with
  | none =>
      have impossible := eq_of_mem_support_pure (none : Option (List (BitVec 512))) afterLower
      contradiction
  | some result =>
      rcases result with ⟨roots, lowerInputs⟩
      obtain ⟨capResult, capReached, afterCap⟩ := mem_support_bind_peel _ _ afterLower
      cases capResult with
      | none =>
          have impossible := eq_of_mem_support_pure (none : Option (List (BitVec 512))) afterCap
          contradiction
      | some result =>
          rcases result with ⟨reported, rest, capInputs⟩
          by_cases accepted : reported = root ∧ rest = []
          · simp only [Option.bind_some, if_pos accepted] at afterCap
            have same := eq_of_mem_support_pure (some (lowerInputs ++ capInputs)) afterCap
            have trace := Option.some.inj same
            rw [trace, List.length_append, cap_lower_batch_trace_length _ _ _ _ lowerReached,
              cap_cap_trace_length _ _ _ _ _ capReached]
            have capBound := cap_calls_full_bound (capKnownView roots 8 0)
            norm_num at capBound
            omega
          · simp only [Option.bind_some, if_neg accepted] at afterCap
            have impossible := eq_of_mem_support_pure (none : Option (List (BitVec 512))) afterCap
            contradiction
end CommitGolfCandidate
