import CommitGolfCandidate.ChainedCheckerCapHash

/-! Result-copy and restoration at the cap's actual parent heap address. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local irreducible] chainedCheckerImage

theorem cap_destination_word (node : Fin 256) (word : Fin 4) :
    capDestination node+BitVec.ofNat 64 (8*word.val)=wordAddress (2048+4*node.val+word.val) := by
  unfold capDestination wordAddress
  rw [←BitVec.ofNat_add]
  congr 1
  omega
theorem cap_destination_access (node : Fin 256) (word : Fin 4) :
    accessValid (capDestination node+BitVec.ofNat 64 (8*word.val)) 8=true := by
  rw [cap_destination_word]
  exact RecordLeaf.aligned_access _ (by omega)

theorem saved_word_before_heap (slot : Fin 31) (index : Nat) (lower : 31 ≤ index) (upper : index<2^33) :
    checkerSaveWord slot≠wordAddress index := by
  intro same
  have numeric := congrArg BitVec.toNat same
  change (BitVec.ofNat 64 (8*slot.val)).toNat=(BitVec.ofNat 64 (8*index)).toNat at numeric
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*slot.val<2^64),
    Nat.mod_eq_of_lt (by omega : 8*index<2^64)] at numeric
  omega
theorem cap_destination_saved_apart (node : Fin 256) (slot : Fin 31) (word : Fin 4) :
    checkerSaveWord slot≠capDestination node+BitVec.ofNat 64 (8*word.val) := by
  rw [cap_destination_word]
  exact saved_word_before_heap slot _ (by omega) (by omega)
theorem cap_source_saved_apart (node : Fin 256) (slot : Fin 31) (word : Fin 8) :
    checkerSaveWord slot≠capSource node+BitVec.ofNat 64 (8*word.val) := by
  rw [cap_source_word]
  exact saved_word_before_heap slot _ (by omega) (by omega)

theorem result_outside_to (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9)
    (address : Word) (destination : s.getMem (checkerSaveWord site.resultSlot)=address) (query : Word)
    (away : ∀ word : Fin 4, query≠address+BitVec.ofNat 64 (8*word.val)) :
    (checkerResultPrefix site s n).getMem query=s.getMem query := by
  induction n with
  | zero => rw [checker_result_zero]
  | succ n ih =>
    rw [checker_result_succ,←ih (by omega)]
    have source (positive : 0<n) : (checkerResultPrefix site s n).getReg .x31=address :=
      (checker_result_destination site s n positive (by omega)).trans destination
    have bound : n<9 := by omega
    cases site <;> interval_cases n
    all_goals first | rfl | apply word_store_frame
    all_goals rw [source (by omega)]
    all_goals first | exact away ⟨0,by omega⟩ | exact away ⟨1,by omega⟩ |
      exact away ⟨2,by omega⟩ | exact away ⟨3,by omega⟩

theorem result_saved_to (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9)
    (address : Word) (destination : s.getMem (checkerSaveWord site.resultSlot)=address)
    (away : ∀ slot : Fin 31, ∀ word : Fin 4, checkerSaveWord slot≠address+BitVec.ofNat 64 (8*word.val))
    (slot : Fin 31) : (checkerResultPrefix site s n).getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) :=
  result_outside_to site s n small address destination _ (away slot)

private theorem load_ordinary_at (s : MachineState) (dst base : Reg) (offset : BitVec 12)
    (valid : accessValid (s.getReg base+signExtend12 offset) 8=true) :
    ordinaryStep s (.base (.LD dst base offset))=some (execInstrBr s (.LD dst base offset)) := by
  change (if accessValid (s.getReg base+signExtend12 offset) 8 then _ else _)=_
  exact ite_eq_left valid
private theorem store_ordinary_at (s : MachineState) (base src : Reg) (offset : BitVec 12)
    (valid : accessValid (s.getReg base+signExtend12 offset) 8=true) :
    ordinaryStep s (.base (.SD base src offset))=some (execInstrBr s (.SD base src offset)) := by
  change (if accessValid (s.getReg base+signExtend12 offset) 8 then _ else _)=_
  exact ite_eq_left valid

private theorem result_ordinary_to (site : CheckerHashSite) (s : MachineState) (i : Fin 9)
    (address : Word) (source : 0 < i.val → s.getReg .x31=address)
    (access : ∀ word : Fin 4, accessValid (address+BitVec.ofNat 64 (8*word.val)) 8=true) :
    ordinaryStep s (.base ((checkerResultOps site).getD i.val .EBREAK))=
      some (execInstrBr s ((checkerResultOps site).getD i.val .EBREAK)) := by
  have zero : s.getReg .x0=0#64 := rfl
  by_cases initial : i.val=0
  · have same : i=0 := Fin.ext initial
    subst i
    cases site
    · exact load_ordinary_at s .x31 .x0 176 (by rw [zero]; decide +kernel)
    · exact load_ordinary_at s .x31 .x0 88 (by rw [zero]; decide +kernel)
  have destination := source (by omega)
  fin_cases i
  case «0» => exact False.elim (initial rfl)
  case «1» => exact load_ordinary_at s .x20 .x0 256 (by rw [zero]; decide +kernel)
  case «2» =>
    apply store_ordinary_at
    rw [destination,show signExtend12 0=BitVec.ofNat 64 (8*0) from by decide +kernel]
    exact access ⟨0,by decide⟩
  case «3» => exact load_ordinary_at s .x20 .x0 264 (by rw [zero]; decide +kernel)
  case «4» =>
    apply store_ordinary_at
    rw [destination,show signExtend12 8=BitVec.ofNat 64 (8*1) from by decide +kernel]
    exact access ⟨1,by decide⟩
  case «5» => exact load_ordinary_at s .x20 .x0 272 (by rw [zero]; decide +kernel)
  case «6» =>
    apply store_ordinary_at
    rw [destination,show signExtend12 16=BitVec.ofNat 64 (8*2) from by decide +kernel]
    exact access ⟨2,by decide⟩
  case «7» => exact load_ordinary_at s .x20 .x0 280 (by rw [zero]; decide +kernel)
  case «8» =>
    apply store_ordinary_at
    rw [destination,show signExtend12 24=BitVec.ofNat 64 (8*3) from by decide +kernel]
    exact access ⟨3,by decide⟩

theorem result_execution_to (site : CheckerHashSite) (s : MachineState) (pc : s.pc=site.resume)
    (address : Word) (destination : s.getMem (checkerSaveWord site.resultSlot)=address)
    (access : ∀ word : Fin 4, accessValid (address+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (9+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerResultPrefix site s 9) coins
          return result.charge 9 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_result_zero site s]
  apply execute_unit_steps (states := checkerResultPrefix site s)
  intro i inside
  refine ⟨.base ((checkerResultOps site).getD i .EBREAK),?_,?_,?_⟩
  · apply checker_result_at site i inside
    rw [checker_result_pc _ _ _ (by omega),pc]
  · rw [checker_result_succ]
    exact result_ordinary_to site _ ⟨i,inside⟩ address (fun positive =>
      (checker_result_destination site s i positive (by omega)).trans destination) access
  · cases site <;> interval_cases i <;> rfl

theorem hash_returned_register_to (site : CheckerHashSite) (s : MachineState)
    (address : Word) (destination : s.getMem (checkerSaveWord site.resultSlot)=address)
    (away : ∀ slot : Fin 31, ∀ word : Fin 4, checkerSaveWord slot≠address+BitVec.ofNat 64 (8*word.val))
    (slot : Fin 31) : (checkerHashReturned site s).getReg (checkerSnapshotReg slot)=s.getMem (checkerSaveWord slot) := by
  rw [checkerHashReturned]
  have step (t : MachineState) (reg : Reg) : (execInstrBr t (.JALR .x0 .x1 0)).getReg reg=t.getReg reg := by cases reg <;> rfl
  rw [step,checker_load_back_register,result_saved_to _ _ _ (by omega) address destination away]

theorem hash_returned_pc_to (site : CheckerHashSite) (s : MachineState)
    (address : Word) (destination : s.getMem (checkerSaveWord site.resultSlot)=address)
    (away : ∀ slot : Fin 31, ∀ word : Fin 4, checkerSaveWord slot≠address+BitVec.ofNat 64 (8*word.val))
    (link : Word) (saved : s.getMem (checkerSaveWord ⟨0,by omega⟩)=link) :
    (checkerHashReturned site s).pc=(link+signExtend12 0) &&& ~~~(1#64) := by
  rw [checkerHashReturned]
  have restored : (checkerLoadBackPrefix (checkerResultPrefix site s 9) 31).getReg .x1=link :=
    (checker_load_back_register _ ⟨0,by omega⟩).trans
      ((result_saved_to site s 9 (by omega) address destination away ⟨0,by omega⟩).trans saved)
  change ((checkerLoadBackPrefix (checkerResultPrefix site s 9) 31).getReg .x1+signExtend12 0) &&& _=_
  rw [restored]

theorem hash_return_execution_to (site : CheckerHashSite) (s : MachineState) (pc : s.pc=site.resume)
    (address : Word) (destination : s.getMem (checkerSaveWord site.resultSlot)=address)
    (access : ∀ word : Fin 4, accessValid (address+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (41+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerHashReturned site s) coins
          return result.charge 41 0) := by
  have resultPC : (checkerResultPrefix site s 9).pc=4096+BitVec.ofNat 64 (4*site.restoreIndex) := by
    rw [checker_result_pc _ _ _ (by omega),pc]
    cases site <;> rfl
  have loadPC : (checkerLoadBackPrefix (checkerResultPrefix site s 9) 31).pc=
      4096+BitVec.ofNat 64 (4*(site.restoreIndex+31)) := by
    rw [checker_load_back_pc _ _ (by omega),resultPC]
    cases site <;> rfl
  have tail : execute (Artifact.submission.image .check) (1+fuel)
      (checkerLoadBackPrefix (checkerResultPrefix site s 9) 31) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerHashReturned site s) coins
          return result.charge 1 0) := by
    rw [checking_manifest_image,checkerHashReturned]
    rw [show 1+fuel=fuel+1 by omega]
    apply execute_ordinary_step (instruction := .base (.JALR .x0 .x1 0))
    · cases site
      · exact chained_checker_ops_at 2860 (by rw [chained_checker_ops_length]; decide) _ loadPC
      · exact chained_checker_ops_at 2958 (by rw [chained_checker_ops_length]; decide) _ loadPC
    · rfl
  rw [show 41+fuel=9+(31+(1+fuel)) by omega,result_execution_to site s pc address destination access,
    checker_load_back_execution site _ resultPC,tail]
  simp [Execution.charge,←Nat.add_assoc]

theorem child_mask_saved_at (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9)
    (address : Word) (pair : s.getReg site.childReg=address) (slot : Fin 31)
    (away : ∀ word : Fin 8, checkerSaveWord slot≠address+BitVec.ofNat 64 (8*word.val)) :
    (checkerChildMaskPrefix site s n).getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  have succ (i : Nat) (inside : i<9) : checkerChildMaskPrefix site s (i+1)=
      execInstrBr (checkerChildMaskPrefix site s i) ((checkerChildMaskOps site).getD i .EBREAK) := by
    cases site <;> interval_cases i <;> rw [checkerChildMaskPrefix,checkerChildMaskPrefix] <;> rfl
  have step (t : MachineState) (i : Fin 9) (source : t.getReg .x14=address) :
      (execInstrBr t ((checkerChildMaskOps site).getD i.val .EBREAK)).getMem (checkerSaveWord slot)=t.getMem (checkerSaveWord slot) := by
    cases site <;> fin_cases i
    all_goals first | rfl | apply word_store_frame
    all_goals rw [source]
    all_goals first | exact away ⟨3,by omega⟩ | exact away ⟨7,by omega⟩
  induction n with
  | zero => rw [checkerChildMaskPrefix]; rfl
  | succ n ih =>
    by_cases empty : n=0
    · subst n
      rw [checkerChildMaskPrefix]
      cases site <;> rfl
    · rw [succ n (by omega),step _ ⟨n,by omega⟩
        ((checker_child_mask_source site s n (by omega) (by omega)).trans pair),ih (by omega)]

theorem cap_prepared_saved (height : Fin 8) (node : Fin 256) (s : MachineState)
    (source : s.getReg .x10=capSource node) (slot : Fin 31) :
    (capPrepared height s).getMem (checkerSaveWord slot)=s.getReg (checkerSnapshotReg slot) := by
  rw [capPrepared,checker_hash_abi_memory]
  change (capScheduled height (capMasked s)).mem (checkerSaveWord slot)=_
  rw [cap_scheduled_memory]
  change (capMasked s).getMem (checkerSaveWord slot)=_
  rw [capMasked,child_mask_saved_at .cap _ 9 (by omega) (capSource node)
    ((checker_snapshot_register 31 s (by omega) .x10).trans source) slot (cap_source_saved_apart node slot)]
  exact checker_snapshot_saved 31 s (by omega) slot slot.isLt

theorem cap_parent_saved (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (reached : out∈support (capParentTrace height s)) (slot : Fin 31) :
    out.getMem (checkerSaveWord slot)=s.getReg (checkerSnapshotReg slot) := by
  exact (checker_hash_saved_memory .cap 0 _ out (cap_prepared_ready height node range s pc parent source).args reached slot).trans
    (cap_prepared_saved height node s source slot)

theorem cap_parent_destination (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (destination : s.getReg .x12=capDestination node)
    (reached : out∈support (capParentTrace height s)) :
    out.getMem (checkerSaveWord CheckerHashSite.cap.resultSlot)=capDestination node := by
  have saved := cap_parent_saved height node range s out pc parent source reached ⟨11,by omega⟩
  change out.getMem (checkerSaveWord CheckerHashSite.cap.resultSlot)=s.getReg .x12 at saved
  exact saved.trans destination

theorem cap_returned_register (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (destination : s.getReg .x12=capDestination node)
    (reached : out∈support (capParentTrace height s)) (slot : Fin 31) :
    (checkerHashReturned .cap out).getReg (checkerSnapshotReg slot)=s.getReg (checkerSnapshotReg slot) := by
  exact (hash_returned_register_to .cap out (capDestination node)
    (cap_parent_destination height node range s out pc parent source destination reached)
    (cap_destination_saved_apart node) slot).trans
      (cap_parent_saved height node range s out pc parent source reached slot)

theorem cap_returned_pc (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (destination : s.getReg .x12=capDestination node)
    (link : s.getReg .x1=4096+4*2714) (reached : out∈support (capParentTrace height s)) :
    (checkerHashReturned .cap out).pc=4096+4*2714 := by
  have saved := (cap_parent_saved height node range s out pc parent source reached ⟨0,by omega⟩).trans link
  rw [hash_returned_pc_to .cap out (capDestination node)
    (cap_parent_destination height node range s out pc parent source destination reached)
    (cap_destination_saved_apart node) (4096+4*2714) saved]
  decide +kernel

def capReturnTrace (height : Fin 8) (s : MachineState) : OracleComp World MachineState := do
  let out ← capParentTrace height s
  pure (checkerHashReturned .cap out)

theorem cap_return_execution (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (destination : s.getReg .x12=capDestination node)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (132+4*capDepth height+fuel) s coins=
      (do let out ← capReturnTrace height s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (139+4*capDepth height) 1) := by
  rw [show 132+4*capDepth height+fuel=91+4*capDepth height+(41+fuel) by omega,
    cap_parent_execution height node range s pc parent source,capReturnTrace]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro out reached
  rw [hash_return_execution_to .cap out (cap_parent_pc height node range s out pc parent source reached)
    (capDestination node) (cap_parent_destination height node range s out pc parent source destination reached)
    (cap_destination_access node)]
  simp [Execution.charge,Nat.add_assoc,Nat.add_comm]
  rw [show 41+(98+4*capDepth height)=139+4*capDepth height by omega]

theorem cap_return_pc (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (destination : s.getReg .x12=capDestination node)
    (link : s.getReg .x1=4096+4*2714) (reached : out∈support (capReturnTrace height s)) :
    out.pc=4096+4*2714 := by
  simp only [capReturnTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,first,rfl⟩ := reached
  exact cap_returned_pc height node range s hashed pc parent source destination link first

theorem cap_return_register (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (destination : s.getReg .x12=capDestination node)
    (reached : out∈support (capReturnTrace height s)) (slot : Fin 31) :
    out.getReg (checkerSnapshotReg slot)=s.getReg (checkerSnapshotReg slot) := by
  simp only [capReturnTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,first,rfl⟩ := reached
  exact cap_returned_register height node range s hashed pc parent source destination first slot

end CommitGolfCandidate.Chained.Native.CheckerCap
