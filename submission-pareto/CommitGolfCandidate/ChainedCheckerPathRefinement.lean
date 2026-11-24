import CommitGolfCandidate.ChainedCheckerRefinement

/-! Recorded lower-path hashes use the nodes actually read by the delivered checker. -/
namespace CommitGolfCandidate.Chained.Native.Refinement
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open RecordLeaf
set_option maxRecDepth 8192

theorem recorded_bind_evaluation {α β : Type} (oracle : Oracle)
    (first : OracleComp World α) (next : α → OracleComp World β) :
    checkEvaluation oracle (recordRows (first >>= next))=
      let earlier := checkEvaluation oracle (recordRows first)
      let later := checkEvaluation oracle (recordRows (next earlier.1.1))
      ((later.1.1,earlier.1.2++later.1.2),earlier.2+later.2) := by
  rw [record_rows_bind,check_evaluation_bind]
  generalize checkEvaluation oracle (recordRows first)=earlier
  rcases earlier with ⟨⟨value,rows⟩,calls⟩
  dsimp only
  rw [check_evaluation_bind]
  generalize checkEvaluation oracle (recordRows (next value))=later
  rcases later with ⟨⟨out,more⟩,extra⟩
  simp [check_evaluation_pure]

theorem checker_lower_hash_recorded_chain (oracle : Oracle) (height : Fin 16) (state : MachineState)
    (pc : state.pc=4096+4*2757) (pair : state.getReg .x24=12544)
    (counter : state.getReg .x29=BitVec.ofNat 64 (16-height.val)) :
    let h : Height := ⟨height.val,by omega⟩
    let seed := (readBuffer state 12576 32).setWidth 238 ++ (readBuffer state 12544 32).setWidth 238
    let observed := checkEvaluation oracle
      (recordRows (checkerHashTrace .lower (checkerLowerRemaining height) (checkerLowerHashState height state)))
    RecordedChain canonicalEncoding calls observed.1.2 h seed (canonicalChainValue oracle h seed) ∧
      readBuffer observed.1.1 256 32=finalValue h (canonicalChainValue oracle h seed (calls h-1)) := by
  have ready := checker_lower_hash_ready height state pc pair counter
  have small : checkerLowerRemaining height≤7 := by unfold checkerLowerRemaining; split_ifs <;> omega
  apply checker_hash_recorded_chain oracle .lower _ small _ ready.args ⟨height.val,by omega⟩
    _ _ ready.height ready.mask (checker_lower_remaining_calls height)
  intro word
  rw [ready.source,checker_lower_hash_memory]
  exact checker_first_hash_children state pair word

theorem checker_first_sibling_recorded_chain (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    let height : Height := ⟨0,by decide⟩
    let seed := checkerFirstRight state base.value ++ checkerFirstLeft state base.value
    let observed := checkEvaluation oracle (recordRows (checkerFirstSiblingHashTrace state))
    RecordedChain canonicalEncoding calls observed.1.2 height seed (canonicalChainValue oracle height seed) ∧
      readBuffer observed.1.1 256 32=finalValue height
        (canonicalChainValue oracle height seed (calls height-1)) := by
  rw [checker_first_sibling_hash_eq]
  have prepared := checker_first_sibling_hash_prepared input state ready
  exact checker_hash_recorded_chain oracle .lower 3 (by decide) _ prepared.args ⟨0,by decide⟩
    _ _ prepared.height prepared.mask (by decide) (checker_first_sibling_hash_children input state ready)

private theorem path_reg_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg=state.getReg reg := by cases reg <;> rfl
private theorem path_mem_reg (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem=state.mem := by cases reg <;> rfl
private theorem path_mem_pc (state : MachineState) (pc : Word) : (state.setPC pc).mem=state.mem := rfl
private theorem path_mem_store (state : MachineState) (address value : Word) :
    (state.setMem address value).mem=(fun query => if query=address then value else state.mem query) := by
  funext query
  simp [MachineState.setMem]

theorem checker_result_lower_memory (state : MachineState)
    (destination : state.getMem (checkerSaveWord CheckerHashSite.lower.resultSlot)=12288) :
    (checkerResultPrefix .lower state 9).mem=(Opening.fourWordStore state 256 12288).mem := by
  change state.mem 176=12288 at destination
  have saved : state.mem 176#64=12288#64 := destination
  have zero : state.getReg .x0=0 := rfl
  repeat rw [checker_result_succ]
  rw [checker_result_zero]
  simp [checkerResultOps,CheckerHashSite.resultSlot,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,
    path_reg_mem,signExtend12,MachineState.getMem,path_mem_pc,path_mem_reg,path_mem_store,
    zero,saved,Opening.fourWordStore]

theorem checker_result_lower_word (state : MachineState)
    (destination : state.getMem (checkerSaveWord CheckerHashSite.lower.resultSlot)=12288) (word : Fin 4) :
    (checkerResultPrefix .lower state 9).getMem ((12288 : Word)+BitVec.ofNat 64 (8*word.val))=
      state.getMem ((256 : Word)+BitVec.ofNat 64 (8*word.val)) := by
  have copied := TwoPermutationPrototype.Checker.four_word_store_word state 256 12288 1536
    (by rfl) (by decide) word
  simpa only [MachineState.getMem,checker_result_lower_memory state destination] using copied

theorem checker_returned_lower_word (state : MachineState)
    (destination : state.getMem (checkerSaveWord CheckerHashSite.lower.resultSlot)=12288) (word : Fin 4) :
    (checkerHashReturned .lower state).getMem ((12288 : Word)+BitVec.ofNat 64 (8*word.val))=
      state.getMem ((256 : Word)+BitVec.ofNat 64 (8*word.val)) := by
  rw [checkerHashReturned]
  change (checkerLoadBackPrefix (checkerResultPrefix .lower state 9) 31).getMem _=_
  rw [checker_load_back_memory _ _ (by decide)]
  exact checker_result_lower_word state destination word

theorem checker_returned_lower_buffer (state : MachineState)
    (destination : state.getMem (checkerSaveWord CheckerHashSite.lower.resultSlot)=12288) :
    readBuffer (checkerHashReturned .lower state) 12288 32=readBuffer state 256 32 := by
  apply output_ext_words
  intro word
  rw [read_digest_word _ _ _ (by decide) word.isLt,read_digest_word _ _ _ (by decide) word.isLt]
  simpa only [BitVec.ofNat_add,show BitVec.ofNat 64 12288=(12288 : Word) from rfl,
    show BitVec.ofNat 64 256=(256 : Word) from rfl] using checker_returned_lower_word state destination word

private theorem path_jal_memory (state : MachineState) (offset : BitVec 21) :
    (execInstrBr state (.JAL .x0 offset)).mem=state.mem := rfl
private theorem path_add_memory (state : MachineState) (left right : Reg) :
    (execInstrBr state (.ADD .x21 left right)).mem=state.mem := rfl
private theorem path_shift_memory (state : MachineState) (shift : BitVec 6) :
    (execInstrBr state (.SRLI .x6 .x6 shift)).mem=state.mem := rfl
private theorem path_addi_memory (state : MachineState) (offset : BitVec 12) :
    (execInstrBr state (.ADDI .x29 .x29 offset)).mem=state.mem := rfl
private theorem path_bne_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x29 .x0 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split_ifs <;> rfl

private theorem lower_finish_tail_memory (state : MachineState) (extra : Nat) (small : extra≤5) :
    (checkerLowerFinishPrefix state (5+extra)).mem=(checkerLowerFinishPrefix state 5).mem := by
  have step (before : MachineState) (i : Fin 5) :
      (execInstrBr before (checkerLowerFinishOps.getD (5+i.val) .EBREAK)).mem=before.mem := by
    fin_cases i
    · exact path_jal_memory before 2096612
    · exact path_add_memory before .x21 .x30
    · exact path_shift_memory before 1
    · exact path_addi_memory before 4095
    · exact path_bne_memory before 7488
  induction extra with
  | zero => rfl
  | succ extra ih =>
    rw [show 5+(extra+1)=(5+extra)+1 by omega,checker_lower_finish_succ,
      step _ ⟨extra,by omega⟩,ih (by omega)]

private theorem lower_finish_mask_memory (state : MachineState) (digest : state.getReg .x23=12288) :
    (checkerLowerFinishPrefix state 5).mem=
      (state.setMem (wordAddress 1539)
        ((state.getMem (wordAddress 1539) <<< 18) >>> 18)).mem := by
  repeat rw [checker_lower_finish_succ]
  rw [checker_lower_finish_zero]
  have pointer : state.getReg .x23=12288#64 := digest
  simp [checkerLowerFinishOps,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,
    path_reg_mem,path_mem_pc,path_mem_reg,path_mem_store,MachineState.getMem,signExtend12,pointer,wordAddress]

theorem checker_lower_finish_memory (state : MachineState) (digest : state.getReg .x23=12288) :
    (checkerLowerFinishPrefix state 10).mem=(truncLower state).mem := by
  rw [show 10=5+5 from rfl,lower_finish_tail_memory _ _ (by decide),lower_finish_mask_memory state digest]
  funext query
  rw [path_mem_store,trunc_lower_mem state digest query]
  dsimp only
  split_ifs with hit
  · subst query
    exact shift_mask _
  · rfl

theorem checker_lower_finish_node (state : MachineState) (digest : state.getReg .x23=12288) :
    (readBuffer (checkerLowerFinishPrefix state 10) 12288 32).setWidth 238=
      (readBuffer state 12288 32).setWidth 238 := by
  rw [read_buffer_memory_congr _ _ (checker_lower_finish_memory state digest) 12288 32,
    trunc_lower_digest state digest]
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_ofNat,Nat.testBit_mod_two_pow,BitVec.testBit_toNat]
  simp [inside,show bit<256 by omega]

theorem final_value_node (height : Height) (value : Output) :
    (finalValue height value).setWidth 238=nodeDigest (width height) value := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [finalValue,nodeDigest,lowBits,BitVec.getLsbD_setWidth,BitVec.getLsbD_ofNat,
    BitVec.testBit_toNat,BitVec.getLsbD_extractLsb',Nat.testBit_mod_two_pow,Nat.zero_add]
  simp [inside,show bit<256 by omega]

theorem checker_first_seed (state : MachineState) (recordBase : Nat) :
    checkerFirstRight state recordBase ++ checkerFirstLeft state recordBase=
      pathSeed (state.getReg .x6).toNat ((readBuffer state 12288 32).setWidth 238)
        ((readBuffer state (recordBase+16) 32).setWidth 238) := by
  have numeric : (state.getReg .x6 &&& 1).toNat=(state.getReg .x6).toNat%2 := by
    rw [BitVec.toNat_and]
    change (state.getReg .x6).toNat &&& (2^1-1)=_
    rw [Nat.and_two_pow_sub_one_eq_mod]
  have even : state.getReg .x6 &&& 1=0 ↔ (state.getReg .x6).toNat%2=0 := by
    constructor
    · intro same
      rw [←numeric,same]
      rfl
    · intro same
      apply BitVec.eq_of_toNat_eq
      change (state.getReg .x6 &&& 1).toNat=0
      rw [numeric,same]
  simp only [checkerFirstRight,checkerFirstLeft,pathSeed,←even]
  split_ifs <;> rfl

theorem recorded_evaluation_support {α : Type} (oracle : Oracle) (program : OracleComp World α) :
    (checkEvaluation oracle (recordRows program)).1.1∈support program := by
  have reached := check_evaluation_support oracle program
  have erase := congrArg Prod.fst (TwoPermutationPrototype.Checker.check_record_erase oracle program)
  rwa [←erase] at reached

theorem recorded_single_step {enc : Encoding} {schedule widths : Height → Nat}
    {rows : List PublicRow} {node level : Nat} {child sibling root : Node}
    {height : Height} {seed : Seed} {values : Nat → Output}
    (atHeight : height.val=level) (children : seed=pathSeed node child sibling)
    (chain : RecordedChain enc schedule rows height seed values)
    (parent : root=nodeDigest (widths height) (values (schedule height-1))) :
    RecordedPath enc schedule widths rows node level 1 child root := by
  subst seed
  subst root
  exact RecordedPath.step atHeight chain (RecordedPath.done _ _ _)

theorem recorded_path_prepend {enc : Encoding} {schedule widths : Height → Nat}
    {rows : List PublicRow} {node level count : Nat} {child middle root : Node}
    (first : RecordedPath enc schedule widths rows node level 1 child middle)
    (later : RecordedPath enc schedule widths rows (node/2) (level+1) count middle root) :
    RecordedPath enc schedule widths rows node level (count+1) child root := by
  cases first with
  | step atHeight chain tail =>
    cases tail
    exact RecordedPath.step atHeight chain later

theorem recorded_path_prepend_rows {enc : Encoding} {schedule widths : Height → Nat}
    {earlier later : List PublicRow} {node level count : Nat} {child middle root : Node}
    (first : RecordedPath enc schedule widths earlier node level 1 child middle)
    (tail : RecordedPath enc schedule widths later (node/2) (level+1) count middle root) :
    RecordedPath enc schedule widths (earlier++later) node level (count+1) child root := by
  apply recorded_path_prepend
  · exact first.mono (by intro row member; exact List.mem_append.mpr (Or.inl member))
  · exact tail.mono (by intro row member; exact List.mem_append.mpr (Or.inr member))

@[irreducible] noncomputable def firstHashObservation (oracle : Oracle) (state : MachineState) :=
  checkEvaluation oracle (recordRows (checkerFirstSiblingHashTrace state))

@[irreducible] noncomputable def firstLowerObservation (oracle : Oracle) (state : MachineState) :=
  checkEvaluation oracle (recordRows (checkerFirstLowerTrace state))

theorem first_hash_observation_eq (oracle : Oracle) (state : MachineState) :
    firstHashObservation oracle state=checkEvaluation oracle (recordRows (checkerFirstSiblingHashTrace state)) := by
  rw [firstHashObservation]

theorem first_lower_observation_eq (oracle : Oracle) (state : MachineState) :
    firstLowerObservation oracle state=checkEvaluation oracle (recordRows (checkerFirstLowerTrace state)) := by
  rw [firstLowerObservation]

theorem first_lower_observation_map (oracle : Oracle) (state : MachineState) :
    firstLowerObservation oracle state=
      ((checkerLowerFinishPrefix (checkerHashReturned .lower (firstHashObservation oracle state).1.1) 10,
        (firstHashObservation oracle state).1.2),(firstHashObservation oracle state).2) := by
  have mapped := record_map_evaluation oracle
    (fun out => checkerLowerFinishPrefix (checkerHashReturned .lower out) 10) (checkerFirstSiblingHashTrace state)
  rw [←first_hash_observation_eq] at mapped
  rw [first_lower_observation_eq]
  simpa only [checkerFirstLowerTrace,map_eq_bind_pure_comp,Function.comp_def] using mapped

theorem observed_map_rows {α β γ : Type} (before after : (α × β) × γ) (update : α → α)
    (mapped : after=((update before.1.1,before.1.2),before.2)) : after.1.2=before.1.2 := by
  rw [mapped]

theorem first_lower_observation_rows (oracle : Oracle) (state : MachineState) :
    (firstLowerObservation oracle state).1.2=(firstHashObservation oracle state).1.2 := by
  exact observed_map_rows (firstHashObservation oracle state) (firstLowerObservation oracle state)
    (fun out => checkerLowerFinishPrefix (checkerHashReturned .lower out) 10)
    (first_lower_observation_map oracle state)

theorem first_hash_observation_support (oracle : Oracle) (state : MachineState) :
    (firstHashObservation oracle state).1.1∈support (checkerFirstSiblingHashTrace state) := by
  rw [first_hash_observation_eq]
  exact recorded_evaluation_support oracle _

@[irreducible] def firstRecordedHeight : Height := ⟨0,by decide⟩

theorem first_recorded_height_val : firstRecordedHeight.val=0 := by rw [firstRecordedHeight]

@[irreducible] def firstRecordedSeed (state : MachineState) (base : Nat) : Seed :=
  checkerFirstRight state base ++ checkerFirstLeft state base

@[irreducible] noncomputable def firstRecordedValues (oracle : Oracle) (state : MachineState) (base : Nat) :=
  canonicalChainValue oracle firstRecordedHeight (firstRecordedSeed state base)

theorem first_recorded_seed_eq (state : MachineState) (base : Nat) :
    firstRecordedSeed state base=pathSeed (state.getReg .x6).toNat
      ((readBuffer state 12288 32).setWidth 238) ((readBuffer state (base+16) 32).setWidth 238) := by
  rw [firstRecordedSeed]
  exact checker_first_seed state base

theorem first_hash_observation_chain (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    RecordedChain canonicalEncoding calls (firstHashObservation oracle state).1.2 firstRecordedHeight
      (firstRecordedSeed state base.value) (firstRecordedValues oracle state base.value) ∧
    readBuffer (firstHashObservation oracle state).1.1 256 32=finalValue firstRecordedHeight
      (firstRecordedValues oracle state base.value (calls firstRecordedHeight-1)) := by
  rw [first_hash_observation_eq,firstRecordedValues,firstRecordedSeed,firstRecordedHeight]
  exact checker_first_sibling_recorded_chain oracle input state ready

theorem first_lower_observation_node (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    (readBuffer (firstLowerObservation oracle state).1.1 12288 32).setWidth 238=
      nodeDigest (width firstRecordedHeight)
        (firstRecordedValues oracle state base.value (calls firstRecordedHeight-1)) := by
  have reached := first_hash_observation_support oracle state
  have destination := checker_first_sibling_destination input state _ ready reached
  have digest := checker_first_sibling_return_digest input state _ ready reached
  have value := (first_hash_observation_chain oracle input state ready).2
  rw [first_lower_observation_map,checker_lower_finish_node _ digest,
    checker_returned_lower_buffer _ destination,value,final_value_node]

theorem first_lower_observation_path (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    RecordedPath canonicalEncoding calls width (firstLowerObservation oracle state).1.2
      (state.getReg .x6).toNat 0 1 ((readBuffer state 12288 32).setWidth 238)
      ((readBuffer (firstLowerObservation oracle state).1.1 12288 32).setWidth 238) := by
  have chain := (first_hash_observation_chain oracle input state ready).1
  rw [←first_lower_observation_rows oracle state] at chain
  exact recorded_single_step first_recorded_height_val (first_recorded_seed_eq state base.value) chain
    (first_lower_observation_node oracle input state ready)

theorem checker_first_lower_recorded_path (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    let observed := checkEvaluation oracle (recordRows (checkerFirstLowerTrace state))
    RecordedPath canonicalEncoding calls width observed.1.2 (state.getReg .x6).toNat 0 1
      ((readBuffer state 12288 32).setWidth 238) ((readBuffer observed.1.1 12288 32).setWidth 238) := by
  rw [←first_lower_observation_eq]
  exact first_lower_observation_path oracle input state ready

theorem later_pad_word_away (order : FirstSiblingOrder) (state : MachineState)
    (pair : state.getReg .x24=12544) (query : Word)
    (away : query≠match order with | .even => 12600 | .odd => 12568) :
    (checkerLaterPadState order state).getMem query=state.getMem query := by
  rw [checkerLaterPadState]
  change (state.setHalfword (state.getReg .x24+signExtend12 order.laterPadOffset) 0).getMem query=_
  rw [pair]
  cases order with
  | even =>
    change (if query==(12600 : Word) then _ else _)=_
    simp only [beq_iff_eq,ite_eq_right away,MachineState.getMem]
  | odd =>
    change (if query==(12568 : Word) then _ else _)=_
    simp only [beq_iff_eq,ite_eq_right away,MachineState.getMem]

theorem later_pad_buffer_away (order : FirstSiblingOrder) (state : MachineState)
    (pair : state.getReg .x24=12544) (address : Nat) (aligned : address%8=0)
    (away : ∀ i < 4, BitVec.ofNat 64 (address+8*i)≠match order with | .even => 12600 | .odd => 12568) :
    readBuffer (checkerLaterPadState order state) address 32=readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i inside
  exact later_pad_word_away order state pair _ (away i inside)

theorem later_dispatch_buffer (state : MachineState) (address : Nat) :
    readBuffer (checkerLaterDispatchPrefix state 5) address 32=readBuffer state address 32 := by
  apply read_buffer_memory_congr
  funext query
  exact checker_later_dispatch_memory state query

theorem later_jump_buffer (order : FirstSiblingOrder) (state : MachineState) (address : Nat) :
    readBuffer (checkerLaterJumpState order state) address 32=readBuffer state address 32 := by
  apply read_buffer_memory_congr
  funext query
  exact checker_later_jump_memory order state query

theorem later_ordered_child_buffer {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) :
    readBuffer (checkerLaterOrderedState state)
      (if state.getReg .x6 &&& 1=0 then 12544 else 12576) 32=readBuffer state 12288 32 := by
  have digest : (checkerLaterDispatchPrefix state 5).getReg .x23=12288 :=
    (checker_later_dispatch_register _ _ (by decide) (by decide)).trans ready.digest
  have pair : (checkerLaterDispatchPrefix state 5).getReg .x24=12544 :=
    (checker_later_dispatch_register _ _ (by decide) (by decide)).trans ready.pair
  have ordered : 12576≤checkerLowerCursor ⟨height.val,by omega⟩ base.value := by
    have := base.above
    simp only [checkerLowerCursor]
    omega
  by_cases even : state.getReg .x6 &&& 1=0
  · have childPair := (checker_first_child_register .even (checkerLaterDispatchPrefix state 5) 8
        (by omega) .x24 (by decide)).trans pair
    have copyPair := (checker_copy_register .even
        (checkerFirstChildPrefix .even (checkerLaterDispatchPrefix state 5) 8) .x24 (by decide)).trans childPair
    rw [ite_eq_left even,checkerLaterOrderedState,ite_eq_left even,later_jump_buffer,
      later_pad_buffer_away .even _ copyPair _ (by decide)
        (by intro i inside; interval_cases i <;> decide),
      checker_copy_buffer_outside .even _ _ _ _ _ (checker_later_even_copy_ready height state ready even)
        ordered (by decide) (Or.inr (by decide))]
    have child := checker_first_child_buffer .even (checkerLaterDispatchPrefix state 5) digest pair
    simpa only [FirstSiblingOrder.childOffset,Nat.add_zero,later_dispatch_buffer] using child
  · have copyPair := (checker_copy_register .odd (checkerLaterDispatchPrefix state 5) .x24 (by decide)).trans pair
    have padPair := (checker_later_pad_register .odd
        (checkerCopyState .odd (checkerLaterDispatchPrefix state 5)) .x24).trans copyPair
    have padDigest := (checker_later_pad_register .odd
        (checkerCopyState .odd (checkerLaterDispatchPrefix state 5)) .x23).trans
      ((checker_copy_register .odd (checkerLaterDispatchPrefix state 5) .x23 (by decide)).trans digest)
    rw [ite_eq_right even,checkerLaterOrderedState,ite_eq_right even,later_jump_buffer]
    have child := checker_first_child_buffer .odd
      (checkerLaterPadState .odd (checkerCopyState .odd (checkerLaterDispatchPrefix state 5))) padDigest padPair
    rw [show 12576=12544+FirstSiblingOrder.childOffset .odd from rfl,child,
      later_pad_buffer_away .odd _ copyPair _ (by decide)
        (by intro i inside; interval_cases i <;> decide),
      checker_copy_buffer_outside .odd _ _ _ _ _ (checker_later_odd_copy_ready height state ready even)
        (by omega) (by decide) (Or.inr (by decide)),later_dispatch_buffer]

theorem later_caller_buffer (state : MachineState) (address : Nat) :
    readBuffer (checkerLaterCaller state) address 32=readBuffer (checkerLaterOrderedState state) address 32 := by
  apply read_buffer_memory_congr
  funext query
  rw [checkerLaterCaller]
  exact checker_first_hash_call_memory (checkerLaterOrderedState state) query

theorem word_even_iff (word : Word) : word &&& 1=0 ↔ word.toNat%2=0 := by
  have numeric : (word &&& 1).toNat=word.toNat%2 := by
    rw [BitVec.toNat_and]
    change word.toNat &&& (2^1-1)=_
    rw [Nat.and_two_pow_sub_one_eq_mod]
  constructor
  · intro same
    rw [←numeric,same]
    rfl
  · intro same
    apply BitVec.eq_of_toNat_eq
    change (word &&& 1).toNat=0
    rw [numeric,same]

@[irreducible] def laterRecordedSeed (state : MachineState) : Seed :=
  (readBuffer (checkerLaterCaller state) 12576 32).setWidth 238 ++
    (readBuffer (checkerLaterCaller state) 12544 32).setWidth 238

@[irreducible] def laterRecordedSibling (state : MachineState) : Node :=
  if state.getReg .x6 &&& 1=0 then (readBuffer (checkerLaterOrderedState state) 12576 32).setWidth 238
  else (readBuffer (checkerLaterOrderedState state) 12544 32).setWidth 238

theorem later_recorded_seed_eq {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) :
    laterRecordedSeed state=pathSeed (state.getReg .x6).toNat
      ((readBuffer state 12288 32).setWidth 238) (laterRecordedSibling state) := by
  have child := later_ordered_child_buffer height state ready
  rw [laterRecordedSeed,laterRecordedSibling]
  simp only [pathSeed,←word_even_iff,later_caller_buffer]
  by_cases even : state.getReg .x6 &&& 1=0
  · simp only [even,ite_true] at child ⊢
    rw [child]
  · simp only [even,ite_false] at child ⊢
    rw [child]

@[irreducible] noncomputable def laterHashObservation (oracle : Oracle) (height : Fin 16) (state : MachineState) :=
  checkEvaluation oracle (recordRows (checkerLaterHashTrace height state))

@[irreducible] noncomputable def laterLowerObservation (oracle : Oracle) (height : Fin 16) (state : MachineState) :=
  checkEvaluation oracle (recordRows (checkerLaterLowerTrace height state))

theorem later_hash_observation_eq (oracle : Oracle) (height : Fin 16) (state : MachineState) :
    laterHashObservation oracle height state=checkEvaluation oracle (recordRows (checkerLaterHashTrace height state)) := by
  rw [laterHashObservation]

theorem later_lower_observation_eq (oracle : Oracle) (height : Fin 16) (state : MachineState) :
    laterLowerObservation oracle height state=checkEvaluation oracle (recordRows (checkerLaterLowerTrace height state)) := by
  rw [laterLowerObservation]

theorem later_lower_observation_map (oracle : Oracle) (height : Fin 16) (state : MachineState) :
    laterLowerObservation oracle height state=
      ((checkerLowerFinishPrefix (checkerHashReturned .lower (laterHashObservation oracle height state).1.1) 10,
        (laterHashObservation oracle height state).1.2),(laterHashObservation oracle height state).2) := by
  have mapped := record_map_evaluation oracle
    (fun out => checkerLowerFinishPrefix (checkerHashReturned .lower out) 10) (checkerLaterHashTrace height state)
  rw [←later_hash_observation_eq] at mapped
  rw [later_lower_observation_eq]
  simpa only [checkerLaterLowerTrace,map_eq_bind_pure_comp,Function.comp_def] using mapped

theorem later_lower_observation_rows (oracle : Oracle) (height : Fin 16) (state : MachineState) :
    (laterLowerObservation oracle height state).1.2=(laterHashObservation oracle height state).1.2 := by
  exact observed_map_rows (laterHashObservation oracle height state) (laterLowerObservation oracle height state)
    (fun out => checkerLowerFinishPrefix (checkerHashReturned .lower out) 10)
    (later_lower_observation_map oracle height state)

@[irreducible] noncomputable def laterRecordedValues (oracle : Oracle) (height : Fin 16) (state : MachineState) :=
  canonicalChainValue oracle ⟨height.val,by omega⟩ (laterRecordedSeed state)

theorem later_hash_observation_chain (oracle : Oracle) {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) :
    RecordedChain canonicalEncoding calls (laterHashObservation oracle height state).1.2 ⟨height.val,by omega⟩
      (laterRecordedSeed state) (laterRecordedValues oracle height state) ∧
    readBuffer (laterHashObservation oracle height state).1.1 256 32=finalValue ⟨height.val,by omega⟩
      (laterRecordedValues oracle height state (calls ⟨height.val,by omega⟩-1)) := by
  rw [laterRecordedValues,laterRecordedSeed,later_hash_observation_eq,checkerLaterHashTrace]
  exact checker_lower_hash_recorded_chain oracle height (checkerLaterCaller state)
    (checker_later_caller_pc height state ready) (checker_later_caller_pair height state ready)
    (checker_later_caller_counter height state ready)

theorem later_lower_observation_node (oracle : Oracle) {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) :
    (readBuffer (laterLowerObservation oracle height state).1.1 12288 32).setWidth 238=
      nodeDigest (width ⟨height.val,by omega⟩)
        (laterRecordedValues oracle height state (calls ⟨height.val,by omega⟩-1)) := by
  have reached : (laterHashObservation oracle height state).1.1∈support (checkerLaterHashTrace height state) := by
    rw [later_hash_observation_eq]
    exact recorded_evaluation_support oracle _
  have destination := checker_later_hash_destination height state _ ready reached
  have digest := checker_later_return_digest height state _ ready reached
  rw [later_lower_observation_map,checker_lower_finish_node _ digest,
    checker_returned_lower_buffer _ destination,(later_hash_observation_chain oracle height state ready).2,final_value_node]

theorem later_lower_observation_path (oracle : Oracle) {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) :
    RecordedPath canonicalEncoding calls width (laterLowerObservation oracle height state).1.2
      (state.getReg .x6).toNat height.val 1 ((readBuffer state 12288 32).setWidth 238)
      ((readBuffer (laterLowerObservation oracle height state).1.1 12288 32).setWidth 238) := by
  have chain := (later_hash_observation_chain oracle height state ready).1
  rw [←later_lower_observation_rows oracle height state] at chain
  exact recorded_single_step rfl (later_recorded_seed_eq height state ready) chain
    (later_lower_observation_node oracle height state ready)

theorem checker_later_lower_recorded_path (oracle : Oracle) {base : CheckerRecordBase} (height : Fin 16)
    (state : MachineState) (ready : CheckerLaterPathReady height state base) :
    let observed := checkEvaluation oracle (recordRows (checkerLaterLowerTrace height state))
    RecordedPath canonicalEncoding calls width observed.1.2 (state.getReg .x6).toNat height.val 1
      ((readBuffer state 12288 32).setWidth 238) ((readBuffer observed.1.1 12288 32).setWidth 238) := by
  rw [←later_lower_observation_eq]
  exact later_lower_observation_path oracle height state ready

@[irreducible] noncomputable def lowerSuffixObservation (oracle : Oracle) (count : Nat)
    (height : Fin 17) (room : height.val+count≤16) (state : MachineState) :=
  checkEvaluation oracle (recordRows (checkerLowerSuffixTrace count height room state))

theorem lower_suffix_observation_eq (oracle : Oracle) (count : Nat) (height : Fin 17)
    (room : height.val+count≤16) (state : MachineState) :
    lowerSuffixObservation oracle count height room state=
      checkEvaluation oracle (recordRows (checkerLowerSuffixTrace count height room state)) := by
  rw [lowerSuffixObservation]

theorem lower_suffix_observation_succ (oracle : Oracle) (count : Nat) (height : Fin 17)
    (room : height.val+(count+1)≤16) (state : MachineState) :
    lowerSuffixObservation oracle (count+1) height room state=
      let first := laterLowerObservation oracle ⟨height.val,by omega⟩ state
      let later := lowerSuffixObservation oracle count ⟨height.val+1,by omega⟩
        (by change height.val+1+count≤16; omega) first.1.1
      ((later.1.1,first.1.2++later.1.2),first.2+later.2) := by
  rw [lower_suffix_observation_eq,checkerLowerSuffixTrace,recorded_bind_evaluation,
    ←later_lower_observation_eq]
  dsimp only
  rw [←lower_suffix_observation_eq]

theorem lower_suffix_observation_path (oracle : Oracle) {base : CheckerRecordBase} (count : Nat)
    (height : Fin 17) (room : height.val+count≤16) (state : MachineState)
    (positive : 0<height.val) (ready : CheckerLowerLoopReady height state base) :
    RecordedPath canonicalEncoding calls width (lowerSuffixObservation oracle count height room state).1.2
      (state.getReg .x6).toNat height.val count ((readBuffer state 12288 32).setWidth 238)
      ((readBuffer (lowerSuffixObservation oracle count height room state).1.1 12288 32).setWidth 238) := by
  induction count generalizing height state with
  | zero =>
    rw [lower_suffix_observation_eq,checkerLowerSuffixTrace,record_rows_pure,check_evaluation_pure]
    exact RecordedPath.done _ _ _
  | succ count ih =>
    have active : height.val<16 := by omega
    have stepReady := checker_lower_loop_later height state positive active ready
    have reached : (laterLowerObservation oracle ⟨height.val,active⟩ state).1.1∈
        support (checkerLaterLowerTrace ⟨height.val,active⟩ state) := by
      rw [later_lower_observation_eq]
      exact recorded_evaluation_support oracle _
    have first := later_lower_observation_path oracle ⟨height.val,active⟩ state stepReady
    have next := checker_later_lower_next ⟨height.val,active⟩ state _ stepReady reached
    have tail := ih ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega) _
      (by change 0<height.val+1; omega) next
    have node : ((laterLowerObservation oracle ⟨height.val,active⟩ state).1.1.getReg .x6).toNat=
        (state.getReg .x6).toNat/2 := by
      rw [(checker_later_lower_values ⟨height.val,active⟩ state _ stepReady reached).2.1]
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.pow_one]
    rw [node] at tail
    rw [lower_suffix_observation_succ]
    exact recorded_path_prepend_rows first tail

@[irreducible] noncomputable def lowerSixteenObservation (oracle : Oracle) (state : MachineState) :=
  checkEvaluation oracle (recordRows (checkerLowerSixteenTrace state))

theorem lower_sixteen_observation_eq (oracle : Oracle) (state : MachineState) :
    lowerSixteenObservation oracle state=checkEvaluation oracle (recordRows (checkerLowerSixteenTrace state)) := by
  rw [lowerSixteenObservation]

theorem lower_sixteen_observation_bind (oracle : Oracle) (state : MachineState) :
    lowerSixteenObservation oracle state=
      let first := firstLowerObservation oracle state
      let later := lowerSuffixObservation oracle 15 ⟨1,by decide⟩ (by decide) first.1.1
      ((later.1.1,first.1.2++later.1.2),first.2+later.2) := by
  rw [lower_sixteen_observation_eq,checkerLowerSixteenTrace,recorded_bind_evaluation,
    ←first_lower_observation_eq]
  dsimp only
  rw [←lower_suffix_observation_eq]

theorem checker_lower_suffix_recorded_path (oracle : Oracle) {base : CheckerRecordBase} (count : Nat)
    (height : Fin 17) (room : height.val+count≤16) (state : MachineState)
    (positive : 0<height.val) (ready : CheckerLowerLoopReady height state base) :
    let observed := checkEvaluation oracle (recordRows (checkerLowerSuffixTrace count height room state))
    RecordedPath canonicalEncoding calls width observed.1.2 (state.getReg .x6).toNat height.val count
      ((readBuffer state 12288 32).setWidth 238) ((readBuffer observed.1.1 12288 32).setWidth 238) := by
  rw [←lower_suffix_observation_eq]
  exact lower_suffix_observation_path oracle count height room state positive ready

@[irreducible] noncomputable def firstBoundaryState (oracle : Oracle) (state : MachineState) : MachineState :=
  (firstLowerObservation oracle state).1.1

theorem first_boundary_state_eq (oracle : Oracle) (state : MachineState) :
    firstBoundaryState oracle state=(firstLowerObservation oracle state).1.1 := by
  rw [firstBoundaryState]

theorem first_boundary_support (oracle : Oracle) (state : MachineState) :
    firstBoundaryState oracle state∈support (checkerFirstLowerTrace state) := by
  rw [first_boundary_state_eq,first_lower_observation_eq]
  exact recorded_evaluation_support oracle _

theorem first_boundary_ready (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    CheckerLowerLoopReady ⟨1,by decide⟩ (firstBoundaryState oracle state) base :=
  checker_first_lower_next input state _ ready (first_boundary_support oracle state)

theorem first_boundary_index (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    (firstBoundaryState oracle state).getReg .x6=state.getReg .x6 >>> 1 :=
  (checker_first_lower_values input state _ ready (first_boundary_support oracle state)).2.1

theorem shifted_word_nat (before after : Word) (shifted : after=before >>> 1) :
    after.toNat=before.toNat/2 := by
  rw [shifted]
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.pow_one]

theorem first_boundary_index_nat (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    ((firstBoundaryState oracle state).getReg .x6).toNat=(state.getReg .x6).toNat/2 :=
  shifted_word_nat _ _ (first_boundary_index oracle input state ready)

theorem first_boundary_node (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    (readBuffer (firstBoundaryState oracle state) 12288 32).setWidth 238=
      nodeDigest (width firstRecordedHeight)
        (firstRecordedValues oracle state base.value (calls firstRecordedHeight-1)) := by
  rw [first_boundary_state_eq]
  exact first_lower_observation_node oracle input state ready

theorem first_boundary_path (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    RecordedPath canonicalEncoding calls width (firstLowerObservation oracle state).1.2
      (state.getReg .x6).toNat 0 1 ((readBuffer state 12288 32).setWidth 238)
      ((readBuffer (firstBoundaryState oracle state) 12288 32).setWidth 238) := by
  rw [first_boundary_state_eq]
  exact first_lower_observation_path oracle input state ready

theorem height_one_suffix_path (oracle : Oracle) {base : CheckerRecordBase} (count : Nat)
    (closes : count+1=16) (state : MachineState) (ready : CheckerLowerLoopReady ⟨1,by decide⟩ state base) :
    RecordedPath canonicalEncoding calls width
      (lowerSuffixObservation oracle count ⟨1,by decide⟩ (by change 1+count≤16; omega) state).1.2
      (state.getReg .x6).toNat 1 count ((readBuffer state 12288 32).setWidth 238)
      ((readBuffer (lowerSuffixObservation oracle count ⟨1,by decide⟩
        (by change 1+count≤16; omega) state).1.1 12288 32).setWidth 238) :=
  lower_suffix_observation_path oracle count ⟨1,by decide⟩ _ state (by decide) ready

theorem height_one_fifteen_suffix_path (oracle : Oracle) {base : CheckerRecordBase}
    (state : MachineState) (ready : CheckerLowerLoopReady ⟨1,by decide⟩ state base) :
    let observed := lowerSuffixObservation oracle 15 ⟨1,by decide⟩ (by decide) state
    RecordedPath canonicalEncoding calls width observed.1.2 (state.getReg .x6).toNat 1 15
      ((readBuffer state 12288 32).setWidth 238) ((readBuffer observed.1.1 12288 32).setWidth 238) :=
  height_one_suffix_path oracle 15 (by decide) state ready

theorem recorded_observation_prepend {α : Type} {enc : Encoding} {schedule widths : Height → Nat}
    (node : α → Nat) (digest : α → Node) (before : α)
    (first later whole : (α × List PublicRow) × Nat) (level count : Nat)
    (mapped : whole=((later.1.1,first.1.2++later.1.2),first.2+later.2))
    (index : node first.1.1=node before/2)
    (head : RecordedPath enc schedule widths first.1.2 (node before) level 1
      (digest before) (digest first.1.1))
    (tail : RecordedPath enc schedule widths later.1.2 (node first.1.1) (level+1) count
      (digest first.1.1) (digest later.1.1)) :
    RecordedPath enc schedule widths whole.1.2 (node before) level (count+1)
      (digest before) (digest whole.1.1) := by
  rw [mapped]
  apply recorded_path_prepend_rows head
  simpa only [index] using tail

theorem lower_sixteen_boundary_bind (oracle : Oracle) (state : MachineState) :
    lowerSixteenObservation oracle state=
      let first := ((firstBoundaryState oracle state,(firstLowerObservation oracle state).1.2),
        (firstLowerObservation oracle state).2)
      let later := lowerSuffixObservation oracle 15 ⟨1,by decide⟩ (by decide) first.1.1
      ((later.1.1,first.1.2++later.1.2),first.2+later.2) := by
  have mapped := lower_sixteen_observation_bind oracle state
  dsimp only at mapped ⊢
  rw [←first_boundary_state_eq] at mapped
  exact mapped

theorem lower_sixteen_observation_path (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    RecordedPath canonicalEncoding calls width (lowerSixteenObservation oracle state).1.2
      (state.getReg .x6).toNat 0 16 ((readBuffer state 12288 32).setWidth 238)
      ((readBuffer (lowerSixteenObservation oracle state).1.1 12288 32).setWidth 238) :=
  recorded_observation_prepend (fun s : MachineState => (s.getReg .x6).toNat)
    (fun s => (readBuffer s 12288 32).setWidth 238) state
    ((firstBoundaryState oracle state,(firstLowerObservation oracle state).1.2),
      (firstLowerObservation oracle state).2)
    (lowerSuffixObservation oracle 15 ⟨1,by decide⟩ (by decide) (firstBoundaryState oracle state))
    (lowerSixteenObservation oracle state) 0 15
    (lower_sixteen_boundary_bind oracle state) (first_boundary_index_nat oracle input state ready)
    (first_boundary_path oracle input state ready)
    (height_one_fifteen_suffix_path oracle _ (first_boundary_ready oracle input state ready))

theorem checker_lower_sixteen_recorded_path (oracle : Oracle) {base : CheckerRecordBase} {record : Nat}
    (input : CheckInput) (state : MachineState) (ready : CheckerFirstPathReady input state base record) :
    let observed := checkEvaluation oracle (recordRows (checkerLowerSixteenTrace state))
    RecordedPath canonicalEncoding calls width observed.1.2 (state.getReg .x6).toNat 0 16
      ((readBuffer state 12288 32).setWidth 238) ((readBuffer observed.1.1 12288 32).setWidth 238) := by
  rw [←lower_sixteen_observation_eq]
  exact lower_sixteen_observation_path oracle input state ready

end CommitGolfCandidate.Chained.Native.Refinement
