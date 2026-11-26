import CommitGolfCandidate.ChainedCheckerPathRefinement

/-! Recorded cap hashes use the delivered wrapper's actual heap children. -/
namespace CommitGolfCandidate.Chained.Native.Refinement
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open RecordLeaf CheckerCap
set_option maxRecDepth 8192

private theorem cap_reg_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg=state.getReg reg := by cases reg <;> rfl
private theorem cap_mem_reg (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem=state.mem := by cases reg <;> rfl
private theorem cap_mem_pc (state : MachineState) (pc : Word) : (state.setPC pc).mem=state.mem := rfl
private theorem cap_mem_store (state : MachineState) (address value : Word) :
    (state.setMem address value).mem=(fun query => if query=address then value else state.mem query) := by
  funext query
  simp [MachineState.setMem]

theorem cap_mask_word_at (state : MachineState) (address : Word) (source : state.getReg .x10=address)
    (word : Fin 8) :
    (checkerChildMaskPrefix .cap state 9).getMem (address+BitVec.ofNat 64 (8*word.val))=
      if word.val=3 ∨ word.val=7 then
        (state.getMem (address+BitVec.ofNat 64 (8*word.val)) <<< 18) >>> 18
      else state.getMem (address+BitVec.ofNat 64 (8*word.val)) := by
  fin_cases word
  all_goals simp [checkerChildMaskPrefix,checkerChildMaskOps,CheckerHashSite.childReg,execInstrBr,source,
    MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,cap_reg_mem,signExtend12,
    MachineState.getMem,cap_mem_pc,cap_mem_reg,cap_mem_store]

theorem cap_prepared_word (height : Fin 8) (node : Fin 256) (state : MachineState)
    (source : state.getReg .x10=capSource node) (word : Fin 8) :
    (capPrepared height state).getMem (capSource node+BitVec.ofNat 64 (8*word.val))=
      if word.val=3 ∨ word.val=7 then
        (state.getMem (capSource node+BitVec.ofNat 64 (8*word.val)) <<< 18) >>> 18
      else state.getMem (capSource node+BitVec.ofNat 64 (8*word.val)) := by
  rw [capPrepared,checker_hash_abi_memory]
  change (capScheduled height (capMasked state)).mem _=_
  rw [cap_scheduled_memory]
  change (capMasked state).getMem _=_
  rw [capMasked,cap_mask_word_at _ _ ((checker_snapshot_register 31 state (by omega) .x10).trans source)]
  simp only [checker_snapshot_memory_frame 31 state (by omega) _
    (fun slot => (cap_source_saved_apart node slot word).symm)]

theorem cap_prepared_children (height : Fin 8) (node : Fin 256) (state : MachineState)
    (source : state.getReg .x10=capSource node) (word : Fin 8) :
    (capPrepared height state).getMem (capSource node+BitVec.ofNat 64 (8*word.val))=
      if word.val<4 then childWord ((readBuffer state (16384+64*node.val) 32).setWidth 238) word.val
      else childWord ((readBuffer state (16384+64*node.val+32) 32).setWidth 238) (word.val-4) := by
  have left (i : Fin 4) :
      (capPrepared height state).getMem (capSource node+BitVec.ofNat 64 (8*i.val))=
        childWord ((readBuffer state (16384+64*node.val) 32).setWidth 238) i.val := by
    rw [cap_prepared_word height node state source ⟨i.val,by omega⟩,lower_child_word _ i,
      read_digest_word state _ i.val (by omega) i.isLt]
    simp only [show i.val≠7 by omega,or_false,capSource,BitVec.ofNat_add]
  have right (i : Fin 4) :
      (capPrepared height state).getMem (capSource node+BitVec.ofNat 64 (8*(i.val+4)))=
        childWord ((readBuffer state (16384+64*node.val+32) 32).setWidth 238) i.val := by
    have address : capSource node+BitVec.ofNat 64 (8*(i.val+4))=
        BitVec.ofNat 64 (16384+64*node.val+32+8*i.val) := by
      rw [capSource,←BitVec.ofNat_add]
      congr 1
      omega
    rw [cap_prepared_word height node state source ⟨i.val+4,by omega⟩,lower_child_word _ i,
      read_digest_word state _ i.val (by omega) i.isLt,address]
    simp only [show i.val+4≠3 by omega,show (i.val+4=7)↔i.val=3 by omega,false_or]
  by_cases inside : word.val<4
  · simpa only [ite_eq_left inside] using left ⟨word.val,inside⟩
  · have offset : word.val-4+4=word.val := by omega
    simpa only [ite_eq_right inside,offset] using right ⟨word.val-4,by omega⟩

theorem checker_cap_hash_recorded_chain (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2861)
    (parent : state.getReg .x6=BitVec.ofNat 64 node.val) (source : state.getReg .x10=capSource node) :
    let seed := (readBuffer state (16384+64*node.val+32) 32).setWidth 238 ++
      (readBuffer state (16384+64*node.val) 32).setWidth 238
    let observed := checkEvaluation oracle (recordRows (capParentTrace height state))
    RecordedChain canonicalEncoding calls observed.1.2 (CheckerCap.capHeight height) seed
      (canonicalChainValue oracle (CheckerCap.capHeight height) seed) ∧
      readBuffer observed.1.1 256 32=finalValue (CheckerCap.capHeight height)
        (canonicalChainValue oracle (CheckerCap.capHeight height) seed (calls (CheckerCap.capHeight height)-1)) := by
  have ready := cap_prepared_ready height node range state pc parent source
  apply checker_hash_recorded_chain oracle .cap 0 (by decide) _ ready.args (CheckerCap.capHeight height)
    _ _ ready.height ready.mask (by unfold calls CheckerCap.capHeight; dsimp only; split_ifs <;> omega)
  intro word
  rw [cap_prepared_source,source]
  exact cap_prepared_children height node state source word

@[irreducible] def capRecordedSeed (state : MachineState) (node : Fin 256) : Seed :=
  (readBuffer state (16384+64*node.val+32) 32).setWidth 238 ++
    (readBuffer state (16384+64*node.val) 32).setWidth 238

@[irreducible] noncomputable def capHashObservation (oracle : Oracle) (height : Fin 8) (state : MachineState) :=
  checkEvaluation oracle (recordRows (capParentTrace height state))

@[irreducible] noncomputable def capRecordedValues (oracle : Oracle) (height : Fin 8)
    (node : Fin 256) (state : MachineState) :=
  canonicalChainValue oracle (CheckerCap.capHeight height) (capRecordedSeed state node)

theorem cap_hash_observation_chain (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2861)
    (parent : state.getReg .x6=BitVec.ofNat 64 node.val) (source : state.getReg .x10=capSource node) :
    RecordedChain canonicalEncoding calls (capHashObservation oracle height state).1.2
      (CheckerCap.capHeight height) (capRecordedSeed state node) (capRecordedValues oracle height node state) ∧
      readBuffer (capHashObservation oracle height state).1.1 256 32=
        finalValue (CheckerCap.capHeight height)
          (capRecordedValues oracle height node state (calls (CheckerCap.capHeight height)-1)) := by
  rw [capHashObservation,capRecordedValues,capRecordedSeed]
  exact checker_cap_hash_recorded_chain oracle height node range state pc parent source

theorem cap_hash_observation_node (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2861)
    (parent : state.getReg .x6=BitVec.ofNat 64 node.val) (source : state.getReg .x10=capSource node) :
    (readBuffer (capHashObservation oracle height state).1.1 256 32).setWidth 238=
      nodeDigest (width (CheckerCap.capHeight height))
        (capRecordedValues oracle height node state (calls (CheckerCap.capHeight height)-1)) := by
  rw [(cap_hash_observation_chain oracle height node range state pc parent source).2,final_value_node]

theorem cap_left_seed_eq (state : MachineState) (node : Fin 256) :
    capRecordedSeed state node=pathSeed (2*node.val)
      ((readBuffer state (16384+64*node.val) 32).setWidth 238)
      ((readBuffer state (16384+64*node.val+32) 32).setWidth 238) := by
  rw [capRecordedSeed,pathSeed,ite_eq_left (by omega)]

theorem cap_right_seed_eq (state : MachineState) (node : Fin 256) :
    capRecordedSeed state node=pathSeed (2*node.val+1)
      ((readBuffer state (16384+64*node.val+32) 32).setWidth 238)
      ((readBuffer state (16384+64*node.val) 32).setWidth 238) := by
  rw [capRecordedSeed,pathSeed,ite_eq_right (by omega)]

theorem cap_hash_left_recorded_path (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2861)
    (parent : state.getReg .x6=BitVec.ofNat 64 node.val) (source : state.getReg .x10=capSource node) :
    RecordedPath canonicalEncoding calls width (capHashObservation oracle height state).1.2
      (2*node.val) (16+height.val) 1 ((readBuffer state (16384+64*node.val) 32).setWidth 238)
      ((readBuffer (capHashObservation oracle height state).1.1 256 32).setWidth 238) :=
  recorded_single_step rfl (cap_left_seed_eq state node)
    (cap_hash_observation_chain oracle height node range state pc parent source).1
    (cap_hash_observation_node oracle height node range state pc parent source)

theorem cap_hash_right_recorded_path (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2861)
    (parent : state.getReg .x6=BitVec.ofNat 64 node.val) (source : state.getReg .x10=capSource node) :
    RecordedPath canonicalEncoding calls width (capHashObservation oracle height state).1.2
      (2*node.val+1) (16+height.val) 1 ((readBuffer state (16384+64*node.val+32) 32).setWidth 238)
      ((readBuffer (capHashObservation oracle height state).1.1 256 32).setWidth 238) :=
  recorded_single_step rfl (cap_right_seed_eq state node)
    (cap_hash_observation_chain oracle height node range state pc parent source).1
    (cap_hash_observation_node oracle height node range state pc parent source)

theorem cap_result_memory (state : MachineState) (node : Fin 256)
    (destination : state.getMem (checkerSaveWord CheckerHashSite.cap.resultSlot)=capDestination node) :
    (checkerResultPrefix .cap state 9).mem=(Opening.fourWordStore state 256 (capDestination node)).mem := by
  change state.mem 88=capDestination node at destination
  have saved : state.mem 88#64=capDestination node := destination
  have zero : state.getReg .x0=0 := rfl
  have low (query offset : Nat) (small : query≤280) (short : offset≤24) :
      BitVec.ofNat 64 query≠capDestination node+BitVec.ofNat 64 offset := by
    rw [capDestination,←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  have lowZero (query : Nat) (small : query≤280) : BitVec.ofNat 64 query≠capDestination node := by
    change BitVec.ofNat 64 query≠BitVec.ofNat 64 (16384+32*node.val)
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  repeat rw [checker_result_succ]
  rw [checker_result_zero]
  simp [checkerResultOps,CheckerHashSite.resultSlot,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,
    cap_reg_mem,signExtend12,MachineState.getMem,cap_mem_pc,cap_mem_reg,cap_mem_store,
    zero,saved,Opening.fourWordStore,low,lowZero]

theorem cap_result_word (state : MachineState) (node : Fin 256)
    (destination : state.getMem (checkerSaveWord CheckerHashSite.cap.resultSlot)=capDestination node)
    (word : Fin 4) :
    (checkerResultPrefix .cap state 9).getMem (capDestination node+BitVec.ofNat 64 (8*word.val))=
      state.getMem ((256 : Word)+BitVec.ofNat 64 (8*word.val)) := by
  have copied := TwoPermutationPrototype.Checker.four_word_store_word state 256 (capDestination node)
    (2048+4*node.val) (by unfold capDestination wordAddress; congr 1; omega) (by omega) word
  simpa only [MachineState.getMem,cap_result_memory state node destination] using copied

theorem cap_returned_word (state : MachineState) (node : Fin 256)
    (destination : state.getMem (checkerSaveWord CheckerHashSite.cap.resultSlot)=capDestination node)
    (word : Fin 4) :
    (checkerHashReturned .cap state).getMem (capDestination node+BitVec.ofNat 64 (8*word.val))=
      state.getMem ((256 : Word)+BitVec.ofNat 64 (8*word.val)) := by
  rw [checkerHashReturned]
  change (checkerLoadBackPrefix (checkerResultPrefix .cap state 9) 31).getMem _=_
  rw [checker_load_back_memory _ _ (by decide)]
  exact cap_result_word state node destination word

theorem cap_returned_buffer (state : MachineState) (node : Fin 256)
    (destination : state.getMem (checkerSaveWord CheckerHashSite.cap.resultSlot)=capDestination node) :
    readBuffer (checkerHashReturned .cap state) (16384+32*node.val) 32=readBuffer state 256 32 := by
  apply output_ext_words
  intro word
  rw [read_digest_word _ _ _ (by omega) word.isLt,read_digest_word _ _ _ (by decide) word.isLt]
  simpa only [capDestination,BitVec.ofNat_add,show (256 : Word)=BitVec.ofNat 64 256 from rfl]
    using cap_returned_word state node destination word

theorem read_digest_bit (state : MachineState) (address bit : Nat) (aligned : address%8=0)
    (inside : bit<256) :
    (readBuffer state address 32).getLsbD bit=
      (state.getMem (BitVec.ofNat 64 (address+8*(bit/64)))).getLsbD (bit%64) := by
  have bits := congrArg (fun word : Word => word.getLsbD (bit%64))
    (read_digest_word state address (bit/64) aligned (by omega))
  have numeric : 64*(bit/64)+bit%64=bit := by omega
  simpa only [BitVec.getLsbD_extractLsb',show bit%64<64 by omega,decide_true,Bool.true_and,numeric] using bits

private theorem cap_jump_memory (state : MachineState) (offset : BitVec 21) :
    (execInstrBr state (.JAL .x0 offset)).mem=state.mem := rfl

theorem cap_finish_tail_memory (state : MachineState) :
    (capFinishPrefix state 7).mem=(capFinishPrefix state 5).mem := by
  rw [cap_finish_succ,show capFinishOps.getD 6 .EBREAK=.JAL .x0 2097108 from rfl,cap_jump_memory,
    cap_finish_succ,show capFinishOps.getD 5 .EBREAK=.JAL .x0 2097012 from rfl,cap_jump_memory]

theorem cap_finish_mask_memory (state : MachineState) :
    (capFinishPrefix state 7).mem=
      (state.setMem (state.getReg .x12+24) ((state.getMem (state.getReg .x12+24) <<< 18) >>> 18)).mem := by
  rw [cap_finish_tail_memory]
  repeat rw [cap_finish_succ]
  rw [cap_finish_zero]
  simp [capFinishOps,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,
    signExtend12,MachineState.getMem,cap_mem_pc,cap_mem_reg,cap_mem_store]

theorem cap_last_word_mask_node (state : MachineState) (node : Fin 256) :
    (readBuffer (state.setMem (capDestination node+24)
      ((state.getMem (capDestination node+24) <<< 18) >>> 18)) (16384+32*node.val) 32).setWidth 238=
      (readBuffer state (16384+32*node.val) 32).setWidth 238 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [BitVec.getLsbD_setWidth,inside,decide_true,Bool.true_and]
  rw [read_digest_bit _ _ bit (by omega) (by omega),read_digest_bit _ _ bit (by omega) (by omega)]
  have address : BitVec.ofNat 64 (16384+32*node.val+8*(bit/64))=
      capDestination node+BitVec.ofNat 64 (8*(bit/64)) := by rw [capDestination,←BitVec.ofNat_add]
  change ((state.setMem _ _).mem _).getLsbD _=(state.mem _).getLsbD _
  rw [cap_mem_store]
  dsimp only
  by_cases top : bit/64=3
  · have place : BitVec.ofNat 64 (16384+32*node.val+8*(bit/64))=capDestination node+24 := by
      rw [address,top]
      rfl
    rw [ite_eq_left place,place]
    simp [BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft,
      show 18+bit%64<64 by omega,show bit%64<64 by omega,MachineState.getMem]
  · have away : BitVec.ofNat 64 (16384+32*node.val+8*(bit/64))≠capDestination node+24 := by
      rw [address]
      intro same
      have offsets := (BitVec.add_right_inj _).mp same
      have different : BitVec.ofNat 64 (8*(bit/64))≠24 :=
        word_of_nat_ne (8*(bit/64)) (24 : Nat) (by omega) (by omega) (by omega)
      exact different offsets
    rw [ite_eq_right away]

theorem cap_finish_node (state : MachineState) (node : Fin 256)
    (destination : state.getReg .x12=capDestination node) :
    (readBuffer (capFinishPrefix state 7) (16384+32*node.val) 32).setWidth 238=
      (readBuffer state (16384+32*node.val) 32).setWidth 238 := by
  rw [read_buffer_memory_congr _ _ (cap_finish_mask_memory state) (16384+32*node.val) 32,destination]
  exact cap_last_word_mask_node state node

@[irreducible] noncomputable def capLoopObservation (oracle : Oracle) (height : Fin 8) (state : MachineState) :=
  checkEvaluation oracle (recordRows (capParentLoopTrace height state))

theorem cap_hash_observation_eq (oracle : Oracle) (height : Fin 8) (state : MachineState) :
    capHashObservation oracle height state=checkEvaluation oracle (recordRows (capParentTrace height state)) := by
  rw [capHashObservation]

theorem cap_loop_observation_eq (oracle : Oracle) (height : Fin 8) (state : MachineState) :
    capLoopObservation oracle height state=checkEvaluation oracle (recordRows (capParentLoopTrace height state)) := by
  rw [capLoopObservation]

theorem cap_loop_observation_map (oracle : Oracle) (height : Fin 8) (state : MachineState) :
    capLoopObservation oracle height state=
      ((capFinishPrefix (checkerHashReturned .cap (capHashObservation oracle height (capCallPrefix state 6)).1.1) 7,
        (capHashObservation oracle height (capCallPrefix state 6)).1.2),
        (capHashObservation oracle height (capCallPrefix state 6)).2) := by
  have mapped := record_map_evaluation oracle (fun out => capFinishPrefix (checkerHashReturned .cap out) 7)
    (capParentTrace height (capCallPrefix state 6))
  rw [←cap_hash_observation_eq] at mapped
  rw [cap_loop_observation_eq]
  simpa only [capParentLoopTrace,capParentReturnTrace,capReturnTrace,map_eq_bind_pure_comp,
    Function.comp_def,bind_assoc,pure_bind] using mapped

theorem cap_loop_observation_rows (oracle : Oracle) (height : Fin 8) (state : MachineState) :
    (capLoopObservation oracle height state).1.2=
      (capHashObservation oracle height (capCallPrefix state 6)).1.2 :=
  observed_map_rows _ _ (fun out => capFinishPrefix (checkerHashReturned .cap out) 7)
    (cap_loop_observation_map oracle height state)

theorem cap_loop_hash_reached (oracle : Oracle) (height : Fin 8) (state : MachineState) :
    (capHashObservation oracle height (capCallPrefix state 6)).1.1∈
      support (capParentTrace height (capCallPrefix state 6)) := by
  rw [cap_hash_observation_eq]
  exact recorded_evaluation_support oracle _

theorem cap_loop_restored_destination (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384) :
    (checkerHashReturned .cap (capHashObservation oracle height (capCallPrefix state 6)).1.1).getReg .x12=
      capDestination node := by
  have restored := cap_returned_register height node range (capCallPrefix state 6) _
    (cap_call_pc state pc) (cap_call_node node state child) (cap_call_source node state child heap)
    (cap_call_destination node state child heap) (cap_loop_hash_reached oracle height state) ⟨11,by omega⟩
  change (checkerHashReturned .cap _).getReg .x12=(capCallPrefix state 6).getReg .x12 at restored
  exact restored.trans (cap_call_destination node state child heap)

theorem cap_loop_observation_node (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384) :
    (readBuffer (capLoopObservation oracle height state).1.1 (16384+32*node.val) 32).setWidth 238=
      nodeDigest (width (CheckerCap.capHeight height))
        (capRecordedValues oracle height node (capCallPrefix state 6) (calls (CheckerCap.capHeight height)-1)) := by
  have destination := cap_parent_destination height node range (capCallPrefix state 6) _
    (cap_call_pc state pc) (cap_call_node node state child) (cap_call_source node state child heap)
    (cap_call_destination node state child heap) (cap_loop_hash_reached oracle height state)
  rw [cap_loop_observation_map,cap_finish_node _ node
    (cap_loop_restored_destination oracle height node range state pc child heap),
    cap_returned_buffer _ node destination,
    (cap_hash_observation_chain oracle height node range (capCallPrefix state 6)
      (cap_call_pc state pc) (cap_call_node node state child) (cap_call_source node state child heap)).2,
    final_value_node]

theorem cap_call_buffer (state : MachineState) (address : Nat) :
    readBuffer (capCallPrefix state 6) address 32=readBuffer state address 32 := by
  apply read_buffer_memory_congr
  funext query
  exact cap_call_memory state query

theorem cap_call_seed (state : MachineState) (node : Fin 256) :
    capRecordedSeed (capCallPrefix state 6) node=capRecordedSeed state node := by
  simp only [capRecordedSeed,cap_call_buffer]

theorem cap_loop_observation_chain (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384) :
    RecordedChain canonicalEncoding calls (capLoopObservation oracle height state).1.2
      (CheckerCap.capHeight height) (capRecordedSeed state node)
      (capRecordedValues oracle height node (capCallPrefix state 6)) := by
  have chain := (cap_hash_observation_chain oracle height node range (capCallPrefix state 6)
    (cap_call_pc state pc) (cap_call_node node state child) (cap_call_source node state child heap)).1
  rw [←cap_loop_observation_rows,cap_call_seed] at chain
  exact chain

theorem cap_loop_left_recorded_path (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384) :
    RecordedPath canonicalEncoding calls width (capLoopObservation oracle height state).1.2
      (2*node.val) (16+height.val) 1 ((readBuffer state (16384+64*node.val) 32).setWidth 238)
      ((readBuffer (capLoopObservation oracle height state).1.1 (16384+32*node.val) 32).setWidth 238) :=
  recorded_single_step rfl (cap_left_seed_eq state node)
    (cap_loop_observation_chain oracle height node range state pc child heap)
    (cap_loop_observation_node oracle height node range state pc child heap)

theorem cap_loop_right_recorded_path (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384) :
    RecordedPath canonicalEncoding calls width (capLoopObservation oracle height state).1.2
      (2*node.val+1) (16+height.val) 1 ((readBuffer state (16384+64*node.val+32) 32).setWidth 238)
      ((readBuffer (capLoopObservation oracle height state).1.1 (16384+32*node.val) 32).setWidth 238) :=
  recorded_single_step rfl (cap_right_seed_eq state node)
    (cap_loop_observation_chain oracle height node range state pc child heap)
    (cap_loop_observation_node oracle height node range state pc child heap)

theorem cap_returned_frame (state : MachineState) (node : Fin 256)
    (destination : state.getMem (checkerSaveWord CheckerHashSite.cap.resultSlot)=capDestination node)
    (query : Word) (away : ∀ word : Fin 4, query≠capDestination node+BitVec.ofNat 64 (8*word.val)) :
    (checkerHashReturned .cap state).getMem query=state.getMem query := by
  rw [checkerHashReturned]
  change (checkerLoadBackPrefix (checkerResultPrefix .cap state 9) 31).getMem query=_
  rw [checker_load_back_memory _ _ (by decide)]
  exact result_outside_to .cap state 9 (by omega) _ destination query away

theorem cap_prepared_frame (height : Fin 8) (node : Fin 256) (state : MachineState)
    (source : state.getReg .x10=capSource node) (query : Word) (outside : OutsideScratch query)
    (away : ∀ word : Fin 8, query≠capSource node+BitVec.ofNat 64 (8*word.val)) :
    (capPrepared height state).getMem query=state.getMem query := by
  rw [capPrepared,checker_hash_abi_memory]
  change (capScheduled height (capMasked state)).mem query=_
  rw [cap_scheduled_memory]
  change (capMasked state).getMem query=_
  rw [capMasked,child_mask_outside_at .cap _ 9 (by omega) (capSource node)
    ((checker_snapshot_register 31 state (by omega) .x10).trans source) query away]
  apply checker_snapshot_memory_frame 31 state (by omega)
  intro slot same
  have numeric := congrArg BitVec.toNat same
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*slot.val<2^64)] at numeric
  have := outside.lower
  omega

theorem cap_hash_frame (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (state out : MachineState) (pc : state.pc=4096+4*2861)
    (parent : state.getReg .x6=BitVec.ofNat 64 node.val) (source : state.getReg .x10=capSource node)
    (reached : out∈support (capParentTrace height state)) (query : Word) (outside : OutsideScratch query)
    (away : ∀ word : Fin 8, query≠capSource node+BitVec.ofNat 64 (8*word.val)) :
    out.getMem query=state.getMem query :=
  (checker_hash_trace_memory .cap 0 _ out (cap_prepared_ready height node range state pc parent source).args
    reached query outside).trans (cap_prepared_frame height node state source query outside away)

theorem cap_loop_word_frame (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (state out : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384)
    (reached : out∈support (capParentLoopTrace height state)) (query : Word) (outside : OutsideScratch query)
    (sources : ∀ word : Fin 8, query≠capSource node+BitVec.ofNat 64 (8*word.val))
    (destinations : ∀ word : Fin 4, query≠capDestination node+BitVec.ofNat 64 (8*word.val)) :
    out.getMem query=state.getMem query := by
  simp only [capParentLoopTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨returned,first,rfl⟩ := reached
  rw [cap_finish_memory returned 7 (by omega) (capDestination node)
    (cap_parent_return_destination height node range state returned pc child heap first) query
    (by simpa only [show signExtend12 24=BitVec.ofNat 64 (8*3) from rfl] using destinations ⟨3,by decide⟩)]
  have returnedFirst : returned∈support (capReturnTrace height (capCallPrefix state 6)) := first
  simp only [capReturnTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at returnedFirst
  obtain ⟨hashed,hashReached,rfl⟩ := returnedFirst
  have destination := cap_parent_destination height node range (capCallPrefix state 6) hashed
    (cap_call_pc state pc) (cap_call_node node state child) (cap_call_source node state child heap)
    (cap_call_destination node state child heap) hashReached
  rw [cap_returned_frame hashed node destination query destinations]
  exact (cap_hash_frame height node range (capCallPrefix state 6) hashed
    (cap_call_pc state pc) (cap_call_node node state child) (cap_call_source node state child heap)
    hashReached query outside sources).trans (cap_call_memory state query)

theorem cap_heap_word_outside (query : Nat) (small : query<512) (word : Fin 4) :
    OutsideScratch (BitVec.ofNat 64 (16384+32*query+8*word.val)) := by
  have numeric : (BitVec.ofNat 64 (16384+32*query+8*word.val)).toNat=16384+32*query+8*word.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_,?_,?_⟩
  all_goals rw [numeric]
  all_goals omega

theorem cap_loop_heap_word_frame (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (state out : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384)
    (reached : out∈support (capParentLoopTrace height state)) (query : Nat) (small : query<512)
    (parentApart : query≠node.val) (leftApart : query≠2*node.val) (rightApart : query≠2*node.val+1)
    (word : Fin 4) :
    out.getMem (BitVec.ofNat 64 (16384+32*query+8*word.val))=
      state.getMem (BitVec.ofNat 64 (16384+32*query+8*word.val)) := by
  apply cap_loop_word_frame height node range state out pc child heap reached _ (cap_heap_word_outside query small word)
  · intro sourceWord
    rw [capSource,←BitVec.ofNat_add]
    exact word_of_nat_ne (16384+32*query+8*word.val) (16384+64*node.val+8*sourceWord.val)
      (by omega) (by omega) (by omega)
  · intro destinationWord
    rw [capDestination,←BitVec.ofNat_add]
    exact word_of_nat_ne (16384+32*query+8*word.val) (16384+32*node.val+8*destinationWord.val)
      (by omega) (by omega) (by omega)

theorem cap_loop_heap_buffer_frame (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (state out : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384)
    (reached : out∈support (capParentLoopTrace height state)) (query : Nat) (small : query<512)
    (parentApart : query≠node.val) (leftApart : query≠2*node.val) (rightApart : query≠2*node.val+1) :
    readBuffer out (16384+32*query) 32=readBuffer state (16384+32*query) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  exact cap_loop_heap_word_frame height node range state out pc child heap reached query small
    parentApart leftApart rightApart ⟨word,inside⟩

open CheckerCap.Visit

theorem cap_frontier_heap_word_frame (state : MachineState) (node pointer : Nat)
    (ready : FrontierReady state node pointer) (fits : ¬state.getReg .x22<state.getReg .x21+30#64)
    (query : Nat) (small : query<512) (apart : query≠node) (word : Fin 4) :
    (frontierRead state).getMem (BitVec.ofNat 64 (16384+32*query+8*word.val))=
      state.getMem (BitVec.ofNat 64 (16384+32*query+8*word.val)) := by
  have frame := actualFrontier.frame state node pointer ready fits (2048+4*query+word.val) (by omega) (by omega)
  have address : wordAddress (2048+4*query+word.val)=BitVec.ofNat 64 (16384+32*query+8*word.val) := by
    unfold wordAddress
    congr 1
    omega
  change (frontierRead state).getMem (wordAddress (2048+4*query+word.val))=
    state.getMem (wordAddress (2048+4*query+word.val)) at frame
  simpa only [address] using frame

theorem cap_frontier_heap_buffer_frame (state : MachineState) (node pointer : Nat)
    (ready : FrontierReady state node pointer) (fits : ¬state.getReg .x22<state.getReg .x21+30#64)
    (query : Nat) (small : query<512) (apart : query≠node) :
    readBuffer (frontierRead state) (16384+32*query) 32=readBuffer state (16384+32*query) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  exact cap_frontier_heap_word_frame state node pointer ready fits query small apart ⟨word,inside⟩

theorem recorded_path_append {enc : Encoding} {schedule widths : Height → Nat} {rows : List PublicRow}
    {node level count more : Nat} {child middle root : Node}
    (first : RecordedPath enc schedule widths rows node level count child middle)
    (later : RecordedPath enc schedule widths rows (node/2^count) (level+count) more middle root) :
    RecordedPath enc schedule widths rows node level (count+more) child root := by
  induction count generalizing node level child with
  | zero =>
    cases first
    simpa only [Nat.pow_zero,Nat.div_one,Nat.add_zero,Nat.zero_add] using later
  | succ count ih =>
    cases first with
    | step atHeight chain tail =>
      rw [show count+1+more=(count+more)+1 by omega]
      apply RecordedPath.step atHeight chain
      apply ih tail
      have index : (node/2)/2^count=node/2^(count+1) := by
        rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm 2]
      simpa only [index,show level+1+count=level+(count+1) by omega] using later

end CommitGolfCandidate.Chained.Native.Refinement
