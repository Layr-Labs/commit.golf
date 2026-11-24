import CommitGolfCandidate.ChainedCheckerCapFrontier
import CommitGolfCandidate.TwoPermutationPackedCapBytes
import CommitGolfCandidate.TwoPermutationCheckerCapHash
import CommitGolfCandidate.TwoPermutationPackedCopy
import RiscvZkvm.Rv64.Logic.ByteOps
import CommitGolfCandidate.TwoPermutationPackedCapVisit

section

/-! Delivered cap entry, root/parity decisions and right-sibling advance. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap.Visit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker ProjectedHalfword
open TwoPermutationPrototype.Checker (capRootAt)

set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage
attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

private theorem merged_ChainedCheckerCapAdvance_cap_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index<3012) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (opcode : chainedCheckerOps.getD index .EBREAK=instruction) :
    fetch chainedCheckerImage state=some (.base instruction) := by
  have location : state.pc=4096+BitVec.ofNat 64 (4*index) := by
    change state.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index)
    rwa [←BitVec.ofNat_add]
  simpa only [opcode] using chained_checker_ops_at index
    (by rw [chained_checker_ops_length]; exact bounded) state location

@[local simp] private theorem merged_ChainedCheckerCapAdvance_pc_after (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
@[local simp] private theorem merged_ChainedCheckerCapAdvance_reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def blockPrefix (code : List Instr) (state : MachineState) (count : Nat) : MachineState :=
  (code.take count).foldl execInstrBr state

def capRootTestCode : List Instr := [.ADDI .x7 .x0 1, .BEQ .x6 .x7 52]

def capRootTest (state : MachineState) := blockPrefix capRootTestCode state 2

theorem execute_cap_root_test (state : MachineState) (pc : state.pc = (4096+4*2704)) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (2+fuel) state coins =
      (do let next ← execute chainedCheckerImage fuel (capRootTest state) coins
          return next.charge 2 0) := by
  apply execute_unit_steps (states := blockPrefix capRootTestCode state)
  intro i inside
  refine ⟨.base (capRootTestCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply merged_ChainedCheckerCapAdvance_cap_fetch _ (2704+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, capRootTestCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def capParityTestCode : List Instr := [.ANDI .x7 .x6 1, .BEQ .x7 .x0 36]

def capParityTest (state : MachineState) := blockPrefix capParityTestCode state 2

theorem execute_cap_parity_test (state : MachineState) (pc : state.pc = (4096+4*2706)) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (2+fuel) state coins =
      (do let next ← execute chainedCheckerImage fuel (capParityTest state) coins
          return next.charge 2 0) := by
  apply execute_unit_steps (states := blockPrefix capParityTestCode state)
  intro i inside
  refine ⟨.base (capParityTestCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply merged_ChainedCheckerCapAdvance_cap_fetch _ (2706+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, capParityTestCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def capRightCode : List Instr := [.ADDI .x6 .x6 1, .JAL .x0 2096928]

def capRight (state : MachineState) := blockPrefix capRightCode state 2

theorem execute_cap_right (state : MachineState) (pc : state.pc = (4096+4*2716)) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (2+fuel) state coins =
      (do let next ← execute chainedCheckerImage fuel (capRight state) coins
          return next.charge 2 0) := by
  apply execute_unit_steps (states := blockPrefix capRightCode state)
  intro i inside
  refine ⟨.base (capRightCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply merged_ChainedCheckerCapAdvance_cap_fetch _ (2716+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, capRightCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def capStartCode : List Instr := [.ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x6 .x0 1]

def capStart (state : MachineState) := blockPrefix capStartCode state 3

theorem execute_cap_start (state : MachineState) (pc : state.pc = (4096+4*2658)) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (3+fuel) state coins =
      (do let next ← execute chainedCheckerImage fuel (capStart state) coins
          return next.charge 3 0) := by
  apply execute_unit_steps (states := blockPrefix capStartCode state)
  intro i inside
  refine ⟨.base (capStartCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply merged_ChainedCheckerCapAdvance_cap_fetch _ (2658+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, capStartCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_root_post (state : MachineState) (pc : state.pc = (4096+4*2704)) :
    (capRootTest state).pc = if state.getReg .x6 = 1#64 then (4096+4*2718) else (4096+4*2706) := by
  by_cases root : state.getReg .x6 = 1#64 <;>
    simp [capRootTest, blockPrefix, capRootTestCode, execInstrBr, signExtend12, signExtend13, pc, root]

theorem cap_parity_post (state : MachineState) (pc : state.pc = (4096+4*2706)) :
    (capParityTest state).pc = if state.getReg .x6 &&& 1#64 = 0#64 then (4096+4*2716) else (4096+4*2708) := by
  by_cases parity : state.getReg .x6 &&& 1#64 = 0#64 <;>
    simp [capParityTest, blockPrefix, capParityTestCode, execInstrBr, signExtend12, signExtend13, pc, parity]

theorem cap_right_post (state : MachineState) (pc : state.pc = (4096+4*2716)) :
    let next := capRight state
    next.pc = (4096+4*2661) ∧ next.getReg .x6 = state.getReg .x6+1#64 ∧ next.mem = state.mem := by
  simp [capRight, blockPrefix, capRightCode, execInstrBr, signExtend12, signExtend21, pc]
  <;> rfl

theorem cap_parent_loop_node (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2708)
    (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : s.getReg .x25=16384#64)
    (reached : out∈support (capParentLoopTrace height s)) :
    out.getReg .x6=BitVec.ofNat 64 node.val := by
  simp only [capParentLoopTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨returned,first,rfl⟩ := reached
  rw [cap_finish_register returned 7 (by omega) .x6 (by decide)]
  have restored := cap_return_register height node range _ returned (cap_call_pc s pc)
    (cap_call_node node s child) (cap_call_source node s child heap)
    (cap_call_destination node s child heap) first ⟨5,by omega⟩
  change returned.getReg .x6=(capCallPrefix s 6).getReg .x6 at restored
  exact restored.trans (cap_call_node node s child)

theorem cap_parent_loop_fixed (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2708)
    (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : s.getReg .x25=16384#64)
    (reached : out∈support (capParentLoopTrace height s)) (slot : Fin 31)
    (link : checkerSnapshotReg slot≠.x1) (coordinate : checkerSnapshotReg slot≠.x6)
    (source : checkerSnapshotReg slot≠.x10) (destination : checkerSnapshotReg slot≠.x12)
    (temp : checkerSnapshotReg slot≠.x31) :
    out.getReg (checkerSnapshotReg slot)=s.getReg (checkerSnapshotReg slot) := by
  simp only [capParentLoopTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨returned,first,rfl⟩ := reached
  rw [cap_finish_register returned 7 (by omega) _ temp]
  exact (cap_return_register height node range _ returned (cap_call_pc s pc)
    (cap_call_node node s child) (cap_call_source node s child heap)
    (cap_call_destination node s child heap) first slot).trans
      (cap_call_register s _ link coordinate source destination)

end CommitGolfCandidate.Chained.Native.CheckerCap.Visit

end

section

/-! The cap wrapper preserves aligned words outside scratch and the cap heap. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage

structure OutsideCap (query : Word) extends OutsideScratch query : Prop where
  region : query.toNat<16384 ∨ 32768≤query.toNat

theorem OutsideCap.source (query : Word) (outside : OutsideCap query) (node : Fin 256) (word : Fin 8) :
    query≠capSource node+BitVec.ofNat 64 (8*word.val) := by
  intro same
  have numeric := congrArg BitVec.toNat same
  rw [cap_source_word,wordAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*(2048+8*node.val+word.val)<2^64)] at numeric
  have := outside.region
  omega

theorem OutsideCap.destination (query : Word) (outside : OutsideCap query) (node : Fin 256) (word : Fin 4) :
    query≠capDestination node+BitVec.ofNat 64 (8*word.val) := by
  intro same
  have numeric := congrArg BitVec.toNat same
  rw [cap_destination_word,wordAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*(2048+4*node.val+word.val)<2^64)] at numeric
  have := outside.region
  omega

theorem child_mask_outside_at (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9)
    (address : Word) (pair : s.getReg site.childReg=address) (query : Word)
    (away : ∀ word : Fin 8, query≠address+BitVec.ofNat 64 (8*word.val)) :
    (checkerChildMaskPrefix site s n).getMem query=s.getMem query := by
  have succ (i : Nat) (inside : i<9) : checkerChildMaskPrefix site s (i+1)=
      execInstrBr (checkerChildMaskPrefix site s i) ((checkerChildMaskOps site).getD i .EBREAK) := by
    cases site <;> interval_cases i <;> rw [checkerChildMaskPrefix,checkerChildMaskPrefix] <;> rfl
  have step (t : MachineState) (i : Fin 9) (source : t.getReg .x14=address) :
      (execInstrBr t ((checkerChildMaskOps site).getD i.val .EBREAK)).getMem query=t.getMem query := by
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

theorem cap_prepared_memory (height : Fin 8) (node : Fin 256) (s : MachineState)
    (source : s.getReg .x10=capSource node) (query : Word) (outside : OutsideCap query) :
    (capPrepared height s).getMem query=s.getMem query := by
  rw [capPrepared,checker_hash_abi_memory]
  change (capScheduled height (capMasked s)).mem query=_
  rw [cap_scheduled_memory]
  change (capMasked s).getMem query=_
  rw [capMasked,child_mask_outside_at .cap _ 9 (by omega) (capSource node)
    ((checker_snapshot_register 31 s (by omega) .x10).trans source) query (outside.source query node)]
  apply checker_snapshot_memory_frame 31 s (by omega)
  intro slot same
  have numeric := congrArg BitVec.toNat same
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*slot.val<2^64)] at numeric
  have := outside.lower
  omega

theorem cap_parent_memory (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (reached : out∈support (capParentTrace height s))
    (query : Word) (outside : OutsideCap query) : out.getMem query=s.getMem query := by
  exact (RecordLeaf.checker_hash_trace_memory .cap 0 _ out (cap_prepared_ready height node range s pc parent source).args
    reached query outside.toOutsideScratch).trans (cap_prepared_memory height node s source query outside)

theorem cap_return_memory (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2861) (parent : s.getReg .x6=BitVec.ofNat 64 node.val)
    (source : s.getReg .x10=capSource node) (destination : s.getReg .x12=capDestination node)
    (reached : out∈support (capReturnTrace height s)) (query : Word) (outside : OutsideCap query) :
    out.getMem query=s.getMem query := by
  simp only [capReturnTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,first,rfl⟩ := reached
  rw [checkerHashReturned]
  change (checkerLoadBackPrefix (checkerResultPrefix .cap hashed 9) 31).getMem query=_
  rw [checker_load_back_memory _ _ (by omega)]
  exact (result_outside_to .cap hashed 9 (by omega) (capDestination node)
    (cap_parent_destination height node range s hashed pc parent source destination first)
    query (outside.destination query node)).trans
      (cap_parent_memory height node range s hashed pc parent source first query outside)

theorem cap_finish_memory (s : MachineState) (n : Nat) (small : n≤7) (address : Word)
    (destination : s.getReg .x12=address) (query : Word) (away : query≠address+signExtend12 24) :
    (capFinishPrefix s n).getMem query=s.getMem query := by
  have jump_memory (t : MachineState) (offset : BitVec 21) :
      (execInstrBr t (.JAL .x0 offset)).getMem query=t.getMem query := by
    change ((t.setReg .x0 (t.pc+4#64)).setPC (t.pc+signExtend21 offset)).getMem query=_
    rfl
  have step (t : MachineState) (i : Fin 7) (source : t.getReg .x12=address) :
      (execInstrBr t (capFinishOps.getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i
    case «0» => exact jump_memory t 128
    case «1» => rfl
    case «2» => rfl
    case «3» => rfl
    case «4» =>
      apply word_store_frame
      rw [source]
      exact away
    case «5» => exact jump_memory t 2097012
    case «6» => exact jump_memory t 2097108
  induction n with
  | zero => rw [cap_finish_zero]
  | succ n ih =>
    rw [cap_finish_succ,step _ ⟨n,by omega⟩
      ((cap_finish_register s n (by omega) .x12 (by decide)).trans destination),ih (by omega)]

theorem cap_parent_loop_memory (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2708)
    (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : s.getReg .x25=16384#64)
    (reached : out∈support (capParentLoopTrace height s)) (query : Word) (outside : OutsideCap query) :
    out.getMem query=s.getMem query := by
  simp only [capParentLoopTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨returned,first,rfl⟩ := reached
  rw [cap_finish_memory returned 7 (by omega) (capDestination node)
    (cap_parent_return_destination height node range s returned pc child heap first) query]
  · exact (cap_return_memory height node range _ returned (cap_call_pc s pc)
      (cap_call_node node s child) (cap_call_source node s child heap)
      (cap_call_destination node s child heap) first query outside).trans (cap_call_memory s query)
  · exact outside.destination query node ⟨3,by omega⟩

end CommitGolfCandidate.Chained.Native.CheckerCap

end

section

/-! Typed cap position and mark invariants for the delivered parent transition. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap.Visit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage

theorem cap_parent_loop_stable (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2708)
    (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : s.getReg .x25=16384#64)
    (reached : out∈support (capParentLoopTrace height s)) : CapStable s out := by
  have keep := cap_parent_loop_fixed height node range s out pc child heap reached
  intro reg found
  simp [capFixedRegisters] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact keep ⟨4,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact keep ⟨8,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact keep ⟨10,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact keep ⟨12,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact keep ⟨21,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact keep ⟨24,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact keep ⟨25,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact keep ⟨26,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem cap_mark_outside (word : Nat) (low : 513≤word) (high : word<1024) :
    OutsideCap (wordAddress word) := by
  have numeric : (wordAddress word).toNat=8*word := by
    simp only [wordAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*word<2^64)]
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · rw [numeric]; omega
  · rw [numeric]; omega
  · rw [numeric]; omega
  · left; rw [numeric]; omega

theorem cap_parent_position {groups : List Nat} {pointer : Nat}
    (height : Fin 8) (node : Fin 256) (span : TwoPermutationPrototype.Opening.CapSpan node.val (height.val+1))
    (s out : MachineState) (position : CapPosition groups s (2*node.val+1) pointer)
    (pc : s.pc=4096+4*2708) (reached : out∈support (capParentLoopTrace height s)) :
    CapPosition groups out node.val pointer := by
  have range := cap_range_from_span height node span
  have heap := position.context.controls.roots
  have child := position.heap
  have stable := cap_parent_loop_stable height node range s out pc child heap reached
  refine ⟨position.context.transport stable ?_,
    cap_parent_loop_node height node range s out pc child heap reached,?_,position.above,position.even⟩
  · intro word low high
    exact cap_parent_loop_memory height node range s out pc child heap reached
      (wordAddress word) (cap_mark_outside word low high)
  · have cursor := cap_parent_loop_fixed height node range s out pc child heap reached
      ⟨20,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    change out.getReg .x21=s.getReg .x21 at cursor
    exact cursor.trans position.proof

theorem cap_lookup_stable (state : MachineState) : CapStable state (capLookup state) := by
  intro reg found
  simp [capFixedRegisters] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact cap_lookup_register state _ (by decide) (by decide) (by decide)

theorem cap_frontier_position {groups : List Nat} {state : MachineState} {node pointer : Nat}
    (position : CapPosition groups state node pointer) (ready : FrontierReady state node pointer)
    (fits : ¬ state.getReg .x22<state.getReg .x21+30#64) :
    CapPosition groups (frontierRead state) node (pointer+30) := by
  have stable : CapStable state (frontierRead state) := by
    intro reg found
    simp [capFixedRegisters] at found
    rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact actualFrontier.register state _ (by decide) (by decide) (by decide) (by decide)
  refine ⟨position.context.transport stable ?_,?_,?_,by have := position.above; omega,
    by have := position.even; omega⟩
  · intro word low high
    exact actualFrontier.frame state node pointer ready fits word (by omega) (Or.inl (by omega))
  · exact (actualFrontier.register state .x6 (by decide) (by decide) (by decide) (by decide)).trans position.heap
  · exact (actualFrontier.pointer state node pointer ready).2

theorem cap_lookup_position {groups : List Nat} {state : MachineState} {node height proof : Nat}
    (position : CapPosition groups state node proof) (span : TwoPermutationPrototype.Opening.CapSpan node height) :
    let next := capLookup state
    let marked := capIsMarked groups node height
    next.pc = (if marked then if height = 0 then (4096+4*2704) else (4096+4*2661) else (4096+4*2668)) ∧
    CapPosition groups next (if marked && height != 0 then 2*node else node) proof ∧ next.mem = state.mem := by
  obtain ⟨pc, heap, mem⟩ := cap_lookup_post state
  dsimp only at pc heap mem ⊢
  have proofReg : (capLookup state).getReg .x21 = BitVec.ofNat 64 proof :=
    (cap_lookup_register state .x21 (by decide) (by decide) (by decide)).trans position.proof
  have ctxt := position.context.transport (cap_lookup_stable state) (fun _ _ _ => congrFun mem _)
  have marked := cap_lookup_is_marked position span
  change capMarkedWord state=0#64 ↔ capIsMarked groups node height=false at marked
  have leaf := cap_lookup_leaf_iff state node (TwoPermutationPrototype.Opening.cap_span_node node height span).2
    position.context.controls position.heap
  constructor
  · rw [pc]
    simp only [marked, leaf]
    cases height with
    | zero =>
      have valid := TwoPermutationPrototype.Opening.cap_span_is_leaf node span
      cases capIsMarked groups node 0 <;> simp [valid]
    | succ height =>
      have internal := TwoPermutationPrototype.Opening.cap_span_is_internal node height span
      cases capIsMarked groups node (height+1) <;> simp [Nat.not_le_of_gt internal]
  · refine ⟨⟨ctxt, ?_, proofReg, position.above, position.even⟩, mem⟩
    have leaf' := leaf
    rw [position.heap] at leaf'
    rw [heap, position.heap]
    simp only [marked, leaf']
    cases height with
    | zero =>
      have valid := TwoPermutationPrototype.Opening.cap_span_is_leaf node span
      cases capIsMarked groups node 0 <;> simp [valid]
    | succ height =>
      have internal := TwoPermutationPrototype.Opening.cap_span_is_internal node height span
      have shift := cap_lookup_left_word state node position.heap
      rw [position.heap] at shift
      cases capIsMarked groups node (height+1) <;> simp [Nat.not_le_of_gt internal, shift]

attribute [local simp] MachineState.getReg_setPC TwoPermutationPrototype.Opening.getReg_setReg

theorem root_test_register (state : MachineState) (r : Reg) (stable : r ≠ .x7) :
    (capRootTest state).getReg r = state.getReg r := by
  by_cases atRoot : state.getReg .x6 = 1#64 <;>
    simp [capRootTest, blockPrefix, capRootTestCode, execInstrBr, signExtend12,
      show state.getReg .x0 = 0#64 from rfl, atRoot, Ne.symm stable]

private theorem merged_ChainedCheckerCapPosition_parity_test_register (state : MachineState) (r : Reg) (stable : r ≠ .x7) :
    (capParityTest state).getReg r = state.getReg r := by
  by_cases even : state.getReg .x6 &&& 1#64 = 0#64 <;>
    simp [capParityTest, blockPrefix, capParityTestCode, execInstrBr, signExtend12,
      show state.getReg .x0 = 0#64 from rfl, even, Ne.symm stable]

private theorem merged_ChainedCheckerCapPosition_odd_word_eq {node : Nat} (bound : node < 2^64) :
    (BitVec.ofNat 64 node &&& 1#64 = 0#64) ↔ node%2 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  change (node &&& 1 = 0) ↔ _
  rw [Nat.and_one_is_mod]

def capAfterTests (state : MachineState) : MachineState := capParityTest (capRootTest state)

theorem cap_after_tests (state : MachineState) (node : Nat) (bound : 2 ≤ node ∧ node < 512)
    (pc : state.pc = (4096+4*2704)) (heap : state.getReg .x6 = BitVec.ofNat 64 node) :
    let next := capAfterTests state
    next.pc = (if node%2 = 0 then (4096+4*2716) else (4096+4*2708)) ∧ next.getReg .x6 = BitVec.ofNat 64 node := by
  have nRoot : state.getReg .x6 ≠ 1#64 := by
    intro h
    have equal := congrArg BitVec.toNat (heap.symm.trans h)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at equal
    change node = 1 at equal
    omega
  have start : (capRootTest state).pc = (4096+4*2706) := by rw [cap_root_post state pc, ite_eq_right nRoot]
  have before : (capRootTest state).getReg .x6 = BitVec.ofNat 64 node :=
    (root_test_register state .x6 (by decide)).trans heap
  refine ⟨?_, (merged_ChainedCheckerCapPosition_parity_test_register _ .x6 (by decide)).trans before⟩
  unfold capAfterTests
  rw [cap_parity_post _ start, before]
  simp only [merged_ChainedCheckerCapPosition_odd_word_eq (by omega : node < 2^64)]

theorem cap_tests_execution (state : MachineState) (node : Nat) (bound : 2≤node ∧ node<512)
    (pc : state.pc=4096+4*2704) (heap : state.getReg .x6=BitVec.ofNat 64 node)
    (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (4+fuel) state coins=
      (do let result ← execute chainedCheckerImage fuel (capAfterTests state) coins
          return result.charge 4 0) := by
  have nRoot : state.getReg .x6≠1#64 := by
    intro hit
    have equal := congrArg BitVec.toNat (heap.symm.trans hit)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at equal
    change node=1 at equal
    omega
  have middle : (capRootTest state).pc=4096+4*2706 := by
    rw [cap_root_post state pc,ite_eq_right nRoot]
  rw [show 4+fuel=2+(2+fuel) by omega,execute_cap_root_test state pc (2+fuel) coins,
    execute_cap_parity_test _ middle fuel coins]
  simp [capAfterTests,Execution.charge,←Nat.add_assoc]

theorem cap_tests_stable (state : MachineState) : CapStable state (capAfterTests state) :=
  TwoPermutationPrototype.Packed.Checker.cap_tests_stable state
theorem cap_tests_cursor (state : MachineState) : (capAfterTests state).getReg .x21=state.getReg .x21 :=
  TwoPermutationPrototype.Packed.Checker.cap_tests_cursor state
theorem cap_tests_memory (state : MachineState) : (capAfterTests state).mem=state.mem :=
  TwoPermutationPrototype.Packed.Checker.cap_tests_memory state
theorem cap_right_register (state : MachineState) (reg : Reg) (node : reg≠.x6) :
    (capRight state).getReg reg=state.getReg reg :=
  TwoPermutationPrototype.Packed.Checker.cap_right_register state reg node
theorem cap_right_stable (state : MachineState) : CapStable state (capRight state) :=
  TwoPermutationPrototype.Packed.Checker.cap_right_stable state

theorem cap_sibling_position {groups : List Nat} {state : MachineState} {node pointer : Nat}
    (position : CapPosition groups state (2*node) pointer) (pc : state.pc=4096+4*2704)
    (bound : 0<node ∧ 2*node<512) :
    (capRight (capAfterTests state)).pc=4096+4*2661 ∧
      CapPosition groups (capRight (capAfterTests state)) (2*node+1) pointer ∧
      (capRight (capAfterTests state)).mem=state.mem := by
  obtain ⟨after,heap⟩ := cap_after_tests state (2*node) (by omega) pc position.heap
  have nextPC : (capAfterTests state).pc=4096+4*2716 := by rw [after,ite_eq_left (by omega)]
  have post := cap_right_post _ nextPC
  have stable := (cap_tests_stable state).trans (cap_right_stable (capAfterTests state))
  have mem := post.2.2.trans (cap_tests_memory state)
  refine ⟨post.1,⟨position.context.transport stable (fun _ _ _ => congrFun mem _),?_,?_,
    position.above,position.even⟩,mem⟩
  · rw [post.2.1,heap,BitVec.ofNat_add]
  · exact (cap_right_register _ .x21 (by decide)).trans ((cap_tests_cursor state).trans position.proof)

theorem cap_sibling_execution (state : MachineState) (node : Nat) (bound : 0<node ∧ 2*node<512)
    (pc : state.pc=4096+4*2704) (heap : state.getReg .x6=BitVec.ofNat 64 (2*node))
    (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (6+fuel) state coins=
      (do let result ← execute chainedCheckerImage fuel (capRight (capAfterTests state)) coins
          return result.charge 6 0) := by
  have middle : (capAfterTests state).pc=4096+4*2716 := by
    rw [(cap_after_tests state (2*node) (by omega) pc heap).1,ite_eq_left (by omega)]
  rw [show 6+fuel=4+(2+fuel) by omega,cap_tests_execution state (2*node) (by omega) pc heap (2+fuel) coins,
    execute_cap_right _ middle fuel coins]
  simp [Execution.charge,←Nat.add_assoc]

theorem cap_ascend_ready {groups : List Nat} {pointer : Nat}
    (height : Fin 8) (node : Fin 256) (span : TwoPermutationPrototype.Opening.CapSpan node.val (height.val+1))
    (state : MachineState) (position : CapPosition groups state (2*node.val+1) pointer)
    (pc : state.pc=4096+4*2704) :
    (capAfterTests state).pc=4096+4*2708 ∧
      CapPosition groups (capAfterTests state) (2*node.val+1) pointer := by
  have positive := (TwoPermutationPrototype.Opening.cap_span_node node.val (height.val+1) span).1
  obtain ⟨target,heap⟩ := cap_after_tests state (2*node.val+1) (by omega) pc position.heap
  refine ⟨?_,⟨position.context.transport (cap_tests_stable state)
    (fun _ _ _ => congrFun (cap_tests_memory state) _),heap,
    (cap_tests_cursor state).trans position.proof,position.above,position.even⟩⟩
  rw [target,ite_eq_right (by omega)]

theorem cap_ascend_execution {groups : List Nat} {pointer : Nat}
    (height : Fin 8) (node : Fin 256) (span : TwoPermutationPrototype.Opening.CapSpan node.val (height.val+1))
    (state : MachineState) (position : CapPosition groups state (2*node.val+1) pointer)
    (pc : state.pc=4096+4*2704) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (149+4*capDepth height+fuel) state coins=
      (do let out ← capParentLoopTrace height (capAfterTests state)
          let result ← execute chainedCheckerImage fuel out coins
          return result.charge (156+4*capDepth height) 1) := by
  have ready := cap_ascend_ready height node span state position pc
  have positive := (TwoPermutationPrototype.Opening.cap_span_node node.val (height.val+1) span).1
  have parent := cap_parent_loop_execution height node (cap_range_from_span height node span)
    (capAfterTests state) ready.1 ready.2.heap ready.2.context.controls.roots fuel coins
  rw [checking_manifest_image] at parent
  rw [show 149+4*capDepth height+fuel=4+(145+4*capDepth height+fuel) by omega,
    cap_tests_execution state (2*node.val+1) (by omega) pc position.heap _ coins,parent]
  simp [Execution.charge,←Nat.add_assoc]

theorem cap_lookup_cost {groups : List Nat} {state : MachineState} {node height pointer : Nat}
    (position : CapPosition groups state node pointer) (span : TwoPermutationPrototype.Opening.CapSpan node height) :
    capLookupSteps state=(if capIsMarked groups node height then if height=0 then 5 else 7 else 4) := by
  have marked := cap_lookup_is_marked position span
  change capMarkedWord state=0#64 ↔ capIsMarked groups node height=false at marked
  have leaf := cap_lookup_leaf_iff state node (TwoPermutationPrototype.Opening.cap_span_node node height span).2
    position.context.controls position.heap
  simp only [capLookupSteps,marked,leaf]
  cases height with
  | zero =>
    have valid := TwoPermutationPrototype.Opening.cap_span_is_leaf node span
    cases capIsMarked groups node 0 <;> simp [valid]
  | succ height =>
    have internal := TwoPermutationPrototype.Opening.cap_span_is_internal node height span
    cases capIsMarked groups node (height+1) <;> simp [Nat.not_le_of_gt internal]

theorem cap_frontier_stable (state : MachineState) : CapStable state (frontierRead state) := by
  intro reg found
  simp [capFixedRegisters] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact actualFrontier.register state _ (by decide) (by decide) (by decide) (by decide)

theorem cap_frontier_memory (state : MachineState) (node pointer : Nat) (ready : FrontierReady state node pointer)
    (fits : ¬state.getReg .x22<state.getReg .x21+30#64) (query : Word) (outside : OutsideCap query) :
    (frontierRead state).getMem query=state.getMem query := by
  let word := query.toNat/8
  have room := outside.room
  have address : wordAddress word=query := by
    apply BitVec.eq_of_toNat_eq
    rw [wordAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [word]; omega)]
    dsimp [word]
    have := outside.aligned
    omega
  have away : word<2048+4*node ∨ 2048+4*node+4≤word := by
    rcases outside.region with low | high
    · left; dsimp [word]; omega
    · right; dsimp [word]; have := ready.below; omega
  have frame := actualFrontier.frame state node pointer ready fits word (by dsimp [word]; omega) away
  change (frontierRead state).getMem (wordAddress word)=state.getMem (wordAddress word) at frame
  rwa [address] at frame

theorem cap_ascend_position {groups : List Nat} {pointer : Nat}
    (height : Fin 8) (node : Fin 256) (span : TwoPermutationPrototype.Opening.CapSpan node.val (height.val+1))
    (state out : MachineState) (position : CapPosition groups state (2*node.val+1) pointer)
    (pc : state.pc=4096+4*2704) (reached : out∈support (capParentLoopTrace height (capAfterTests state))) :
    out.pc=4096+4*2704 ∧ CapPosition groups out node.val pointer ∧ CapStable state out ∧
      ∀ query, OutsideCap query → out.getMem query=state.getMem query := by
  have ready := cap_ascend_ready height node span state position pc
  have range := cap_range_from_span height node span
  have ctx := ready.2.context.controls
  refine ⟨cap_parent_loop_pc height node range _ out ready.1 ready.2.heap ctx.roots reached,
    cap_parent_position height node span _ out ready.2 ready.1 reached,
    (cap_tests_stable state).trans (cap_parent_loop_stable height node range _ out ready.1 ready.2.heap ctx.roots reached),?_⟩
  intro query outside
  exact (cap_parent_loop_memory height node range _ out ready.1 ready.2.heap ctx.roots reached query outside).trans
    (congrFun (cap_tests_memory state) query)

end CommitGolfCandidate.Chained.Native.CheckerCap.Visit

end
