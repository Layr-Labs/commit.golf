import CommitGolfCandidate.ChainedCheckerCapReturn

section

/-! Delivered right-child return, parent heap pointers and cap wrapper call. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage
attribute [local simp] MachineState.getReg_setPC MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne
@[local simp] private theorem merged_ChainedCheckerCapParent_call_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl

def capCallOps : List Instr := [.SRLI .x6 .x6 1,.SLLI .x10 .x6 6,
  .ADD .x10 .x25 .x10,.SLLI .x12 .x6 5,.ADD .x12 .x25 .x12,.JAL .x1 592]
@[irreducible] def capCallPrefix (s : MachineState) (n : Nat) : MachineState :=
  (capCallOps.take n).foldl execInstrBr s
theorem cap_call_at : OpsAt chainedCheckerImage (4096+4*2708) capCallOps :=
  chained_checker_slice_at 2708 6 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem cap_call_zero (s : MachineState) : capCallPrefix s 0=s := by rw [capCallPrefix]; rfl
theorem cap_call_succ (s : MachineState) (n : Nat) (small : n<6) :
    capCallPrefix s (n+1)=execInstrBr (capCallPrefix s n) (capCallOps.getD n .EBREAK) := by
  interval_cases n <;> rw [capCallPrefix,capCallPrefix] <;> rfl

theorem cap_call_prefix_pc (s : MachineState) (n : Nat) (small : n≤5) :
    (capCallPrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;> simp [capCallPrefix,capCallOps,execInstrBr,BitVec.add_assoc]
theorem cap_call_pc (s : MachineState) (pc : s.pc=4096+4*2708) :
    (capCallPrefix s 6).pc=4096+4*2861 := by
  simp [capCallPrefix,capCallOps,execInstrBr,pc]
  decide +kernel
theorem cap_call_link (s : MachineState) (pc : s.pc=4096+4*2708) :
    (capCallPrefix s 6).getReg .x1=4096+4*2714 := by
  simp [capCallPrefix,capCallOps,execInstrBr,pc,MachineState.getReg_setPC,MachineState.getReg_setReg_eq]
theorem cap_call_register (s : MachineState) (reg : Reg) (link : reg≠.x1)
    (node : reg≠.x6) (source : reg≠.x10) (target : reg≠.x12) :
    (capCallPrefix s 6).getReg reg=s.getReg reg := by
  rw [capCallPrefix]
  cases reg <;> first | contradiction | rfl
theorem cap_call_memory (s : MachineState) (query : Word) :
    (capCallPrefix s 6).getMem query=s.getMem query := by rw [capCallPrefix]; rfl
theorem cap_call_node_value (s : MachineState) :
    (capCallPrefix s 6).getReg .x6=s.getReg .x6 >>> 1 := by rw [capCallPrefix]; rfl
theorem cap_call_source_value (s : MachineState) :
    (capCallPrefix s 6).getReg .x10=s.getReg .x25+((s.getReg .x6 >>> 1) <<< 6) := by rw [capCallPrefix]; rfl
theorem cap_call_destination_value (s : MachineState) :
    (capCallPrefix s 6).getReg .x12=s.getReg .x25+((s.getReg .x6 >>> 1) <<< 5) := by rw [capCallPrefix]; rfl

theorem cap_odd_half (node : Fin 256) :
    BitVec.ofNat 64 (2*node.val+1) >>> 1=BitVec.ofNat 64 node.val := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : 2*node.val+1<2^64),Nat.mod_eq_of_lt (by omega : node.val<2^64)]
  omega
theorem cap_range_from_span (height : Fin 8) (node : Fin 256)
    (span : TwoPermutationPrototype.Opening.CapSpan node.val (height.val+1)) : CapNodeRange height node := by
  obtain ⟨_,first,last⟩ := span
  unfold CapNodeRange
  fin_cases height <;> norm_num at first last ⊢ <;> omega
theorem cap_call_node (node : Fin 256) (s : MachineState)
    (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) :
    (capCallPrefix s 6).getReg .x6=BitVec.ofNat 64 node.val := by
  rw [cap_call_node_value,child,cap_odd_half]
theorem cap_call_source (node : Fin 256) (s : MachineState)
    (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : s.getReg .x25=16384#64) :
    (capCallPrefix s 6).getReg .x10=capSource node := by
  rw [cap_call_source_value,child,cap_odd_half,heap,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 16384+BitVec.ofNat 64 node.val*BitVec.ofNat 64 64=BitVec.ofNat 64 (16384+64*node.val)
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
  congr 1
  omega
theorem cap_call_destination (node : Fin 256) (s : MachineState)
    (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : s.getReg .x25=16384#64) :
    (capCallPrefix s 6).getReg .x12=capDestination node := by
  rw [cap_call_destination_value,child,cap_odd_half,heap,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 16384+BitVec.ofNat 64 node.val*BitVec.ofNat 64 32=BitVec.ofNat 64 (16384+32*node.val)
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
  congr 1
  omega

theorem cap_call_execution (s : MachineState) (pc : s.pc=4096+4*2708) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (6+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (capCallPrefix s 6) coins
          return result.charge 6 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←cap_call_zero s]
  apply execute_unit_steps (states := capCallPrefix s)
  intro i inside
  refine ⟨.base (capCallOps.getD i .EBREAK),?_,?_,?_⟩
  · apply cap_call_at i inside
    rw [cap_call_prefix_pc s i (by omega),pc]
  · rw [cap_call_succ s i inside]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

def capParentReturnTrace (height : Fin 8) (s : MachineState) : OracleComp World MachineState :=
  capReturnTrace height (capCallPrefix s 6)
theorem cap_parent_return_execution (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2708) (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1))
    (heap : s.getReg .x25=16384#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (138+4*capDepth height+fuel) s coins=
      (do let out ← capParentReturnTrace height s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (145+4*capDepth height) 1) := by
  rw [show 138+4*capDepth height+fuel=6+(132+4*capDepth height+fuel) by omega,
    cap_call_execution s pc,cap_return_execution height node range _ (cap_call_pc s pc)
      (cap_call_node node s child) (cap_call_source node s child heap) (cap_call_destination node s child heap),
    capParentReturnTrace,capReturnTrace]
  simp [Execution.charge,←Nat.add_assoc]
theorem cap_parent_return_pc (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2708) (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1))
    (heap : s.getReg .x25=16384#64) (reached : out∈support (capParentReturnTrace height s)) :
    out.pc=4096+4*2714 :=
  cap_return_pc height node range _ out (cap_call_pc s pc) (cap_call_node node s child)
    (cap_call_source node s child heap) (cap_call_destination node s child heap) (cap_call_link s pc) reached

end CommitGolfCandidate.Chained.Native.CheckerCap

end

section

/-! Actual cap-result masking and the return to stackless DFS decisions. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage

def capFinishOps : List Instr := [.JAL .x0 128,.LD .x31 .x12 24,
  .SLLI .x31 .x31 18,.SRLI .x31 .x31 18,.SD .x12 .x31 24,
  .JAL .x0 2097012,.JAL .x0 2097108]
@[irreducible] def capFinishPrefix (s : MachineState) (n : Nat) : MachineState :=
  Nat.rec s (fun i before => execInstrBr before (capFinishOps.getD i .EBREAK)) n
theorem cap_finish_zero (s : MachineState) : capFinishPrefix s 0=s := by rw [capFinishPrefix]; rfl
theorem cap_finish_succ (s : MachineState) (n : Nat) :
    capFinishPrefix s (n+1)=execInstrBr (capFinishPrefix s n) (capFinishOps.getD n .EBREAK) := by
  unfold capFinishPrefix; rfl
def capFinishIndex (i : Fin 8) : Nat :=
  if i.val=0 then 2714 else if i.val≤5 then 2745+i.val else if i.val=6 then 2715 else 2704

theorem cap_finish_pc (s : MachineState) (pc : s.pc=4096+4*2714) (i : Fin 8) :
    (capFinishPrefix s i.val).pc=4096+BitVec.ofNat 64 (4*capFinishIndex i) := by
  have step (t : MachineState) (j : Fin 7) :
      (execInstrBr t (capFinishOps.getD j.val .EBREAK)).pc=t.pc+
        (if j.val=0 then signExtend21 128 else if j.val=5 then signExtend21 2097012
         else if j.val=6 then signExtend21 2097108 else 4) := by fin_cases j <;> rfl
  fin_cases i
  all_goals repeat rw [cap_finish_succ,step _ ⟨_,by omega⟩]
  all_goals rw [cap_finish_zero,pc]; rfl

theorem cap_finish_register (s : MachineState) (n : Nat) (small : n≤7) (reg : Reg) (temp : reg≠.x31) :
    (capFinishPrefix s n).getReg reg=s.getReg reg := by
  have jump (t : MachineState) (offset : BitVec 21) :
      (execInstrBr t (.JAL .x0 offset)).getReg reg=t.getReg reg := by
    change ((t.setReg .x0 (t.pc+4#64)).setPC (t.pc+signExtend21 offset)).getReg reg=_
    rw [MachineState.getReg_setPC]
    rfl
  have store (t : MachineState) (address value : Word) :
      (t.setMem address value).getReg reg=t.getReg reg := by cases reg <;> rfl
  have away : Reg.x31≠reg := Ne.symm temp
  have step (t : MachineState) (j : Fin 7) :
      (execInstrBr t (capFinishOps.getD j.val .EBREAK)).getReg reg=t.getReg reg := by
    fin_cases j
    case «0» => exact jump t 128
    case «5» => exact jump t 2097012
    case «6» => exact jump t 2097108
    all_goals simp only [capFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
      MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ away,store]
  induction n with
  | zero => rw [cap_finish_zero]
  | succ n ih => rw [cap_finish_succ,step _ ⟨n,by omega⟩,ih (by omega)]

private theorem merged_ChainedCheckerCapFinish_finish_ordinary_at (s : MachineState) (i : Fin 7)
    (access : accessValid (s.getReg .x12+signExtend12 24) 8=true) :
    ordinaryStep s (.base (capFinishOps.getD i.val .EBREAK))=
      some (execInstrBr s (capFinishOps.getD i.val .EBREAK)) := by
  fin_cases i
  case «1» =>
    change (if accessValid (s.getReg .x12+signExtend12 24) 8 then _ else _)=_
    exact ite_eq_left access
  case «4» =>
    change (if accessValid (s.getReg .x12+signExtend12 24) 8 then _ else _)=_
    exact ite_eq_left access
  all_goals rfl

theorem cap_finish_execution (s : MachineState) (pc : s.pc=4096+4*2714)
    (access : accessValid (s.getReg .x12+signExtend12 24) 8=true) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (7+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (capFinishPrefix s 7) coins
          return result.charge 7 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←cap_finish_zero s]
  apply execute_unit_steps (states := capFinishPrefix s)
  intro i inside
  refine ⟨.base (capFinishOps.getD i .EBREAK),?_,?_,?_⟩
  · have position := cap_finish_pc s pc ⟨i,by omega⟩
    interval_cases i
    all_goals exact chained_checker_ops_at _ (by rw [chained_checker_ops_length]; simp [capFinishIndex]) _ position
  · rw [cap_finish_succ]
    apply merged_ChainedCheckerCapFinish_finish_ordinary_at _ ⟨i,inside⟩
    rw [cap_finish_register s i (by omega) .x12 (by decide)]
    exact access
  · interval_cases i <;> rfl

theorem cap_parent_return_destination (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2708) (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1))
    (heap : s.getReg .x25=16384#64) (reached : out∈support (capParentReturnTrace height s)) :
    out.getReg .x12=capDestination node := by
  have restored := cap_return_register height node range _ out (cap_call_pc s pc) (cap_call_node node s child)
    (cap_call_source node s child heap) (cap_call_destination node s child heap) reached ⟨11,by omega⟩
  change out.getReg .x12=(capCallPrefix s 6).getReg .x12 at restored
  exact restored.trans (cap_call_destination node s child heap)

def capParentLoopTrace (height : Fin 8) (s : MachineState) : OracleComp World MachineState := do
  let out ← capParentReturnTrace height s
  pure (capFinishPrefix out 7)
theorem cap_parent_loop_execution (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s : MachineState) (pc : s.pc=4096+4*2708) (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1))
    (heap : s.getReg .x25=16384#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (145+4*capDepth height+fuel) s coins=
      (do let out ← capParentLoopTrace height s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (152+4*capDepth height) 1) := by
  rw [show 145+4*capDepth height+fuel=138+4*capDepth height+(7+fuel) by omega,
    cap_parent_return_execution height node range s pc child heap,capParentLoopTrace]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro out reached
  have access : accessValid (out.getReg .x12+signExtend12 24) 8=true := by
    rw [cap_parent_return_destination height node range s out pc child heap reached,
      show signExtend12 24=BitVec.ofNat 64 (8*3) from by decide +kernel]
    exact cap_destination_access node ⟨3,by decide⟩
  rw [cap_finish_execution out (cap_parent_return_pc height node range s out pc child heap reached) access]
  simp [Execution.charge,←Nat.add_assoc,show 145+4*capDepth height+7=152+4*capDepth height by omega]

theorem cap_parent_loop_pc (height : Fin 8) (node : Fin 256) (range : CapNodeRange height node)
    (s out : MachineState) (pc : s.pc=4096+4*2708) (child : s.getReg .x6=BitVec.ofNat 64 (2*node.val+1))
    (heap : s.getReg .x25=16384#64) (reached : out∈support (capParentLoopTrace height s)) :
    out.pc=4096+4*2704 := by
  simp only [capParentLoopTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨returned,first,rfl⟩ := reached
  exact cap_finish_pc returned (cap_parent_return_pc height node range s returned pc child heap first) ⟨7,by decide⟩

end CommitGolfCandidate.Chained.Native.CheckerCap

end

section

namespace CommitGolfCandidate.Chained.Native.CheckerCap.Visit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64

set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage
attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

private theorem merged_ChainedCheckerCapVisit_cap_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index<3012) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (opcode : chainedCheckerOps.getD index .EBREAK=instruction) :
    fetch chainedCheckerImage state=some (.base instruction) := by
  have location : state.pc=4096+BitVec.ofNat 64 (4*index) := by
    change state.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index)
    rwa [←BitVec.ofNat_add]
  simpa only [opcode] using chained_checker_ops_at index
    (by rw [chained_checker_ops_length]; exact bounded) state location

@[local simp] private theorem merged_ChainedCheckerCapVisit_pc_after (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
@[local simp] private theorem merged_ChainedCheckerCapVisit_reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def capMarkAddress (state : MachineState) : Word := state.getReg .x26 + (state.getReg .x6 <<< 3)
def capMarkedWord (state : MachineState) : Word := state.getMem (capMarkAddress state)

def capLookupCode : List Instr :=
  [.SLLI .x7 .x6 3, .ADD .x7 .x26 .x7, .LD .x28 .x7 0]

def capLookupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capLookupCode.take count).foldl execInstrBr state
attribute [local irreducible] capLookupPrefix

theorem cap_lookup_zero (state : MachineState) : capLookupPrefix state 0=state := by
  rw [capLookupPrefix]; rfl

theorem execute_cap_lookup_prefix (state : MachineState) (pc : state.pc = (4096+4*2661)) (fuel : Nat) (coins : Bool)
    (markRead : accessValid (capMarkAddress state) 8 = true) :
    execute chainedCheckerImage (3+fuel) state coins =
      (do let next ← execute chainedCheckerImage fuel (capLookupPrefix state 3) coins
          return next.charge 3 0) := by
  have access : accessValid (state.getReg .x26+(state.getReg .x6 <<< 3)) 8 = true := markRead
  conv_lhs => rw [←cap_lookup_zero state]
  apply execute_unit_steps (states := capLookupPrefix state)
  intro i bound
  refine ⟨.base (capLookupCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply merged_ChainedCheckerCapVisit_cap_fetch _ (2661+i) _ (by omega)
    · interval_cases i <;> simp [capLookupPrefix, capLookupCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
        capLookupPrefix, capLookupCode, access]
  · interval_cases i <;> rfl

theorem cap_lookup_prefix_mark (state : MachineState) :
    (capLookupPrefix state 3).getReg .x28 = capMarkedWord state := by
  simp [capLookupPrefix, capLookupCode, capMarkedWord, capMarkAddress, execInstrBr, signExtend12]

theorem cap_lookup_prefix_register (state : MachineState) (reg : Reg)
    (heap : reg ≠ .x7) (mark : reg ≠ .x28) :
    (capLookupPrefix state 3).getReg reg = state.getReg reg := by
  simp [capLookupPrefix, capLookupCode, execInstrBr, Ne.symm heap, Ne.symm mark]

def capLookup (state : MachineState) : MachineState :=
  let checked := capLookupPrefix state 3
  if capMarkedWord state = 0#64 then
    checked.setPC (4096+4*2668)
  else if state.getReg .x27 ≤ state.getReg .x6 then
    checked.setPC (4096+4*2704)
  else
    (checked.setReg .x6 (state.getReg .x6 <<< 1)).setPC (4096+4*2661)

def capLookupSteps (state : MachineState) : Nat :=
  if capMarkedWord state = 0#64 then 4 else if state.getReg .x27 ≤ state.getReg .x6 then 5 else 7

/-- DFS lookup branches to the frontier read, the marked-leaf return, or the
left child. The mark array is read once and no scratch memory is changed. -/
theorem execute_cap_lookup (state : MachineState) (pc : state.pc = (4096+4*2661)) (fuel : Nat) (coins : Bool)
    (markRead : accessValid (capMarkAddress state) 8 = true) :
    execute chainedCheckerImage (capLookupSteps state+fuel) state coins =
      (do let next ← execute chainedCheckerImage fuel (capLookup state) coins
          return next.charge (capLookupSteps state) 0) := by
  let checked := capLookupPrefix state 3
  have checkedPC : checked.pc = (4096+4*2664) := by
    simp [checked, capLookupPrefix, capLookupCode, execInstrBr, pc]
  have first : fetch chainedCheckerImage checked = some (.base (.BEQ .x28 .x0 16)) :=
    merged_ChainedCheckerCapVisit_cap_fetch checked 2664 _ (by decide) checkedPC rfl
  by_cases unmarked : capMarkedWord state = 0#64
  · have yes : ordinaryStep checked (.base (.BEQ .x28 .x0 16)) = some (checked.setPC (4096+4*2668)) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, checkedPC,
        show checked.getReg .x28 = capMarkedWord state from cap_lookup_prefix_mark state, unmarked]
    rw [capLookup, capLookupSteps, ite_eq_left unmarked, ite_eq_left unmarked,
      show 4+fuel = 3+(fuel+1) by omega, execute_cap_lookup_prefix _ pc _ coins markRead,
      execute_ordinary_step _ _ _ _ _ _ first yes]
    simp [Execution.charge, instructionCycles, checked, ← Nat.add_assoc]
  · let branched := checked.setPC (4096+4*2665)
    have no : ordinaryStep checked (.base (.BEQ .x28 .x0 16)) = some branched := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, checkedPC, branched,
        show checked.getReg .x28 = capMarkedWord state from cap_lookup_prefix_mark state, unmarked]
    have second : fetch chainedCheckerImage branched = some (.base (.BGEU .x6 .x27 156)) :=
      merged_ChainedCheckerCapVisit_cap_fetch branched 2665 _ (by decide) rfl rfl
    have r6 : branched.getReg .x6 = state.getReg .x6 := cap_lookup_prefix_register state .x6 (by decide) (by decide)
    have r27 : branched.getReg .x27 = state.getReg .x27 := cap_lookup_prefix_register state .x27 (by decide) (by decide)
    by_cases leaf : state.getReg .x27 ≤ state.getReg .x6
    · have leafBit : (branched.getReg .x6).ult (branched.getReg .x27) = false := by
        rw [r6, r27]
        exact decide_eq_false (Nat.not_lt.mpr leaf)
      have yes : ordinaryStep branched (.base (.BGEU .x6 .x27 156)) = some (checked.setPC (4096+4*2704)) := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
          leafBit, show branched.pc = (4096+4*2665) from rfl]
        rfl
      rw [capLookup, capLookupSteps, ite_eq_right unmarked, ite_eq_right unmarked,
        ite_eq_left leaf, ite_eq_left leaf, show 5+fuel = 3+((fuel+1)+1) by omega,
        execute_cap_lookup_prefix _ pc _ coins markRead,
        execute_ordinary_step _ _ _ _ _ _ first no, execute_ordinary_step _ _ _ _ _ _ second yes]
      simp [Execution.charge, instructionCycles, checked, ← Nat.add_assoc]
    · let beforeShift := checked.setPC (4096+4*2666)
      let shifted := (checked.setReg .x6 (state.getReg .x6 <<< 1)).setPC (4096+4*2667)
      have branchBit : (branched.getReg .x6).ult (branched.getReg .x27) = true := by
        rw [r6, r27]
        exact decide_eq_true (Nat.lt_of_not_ge leaf)
      have notLeaf : ordinaryStep branched (.base (.BGEU .x6 .x27 156)) = some beforeShift := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
          branchBit, show branched.pc = (4096+4*2665) from rfl]
        rfl
      have fShift : fetch chainedCheckerImage beforeShift = some (.base (.SLLI .x6 .x6 1)) :=
        merged_ChainedCheckerCapVisit_cap_fetch beforeShift 2666 _ (by decide) rfl rfl
      have sShift : ordinaryStep beforeShift (.base (.SLLI .x6 .x6 1)) = some shifted := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, beforeShift, shifted,
          show checked.getReg .x6 = state.getReg .x6 from r6]
        rfl
      have fJump : fetch chainedCheckerImage shifted = some (.base (.JAL .x0 2097128)) :=
        merged_ChainedCheckerCapVisit_cap_fetch shifted 2667 _ (by decide) rfl rfl
      have sJump : ordinaryStep shifted (.base (.JAL .x0 2097128)) =
          some ((checked.setReg .x6 (state.getReg .x6 <<< 1)).setPC (4096+4*2661)) := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, shifted, MachineState.setReg]
        rfl
      rw [capLookup, capLookupSteps, ite_eq_right unmarked, ite_eq_right unmarked,
        ite_eq_right leaf, ite_eq_right leaf, show 7+fuel = 3+((((fuel+1)+1)+1)+1) by omega,
        execute_cap_lookup_prefix _ pc _ coins markRead,
        execute_ordinary_step _ _ _ _ _ _ first no, execute_ordinary_step _ _ _ _ _ _ second notLeaf,
        execute_ordinary_step _ _ _ _ _ _ fShift sShift, execute_ordinary_step _ _ _ _ _ _ fJump sJump]
      simp [Execution.charge, instructionCycles, checked, ← Nat.add_assoc]

theorem cap_lookup_mark_address (state : MachineState) (node : Nat)
    (nodeReg : state.getReg .x6 = BitVec.ofNat 64 node) (markReg : state.getReg .x26 = 4096#64) :
    capMarkAddress state = wordAddress (512+node) := by
  rw [capMarkAddress, nodeReg, markReg, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 4096 + BitVec.ofNat 64 node * BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
  congr 1
  omega

theorem cap_lookup_post (state : MachineState) :
    let next := capLookup state
    let unmarked := capMarkedWord state = 0#64
    let leaf := state.getReg .x27 ≤ state.getReg .x6
    next.pc = (if unmarked then (4096+4*2668) else if leaf then (4096+4*2704) else (4096+4*2661)) ∧
    next.getReg .x6 = (if unmarked ∨ leaf then state.getReg .x6 else state.getReg .x6 <<< 1) ∧
    next.mem = state.mem := by
  have old := cap_lookup_prefix_register state .x6 (by decide) (by decide)
  dsimp only
  by_cases mark : capMarkedWord state = 0#64
  · simp [capLookup, mark, old]
    rw [capLookupPrefix]; rfl
  · by_cases leaf : state.getReg .x27 ≤ state.getReg .x6
    · simp [capLookup, mark, leaf, old]
      rw [capLookupPrefix]; rfl
    · simp [capLookup, mark, leaf, old]
      rw [capLookupPrefix]; rfl

theorem cap_lookup_register (state : MachineState) (reg : Reg) (node : reg ≠ .x6)
    (address : reg ≠ .x7) (mark : reg ≠ .x28) :
    (capLookup state).getReg reg = state.getReg reg := by
  unfold capLookup
  split
  · exact cap_lookup_prefix_register state reg address mark
  · split
    · exact cap_lookup_prefix_register state reg address mark
    · simp [Ne.symm node, cap_lookup_prefix_register state reg address mark]

end CommitGolfCandidate.Chained.Native.CheckerCap.Visit

end
