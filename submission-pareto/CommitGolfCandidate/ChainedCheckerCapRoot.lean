import CommitGolfCandidate.ChainedCheckerCapPosition
import CommitGolfCandidate.TwoPermutationCheckerCapCounts
import CommitGolfCandidate.TwoPermutationCheckerRootRun

section

/-! Recursive delivered cap control trace and its position/resource specification. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap.Visit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capHashCount)
set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage

def capTreeTrace (groups : List Nat) :
    (height : Nat) → height≤8 → Nat → MachineState → OracleComp World MachineState
  | 0,_,node,state => if capIsMarked groups node 0 then pure (capLookup state)
      else pure (frontierRead (capLookup state))
  | height+1,small,node,state =>
      if capIsMarked groups node (height+1) then do
        let left ← capTreeTrace groups height (by omega) (2*node) (capLookup state)
        let right ← capTreeTrace groups height (by omega) (2*node+1) (capRight (capAfterTests left))
        capParentLoopTrace ⟨height,by omega⟩ (capAfterTests right)
      else pure (frontierRead (capLookup state))

def capTreeSteps (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked groups node 0 then 5 else 40
  | height+1 => if capIsMarked groups node (height+1) then
      162+4*(7-height)+capTreeSteps groups (2*node) height+capTreeSteps groups (2*node+1) height else 40

def CapTreePost (groups : List Nat) (node height pointer : Nat) (before out : MachineState) : Prop :=
  out.pc=4096+4*2704 ∧
  CapPosition groups out node (pointer+30*(capFrontierNodes groups node height).length) ∧
  CapStable before out ∧ ∀ query, OutsideCap query → out.getMem query=before.getMem query

structure CapTreeCorrect (groups : List Nat) (height : Nat) (small : height≤8)
    (node pointer : Nat) (before : MachineState) : Prop where
  run : ∀ fuel coins, execute chainedCheckerImage (capTreeSteps groups node height+fuel) before coins=
    (do let out ← capTreeTrace groups height small node before
        let result ← execute chainedCheckerImage fuel out coins
        return result.charge (capTreeSteps groups node height+7*capHashCount groups node height)
          (capHashCount groups node height))
  post : ∀ out, out∈support (capTreeTrace groups height small node before) →
    CapTreePost groups node height pointer before out

theorem cap_tree_unmarked (groups : List Nat) (height : Nat) (small : height≤8) (node : Nat)
    (state : MachineState) (marked : capIsMarked groups node height=false) :
    capTreeTrace groups height small node state=pure (frontierRead (capLookup state)) ∧
      capTreeSteps groups node height=40 ∧ capHashCount groups node height=0 := by
  cases height <;> simp [capTreeTrace,capTreeSteps,capHashCount,marked]

theorem cap_frontier_fits {groups : List Nat} {state : MachineState} {node pointer finish : Nat}
    (position : CapPosition groups state node pointer) (endReg : state.getReg .x22=BitVec.ofNat 64 finish)
    (endBound : finish≤MEMORY_BYTES) (room : pointer+30≤finish) :
    ¬state.getReg .x22<state.getReg .x21+30#64 := by
  have top : MEMORY_BYTES<2^64 := by decide
  rw [endReg,position.proof]
  change ¬BitVec.ofNat 64 finish<BitVec.ofNat 64 pointer+BitVec.ofNat 64 30
  rw [←BitVec.ofNat_add]
  change ¬finish%2^64<(pointer+30)%2^64
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  omega

attribute [local irreducible] capTreeTrace

theorem cap_lookup_access {groups : List Nat} {state : MachineState} {node height pointer : Nat}
    (position : CapPosition groups state node pointer) (span : TwoPermutationPrototype.Opening.CapSpan node height) :
    accessValid (capMarkAddress state) 8=true := by
  rw [cap_lookup_mark_address state node position.heap position.context.controls.markBase]
  exact RecordLeaf.aligned_access (512+node) (by
    have := (TwoPermutationPrototype.Opening.cap_span_node node height span).2
    omega)

theorem cap_tree_leaf {groups : List Nat} {state : MachineState} {node pointer : Nat}
    (position : CapPosition groups state node pointer) (span : TwoPermutationPrototype.Opening.CapSpan node 0)
    (pc : state.pc=4096+4*2661) (marked : capIsMarked groups node 0=true) :
    CapTreeCorrect groups 0 (by decide) node pointer state := by
  have cost : capLookupSteps state=5 := by rw [cap_lookup_cost position span]; simp [marked]
  refine ⟨?_,?_⟩
  · intro fuel coins
    have run := execute_cap_lookup state pc fuel coins (cap_lookup_access position span)
    rw [cost] at run
    simpa [capTreeTrace,capTreeSteps,capHashCount,marked] using run
  · intro out reached
    simp only [capTreeTrace,marked,ite_true,support_pure,Set.mem_singleton_iff] at reached
    subst out
    obtain ⟨target,next,mem⟩ := cap_lookup_position position span
    refine ⟨by simpa [marked] using target,?_,cap_lookup_stable state,fun query _ => congrFun mem query⟩
    simpa [capFrontierNodes,marked] using next

theorem cap_tree_frontier {groups : List Nat} {state : MachineState} {node height pointer finish : Nat}
    (small : height≤8) (position : CapPosition groups state node pointer)
    (span : TwoPermutationPrototype.Opening.CapSpan node height) (pc : state.pc=4096+4*2661)
    (endReg : state.getReg .x22=BitVec.ofNat 64 finish) (endBound : finish≤MEMORY_BYTES)
    (room : pointer+30≤finish) (marked : capIsMarked groups node height=false) :
    CapTreeCorrect groups height small node pointer state := by
  have unmarked := cap_tree_unmarked groups height small node state marked
  have cost : capLookupSteps state=4 := by rw [cap_lookup_cost position span]; simp [marked]
  obtain ⟨target,next,mem⟩ := cap_lookup_position position span
  have looked : CapPosition groups (capLookup state) node pointer := by simpa [marked] using next
  have ready : FrontierReady (capLookup state) node pointer :=
    ⟨by simpa [marked] using target,looked.heap,looked.context.controls.roots,looked.proof,
      (TwoPermutationPrototype.Opening.cap_span_node node height span).2,looked.above,looked.even,by omega⟩
  have finishReg : (capLookup state).getReg .x22=BitVec.ofNat 64 finish :=
    (cap_lookup_register state .x22 (by decide) (by decide) (by decide)).trans endReg
  have fits := cap_frontier_fits looked finishReg endBound room
  have fields : capFrontierNodes groups node height=[node] := by
    cases height <;> simp [capFrontierNodes,marked]
  refine ⟨?_,?_⟩
  · intro fuel coins
    rw [unmarked.2.1,unmarked.2.2,unmarked.1]
    simp only [Nat.mul_zero,Nat.add_zero,pure_bind]
    have lookup := execute_cap_lookup state pc (36+fuel) coins (cap_lookup_access position span)
    rw [cost] at lookup
    rw [show 40+fuel=4+(36+fuel) by omega,lookup,actualFrontier.run _ node pointer ready fits fuel coins]
    simp [Execution.charge,←Nat.add_assoc,actualFrontier]
  · intro out reached
    rw [unmarked.1] at reached
    simp only [support_pure,Set.mem_singleton_iff] at reached
    subst out
    refine ⟨(actualFrontier.pointer _ node pointer ready).1,?_,
      (cap_lookup_stable state).trans (cap_frontier_stable (capLookup state)),?_⟩
    · simpa only [fields,List.length_singleton,Nat.mul_one] using cap_frontier_position looked ready fits
    · intro query outside
      exact (cap_frontier_memory _ node pointer ready fits query outside).trans (congrFun mem query)

end CommitGolfCandidate.Chained.Native.CheckerCap.Visit

end

section

/-! Height induction for the delivered cap traversal. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap.Visit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capHashCount)
set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage capTreeTrace

def CapLowerCorrect (groups : List Nat) (height : Nat) (small : height≤8) (finish : Nat) : Prop :=
  ∀ node pointer state, CapPosition groups state node pointer →
    TwoPermutationPrototype.Opening.CapSpan node height → state.pc=4096+4*2661 →
    state.getReg .x22=BitVec.ofNat 64 finish →
    pointer+30*(capFrontierNodes groups node height).length≤finish →
    CapTreeCorrect groups height small node pointer state

theorem cap_tree_branch {groups : List Nat} {height node pointer finish : Nat} {state : MachineState}
    (small : height+1≤8) (position : CapPosition groups state node pointer)
    (span : TwoPermutationPrototype.Opening.CapSpan node (height+1)) (pc : state.pc=4096+4*2661)
    (endReg : state.getReg .x22=BitVec.ofNat 64 finish)
    (room : pointer+30*(capFrontierNodes groups node (height+1)).length≤finish)
    (marked : capIsMarked groups node (height+1)=true)
    (lower : CapLowerCorrect groups height (by omega) finish) :
    CapTreeCorrect groups (height+1) small node pointer state := by
  have children := TwoPermutationPrototype.Opening.cap_span_children node height span
  have fields : (capFrontierNodes groups node (height+1)).length=
      (capFrontierNodes groups (2*node) height).length+(capFrontierNodes groups (2*node+1) height).length := by
    simp [capFrontierNodes,marked]
  rw [fields] at room
  have bound : 0<node ∧ 2*node<512 := by
    have := (TwoPermutationPrototype.Opening.cap_span_node node (height+1) span).1
    have := TwoPermutationPrototype.Opening.cap_span_is_internal node height span
    omega
  obtain ⟨target,next,mem⟩ := cap_lookup_position position span
  have leftPC : (capLookup state).pc=4096+4*2661 := by simpa [marked] using target
  have leftPos : CapPosition groups (capLookup state) (2*node) pointer := by simpa [marked] using next
  have leftEnd : (capLookup state).getReg .x22=BitVec.ofNat 64 finish :=
    ((cap_lookup_stable state) .x22 (by decide)).trans endReg
  have leftOk := lower (2*node) pointer (capLookup state) leftPos children.1 leftPC leftEnd (by omega)
  have rightOk (left : MachineState) (reached : left∈support (capTreeTrace groups height (by omega) (2*node) (capLookup state))) :
      CapTreeCorrect groups height (by omega) (2*node+1)
        (pointer+30*(capFrontierNodes groups (2*node) height).length) (capRight (capAfterTests left)) := by
    have post := leftOk.post left reached
    have next := cap_sibling_position post.2.1 post.1 bound
    have stable := ((cap_lookup_stable state).trans post.2.2.1).trans
      ((cap_tests_stable left).trans (cap_right_stable (capAfterTests left)))
    exact lower _ _ _ next.2.1 children.2 next.1 ((stable .x22 (by decide)).trans endReg) (by omega)
  let parent : Fin 256 := ⟨node,TwoPermutationPrototype.Opening.cap_span_is_internal node height span⟩
  let level : Fin 8 := ⟨height,by omega⟩
  have cost : capLookupSteps state=7 := by rw [cap_lookup_cost position span]; simp [marked]
  refine ⟨?_,?_⟩
  · intro fuel coins
    rw [capTreeSteps,capHashCount,capTreeTrace]
    simp only [marked,ite_true]
    rw [show 162+4*(7-height)+capTreeSteps groups (2*node) height+capTreeSteps groups (2*node+1) height+fuel=
      7+(capTreeSteps groups (2*node) height+(6+(capTreeSteps groups (2*node+1) height+(149+4*capDepth level+fuel)))) by
        dsimp [level,capDepth]; omega]
    have lookup := execute_cap_lookup state pc
      (capTreeSteps groups (2*node) height+(6+(capTreeSteps groups (2*node+1) height+(149+4*capDepth level+fuel))))
      coins (cap_lookup_access position span)
    rw [cost] at lookup
    rw [lookup,leftOk.run]
    simp only [bind_assoc,pure_bind]
    apply bind_congr_of_forall_mem_support
    intro left reached
    have post := leftOk.post left reached
    rw [cap_sibling_execution left node bound post.1 post.2.1.heap _ coins,(rightOk left reached).run]
    simp only [bind_assoc,pure_bind]
    apply bind_congr_of_forall_mem_support
    intro right reachedRight
    have postRight := (rightOk left reached).post right reachedRight
    rw [cap_ascend_execution level parent span right postRight.2.1 postRight.1 fuel coins]
    simp only [bind_assoc,pure_bind]
    apply bind_congr_of_forall_mem_support
    intro out _
    apply bind_congr_of_forall_mem_support
    intro result _
    congr 1
    cases result
    (simp [Execution.charge,level,capDepth,Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]; omega)
  · intro out reached
    simp only [capTreeTrace,marked,ite_true,mem_support_bind_iff] at reached
    obtain ⟨left,reachedLeft,right,reachedRight,reachedParent⟩ := reached
    have postLeft := leftOk.post left reachedLeft
    have sibling := cap_sibling_position postLeft.2.1 postLeft.1 bound
    have postRight := (rightOk left reachedLeft).post right reachedRight
    have postParent := cap_ascend_position level parent span right out postRight.2.1 postRight.1 reachedParent
    refine ⟨postParent.1,?_,?_,?_⟩
    · simpa [fields,Nat.mul_add,Nat.add_assoc] using postParent.2.1
    · exact ((((cap_lookup_stable state).trans postLeft.2.2.1).trans
        ((cap_tests_stable left).trans (cap_right_stable (capAfterTests left)))).trans postRight.2.2.1).trans postParent.2.2.1
    · intro query outside
      exact (postParent.2.2.2 query outside).trans ((postRight.2.2.2 query outside).trans
        ((congrFun sibling.2.2 query).trans ((postLeft.2.2.2 query outside).trans (congrFun mem query))))

theorem cap_tree_correct (groups : List Nat) (height finish : Nat) (endBound : finish≤MEMORY_BYTES) :
    ∀ small : height≤8, CapLowerCorrect groups height small finish := by
  induction height with
  | zero =>
    intro small node pointer state position span pc endReg room
    by_cases marked : capIsMarked groups node 0=true
    · exact cap_tree_leaf position span pc marked
    · have unmarked : capIsMarked groups node 0=false := by simpa using marked
      exact cap_tree_frontier small position span pc endReg endBound
        (by simpa [capFrontierNodes,unmarked] using room) unmarked
  | succ height ih =>
    intro small node pointer state position span pc endReg room
    by_cases marked : capIsMarked groups node (height+1)=true
    · exact cap_tree_branch small position span pc endReg room marked (ih (by omega))
    · have unmarked : capIsMarked groups node (height+1)=false := by simpa using marked
      exact cap_tree_frontier small position span pc endReg endBound
        (by simpa [capFrontierNodes,unmarked] using room) unmarked

theorem cap_tree_steps_bound (groups : List Nat) (height : Nat) :
    ∀ node, capTreeSteps groups node height+190≤230*2^height := by
  induction height with
  | zero => intro node; simp only [capTreeSteps]; split <;> norm_num
  | succ height ih =>
    intro node
    have left := ih (2*node)
    have right := ih (2*node+1)
    rw [capTreeSteps,Nat.pow_succ]
    split <;> omega

theorem cap_tree_calls_bound (groups : List Nat) (height : Nat) :
    ∀ node, capHashCount groups node height+1≤2^height := by
  induction height with
  | zero => intro node; simp [capHashCount]
  | succ height ih =>
    intro node
    have left := ih (2*node)
    have right := ih (2*node+1)
    rw [capHashCount,Nat.pow_succ]
    split <;> omega

theorem cap_tree_root_limits (groups : List Nat) :
    capTreeSteps groups 1 8≤58690 ∧ capHashCount groups 1 8≤255 ∧
      capTreeSteps groups 1 8+7*capHashCount groups 1 8≤60475 := by
  have steps := cap_tree_steps_bound groups 8 1
  have calls := cap_tree_calls_bound groups 8 1
  norm_num at steps calls
  omega

end CommitGolfCandidate.Chained.Native.CheckerCap.Visit

end

section

/-! Delivered cap initialization and the root-return edge to commitment checking. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap.Visit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capHashCount)
set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage capTreeTrace
attribute [local simp] MachineState.getReg_setPC TwoPermutationPrototype.Opening.getReg_setReg
@[local simp] private theorem merged_ChainedCheckerCapEntry_zero_reg (state : MachineState) : state.getReg .x0=0#64 := rfl
@[local simp] private theorem merged_ChainedCheckerCapEntry_pc_set (state : MachineState) (pc : Word) : (state.setPC pc).pc=pc := rfl

structure CapDfsEntryReady (groups : List Nat) (state : MachineState) (pointer finish : Nat) : Prop where
  pc : state.pc=4096+4*2658
  selector : state.getReg .x5=0#64
  roots : state.getReg .x25=16384#64
  markBase : state.getReg .x26=4096#64
  capLeaves : state.getReg .x27=256#64
  marked : ∀ node, 0<node → node<512 → memoryView state (512+node)=TwoPermutationPrototype.Opening.markWord groups node
  cursor : state.getReg .x21=BitVec.ofNat 64 pointer
  endReg : state.getReg .x22=BitVec.ofNat 64 finish
  above : 32768≤pointer
  even : pointer%2=0
  endBound : finish≤MEMORY_BYTES
  room : pointer+30*(capFrontierNodes groups 1 8).length≤finish

theorem cap_start_register (state : MachineState) (reg : Reg) (node : reg≠.x6)
    (size : reg≠.x11) (primitive : reg≠.x13) : (capStart state).getReg reg=state.getReg reg := by
  simp [capStart,blockPrefix,capStartCode,execInstrBr,Ne.symm node,Ne.symm size,Ne.symm primitive]

theorem cap_start_values (state : MachineState) (pc : state.pc=4096+4*2658) :
    (capStart state).pc=4096+4*2661 ∧ (capStart state).getReg .x6=1#64 ∧
      (capStart state).getReg .x11=64#64 ∧ (capStart state).getReg .x13=0#64 ∧ (capStart state).mem=state.mem := by
  simp [capStart,blockPrefix,capStartCode,execInstrBr,signExtend12,pc]
  rfl

theorem cap_start_position {groups : List Nat} {state : MachineState} {pointer finish : Nat}
    (ready : CapDfsEntryReady groups state pointer finish) :
    (capStart state).pc=4096+4*2661 ∧ CapPosition groups (capStart state) 1 pointer ∧ (capStart state).mem=state.mem := by
  obtain ⟨pc,node,size,primitive,mem⟩ := cap_start_values state ready.pc
  have controls : CapControls (capStart state) :=
    ⟨(cap_start_register state .x5 (by decide) (by decide) (by decide)).trans ready.selector,size,primitive,
      (cap_start_register state .x25 (by decide) (by decide) (by decide)).trans ready.roots,
      (cap_start_register state .x26 (by decide) (by decide) (by decide)).trans ready.markBase,
      (cap_start_register state .x27 (by decide) (by decide) (by decide)).trans ready.capLeaves⟩
  have context : CapContext groups (capStart state) :=
    ⟨controls,fun value positive bound => (congrFun mem _).trans (ready.marked value positive bound)⟩
  exact ⟨pc,⟨context,node,(cap_start_register state .x21 (by decide) (by decide) (by decide)).trans ready.cursor,
    ready.above,ready.even⟩,mem⟩

theorem cap_root_position {groups : List Nat} {state : MachineState} {pointer : Nat}
    (position : CapPosition groups state 1 pointer) (pc : state.pc=4096+4*2704) :
    (capRootTest state).pc=4096+4*2718 ∧ CapPosition groups (capRootTest state) 1 pointer ∧
      CapStable state (capRootTest state) ∧ (capRootTest state).mem=state.mem := by
  have root : state.getReg .x6=1#64 := position.heap
  have mem : (capRootTest state).mem=state.mem := by
    simp [capRootTest,blockPrefix,capRootTestCode,execInstrBr,signExtend12,root]
    rfl
  have stable : CapStable state (capRootTest state) := by
    intro reg found
    apply root_test_register
    intro equal
    subst reg
    simp [capFixedRegisters] at found
  refine ⟨?_,⟨position.context.transport stable (fun _ _ _ => congrFun mem _),
    (root_test_register state .x6 (by decide)).trans position.heap,
    (root_test_register state .x21 (by decide)).trans position.proof,position.above,position.even⟩,stable,mem⟩
  rw [cap_root_post state pc,ite_eq_left root]

def capDfsEntryTrace (groups : List Nat) (state : MachineState) : OracleComp World MachineState := do
  let out ← capTreeTrace groups 8 (by decide) 1 (capStart state)
  return capRootTest out

theorem cap_entry_execution {groups : List Nat} {state : MachineState} {pointer finish : Nat}
    (ready : CapDfsEntryReady groups state pointer finish) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (5+capTreeSteps groups 1 8+fuel) state coins=
      (do let out ← capDfsEntryTrace groups state
          let result ← execute chainedCheckerImage fuel out coins
          return result.charge (5+capTreeSteps groups 1 8+7*capHashCount groups 1 8) (capHashCount groups 1 8)) := by
  have start := cap_start_position ready
  have correct := cap_tree_correct groups 8 finish ready.endBound (by decide) 1 pointer (capStart state)
    start.2.1 TwoPermutationPrototype.Opening.cap_span_root start.1
    ((cap_start_register state .x22 (by decide) (by decide) (by decide)).trans ready.endReg) ready.room
  rw [capDfsEntryTrace]
  simp only [bind_assoc,pure_bind]
  rw [show 5+capTreeSteps groups 1 8+fuel=3+(capTreeSteps groups 1 8+(2+fuel)) by omega,
    execute_cap_start state ready.pc _ coins,correct.run]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro out reached
  rw [execute_cap_root_test out (correct.post out reached).1 fuel coins]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro result _
  congr 1
  cases result
  (simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]; omega)

theorem cap_entry_post {groups : List Nat} {state out : MachineState} {pointer finish : Nat}
    (ready : CapDfsEntryReady groups state pointer finish) (reached : out∈support (capDfsEntryTrace groups state)) :
    out.pc=4096+4*2718 ∧ CapPosition groups out 1 (pointer+30*(capFrontierNodes groups 1 8).length) ∧
    (∀ query, OutsideCap query → out.getMem query=state.getMem query) ∧
    ∀ reg, reg∈capFixedRegisters → reg≠.x11 → reg≠.x13 → out.getReg reg=state.getReg reg := by
  have start := cap_start_position ready
  have correct := cap_tree_correct groups 8 finish ready.endBound (by decide) 1 pointer (capStart state)
    start.2.1 TwoPermutationPrototype.Opening.cap_span_root start.1
    ((cap_start_register state .x22 (by decide) (by decide) (by decide)).trans ready.endReg) ready.room
  simp only [capDfsEntryTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨middle,reached,rfl⟩ := reached
  have post := correct.post middle reached
  have root := cap_root_position post.2.1 post.1
  refine ⟨root.1,root.2.1,?_,?_⟩
  · intro query outside
    exact (congrFun root.2.2.2 query).trans ((post.2.2.2 query outside).trans (congrFun start.2.2 query))
  · intro reg found size primitive
    have node : reg≠.x6 := by intro same; subst reg; simp [capFixedRegisters] at found
    exact (((post.2.2.1.trans root.2.2.1) reg found).trans (cap_start_register state reg node size primitive))

theorem cap_entry_limits (groups : List Nat) :
    5+capTreeSteps groups 1 8≤58695 ∧ capHashCount groups 1 8≤255 ∧
      5+capTreeSteps groups 1 8+7*capHashCount groups 1 8≤60480 := by
  have := cap_tree_root_limits groups
  omega

end CommitGolfCandidate.Chained.Native.CheckerCap.Visit

end

section

/-! Actual root-length, commitment-byte comparisons and terminal exits. -/

namespace CommitGolfCandidate.Chained.Native.CheckerCap.Visit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt word_offset aligned_access)
set_option maxRecDepth 8192
attribute [local irreducible] execute chainedCheckerImage
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC

private theorem merged_ChainedCheckerCapRoot_cap_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index<3012) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (opcode : chainedCheckerOps.getD index .EBREAK=instruction) :
    fetch chainedCheckerImage state=some (.base instruction) := by
  have location : state.pc=4096+BitVec.ofNat 64 (4*index) := by
    change state.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index)
    rwa [←BitVec.ofNat_add]
  simpa only [opcode] using chained_checker_ops_at index
    (by rw [chained_checker_ops_length]; exact bounded) state location


@[local simp] private theorem merged_ChainedCheckerCapRoot_pc_after (s : MachineState) (pc : Word) : (s.setPC pc).pc = pc := rfl

def rootCompareCode (i : Fin 4) : List Instr :=
  [.LD .x29 .x25 (BitVec.ofNat 12 (32+8*i.val)),
   .LD .x30 .x9 (BitVec.ofNat 12 (8*i.val)),
   .BNE .x29 .x30 (BitVec.ofNat 13 (68-12*i.val))]

def rootComparePrefix (state : MachineState) (i : Fin 4) (count : Nat) : MachineState :=
  ((rootCompareCode i).take count).foldl execInstrBr state

def rootCompare (state : MachineState) (i : Fin 4) := rootComparePrefix state i 3

def rootWordMatches (state : MachineState) (i : Fin 4) : Prop :=
  state.getMem (state.getReg .x25 + BitVec.ofNat 64 (32+8*i.val)) =
    state.getMem (state.getReg .x9 + BitVec.ofNat 64 (8*i.val))

instance rootWordMatchesDec (state : MachineState) (i : Fin 4) : Decidable (rootWordMatches state i) :=
  inferInstanceAs (Decidable (_ = _))

theorem execute_root_compare (state : MachineState) (i : Fin 4) (fuel : Nat)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(2719+3*i.val)))
    (cap : accessValid (state.getReg .x25+BitVec.ofNat 64 (32+8*i.val)) 8 = true)
    (claim : accessValid (state.getReg .x9+BitVec.ofNat 64 (8*i.val)) 8 = true) :
    execute chainedCheckerImage (3+fuel) state false =
      (do let result ← execute chainedCheckerImage fuel (rootCompare state i) false
          return result.charge 3 0) := by
  apply execute_unit_steps (states := rootComparePrefix state i)
  intro j bounded
  refine ⟨.base ((rootCompareCode i)[j]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply merged_ChainedCheckerCapRoot_cap_fetch _ (2719+3*i.val+j) _ (by omega)
    · fin_cases i <;> interval_cases j <;>
        simp [rootComparePrefix, rootCompareCode, execInstrBr, pc, MachineState.setPC]
    · fin_cases i <;> interval_cases j <;> rfl
  · fin_cases i <;> interval_cases j <;>
      simp_all [rootComparePrefix, rootCompareCode, execInstrBr, ordinaryStep, memoryArgumentsValid,
        memAccess, signExtend12]
  · interval_cases j <;> rfl

private theorem merged_ChainedCheckerCapRoot_compare_bne_pc (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).pc = if s.getReg a=s.getReg b then s.pc+4 else s.pc+signExtend13 d := by
  simp only [execInstrBr,bne_iff_ne]
  by_cases eq : s.getReg a=s.getReg b <;> simp [eq]

private theorem merged_ChainedCheckerCapRoot_compare_bne_reg (s : MachineState) (a b r : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).getReg r=s.getReg r := by simp only [execInstrBr]; split <;> rfl

private theorem merged_ChainedCheckerCapRoot_compare_bne_mem (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).mem=s.mem := by simp only [execInstrBr]; split <;> rfl

private theorem merged_ChainedCheckerCapRoot_getMem_pc (s : MachineState) (p a : Word) : (s.setPC p).getMem a=s.getMem a := rfl
private theorem merged_ChainedCheckerCapRoot_getMem_reg (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getMem a=s.getMem a := by cases r <;> rfl
attribute [local simp] merged_ChainedCheckerCapRoot_getMem_pc merged_ChainedCheckerCapRoot_getMem_reg

theorem root_compare_post (s : MachineState) (i : Fin 4)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(2719+3*i.val))) :
    let t := rootCompare s i
    t.pc=(if rootWordMatches s i then BitVec.ofNat 64 (4096+4*(2722+3*i.val)) else (4096+4*2738)) ∧
      t.mem=s.mem ∧ ∀ r : Reg, r≠.x29 → r≠.x30 → t.getReg r=s.getReg r := by
  dsimp only
  simp only [rootCompare,rootComparePrefix,rootCompareCode,List.take,List.foldl_cons,List.foldl_nil,
    merged_ChainedCheckerCapRoot_compare_bne_pc,merged_ChainedCheckerCapRoot_compare_bne_reg,merged_ChainedCheckerCapRoot_compare_bne_mem]
  fin_cases i <;> simp [rootWordMatches,execInstrBr,signExtend12,signExtend13,pc]
  all_goals first
    | (refine ⟨rfl, rfl, ?_⟩; intro r m p; simp [Ne.symm m, Ne.symm p])
    | (refine ⟨rfl, ?_⟩; intro r m p; simp [Ne.symm m, Ne.symm p])
    | (intro r m p; simp [Ne.symm m, Ne.symm p])

def rootLength (state : MachineState) := execInstrBr state (.BNE .x21 .x22 80)

theorem execute_root_length (state : MachineState) (pc : state.pc = (4096+4*2718)) (fuel : Nat) :
    execute chainedCheckerImage (1+fuel) state false =
      (do let next ← execute chainedCheckerImage fuel (rootLength state) false
          return next.charge 1 0) := by
  have fetched := merged_ChainedCheckerCapRoot_cap_fetch state 2718 (.BNE .x21 .x22 80) (by decide) pc rfl
  have next : ordinaryStep state (.base (.BNE .x21 .x22 80)) = some (rootLength state) := rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched next]
  rfl

theorem root_length_post (state : MachineState) (pc : state.pc = (4096+4*2718)) :
    (rootLength state).pc = (if state.getReg .x21 = state.getReg .x22 then (4096+4*2719) else (4096+4*2738)) ∧
      (rootLength state).mem = state.mem ∧
      ∀ reg, (rootLength state).getReg reg = state.getReg reg := by
  by_cases length : state.getReg .x21 = state.getReg .x22 <;>
    simp [rootLength, merged_ChainedCheckerCapRoot_compare_bne_pc, merged_ChainedCheckerCapRoot_compare_bne_reg, merged_ChainedCheckerCapRoot_compare_bne_mem, pc, length, signExtend13] <;> rfl

def rejectState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 1).setPC (4096+4*2740)

theorem execute_reject (state : MachineState) (pc : state.pc = (4096+4*2738)) (fuel : Nat) :
    execute chainedCheckerImage (3+fuel) state false = pure ⟨.failure, rejectState state, 3, 0⟩ := by
  let first := (state.setReg .x5 1).setPC (4096+4*2739)
  have a := merged_ChainedCheckerCapRoot_cap_fetch state 2738 (.ADDI .x5 .x0 1) (by decide) pc rfl
  have b := merged_ChainedCheckerCapRoot_cap_fetch first 2739 (.ADDI .x10 .x0 1) (by decide) rfl rfl
  have c := merged_ChainedCheckerCapRoot_cap_fetch (rejectState state) 2740 .ECALL (by decide) rfl rfl
  have r : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some first := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, first] <;> rfl
  have t : ordinaryStep first (.base (.ADDI .x10 .x0 1)) = some (rejectState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, first, rejectState] <;> rfl
  rw [Nat.add_comm 3 fuel]
  simp only [execute, a, b, c, r, t, instructionCycles, pure_bind]
  rfl

def acceptState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC (4096+4*2733)

theorem execute_accept (state : MachineState) (pc : state.pc = (4096+4*2731)) (fuel : Nat) :
    execute chainedCheckerImage (3+fuel) state false = pure ⟨.success, acceptState state, 3, 0⟩ := by
  let first := (state.setReg .x5 1).setPC (4096+4*2732)
  have a := merged_ChainedCheckerCapRoot_cap_fetch state 2731 (.ADDI .x5 .x0 1) (by decide) pc rfl
  have b := merged_ChainedCheckerCapRoot_cap_fetch first 2732 (.ADDI .x10 .x0 0) (by decide) rfl rfl
  have c := merged_ChainedCheckerCapRoot_cap_fetch (acceptState state) 2733 .ECALL (by decide) rfl rfl
  have r : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some first := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, first] <;> rfl
  have t : ordinaryStep first (.base (.ADDI .x10 .x0 0)) = some (acceptState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, first, acceptState] <;> rfl
  rw [Nat.add_comm 3 fuel]
  simp only [execute, a, b, c, r, t, instructionCycles, pure_bind]
  rfl


structure RootScanReady (state : MachineState) (claim left : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*(2719+3*(4-left)))
  roots : state.getReg .x25 = wordAddress 2048
  commitment : state.getReg .x9 = wordAddress claim
  claimBound : claim+4 ≤ 2^33

theorem root_word_unchanged (before after : MachineState)
    (mem : after.mem = before.mem) (r25 : after.getReg .x25 = before.getReg .x25)
    (r9 : after.getReg .x9 = before.getReg .x9) (i : Fin 4) :
    rootWordMatches after i ↔ rootWordMatches before i := by
  simp [rootWordMatches, MachineState.getMem, mem, r25, r9]

private theorem merged_ChainedCheckerCapRoot_root_scan_addresses {state : MachineState} {claim left : Nat}
    (ready : RootScanReady state claim left) (i : Fin 4) :
    accessValid (state.getReg .x25+BitVec.ofNat 64 (32+8*i.val)) 8 = true ∧
      accessValid (state.getReg .x9+BitVec.ofNat 64 (8*i.val)) 8 = true := by
  rw [ready.roots, ready.commitment, show 32+8*i.val = 8*(4+i.val) by omega, word_offset, word_offset]
  exact ⟨aligned_access _ (by omega), aligned_access _ (by have := ready.claimBound; omega)⟩

theorem execute_root_scan {state : MachineState} {claim left : Nat}
    (ready : RootScanReady state claim left) (bounded : left ≤ 4) (fuel : Nat) :
    ∃ result : Execution,
      (result.exit = .success ↔ ∀ i : Fin 4, 4-left ≤ i.val → rootWordMatches state i) ∧
      result.oracleCalls = 0 ∧ result.exit ≠ .unfinished ∧
      result.cycles≤3*left+3 ∧
      execute chainedCheckerImage (3*left+3+fuel) state false = pure result := by
  induction left generalizing state fuel with
  | zero =>
    have pc : state.pc = (4096+4*2731) := ready.pc
    refine ⟨⟨.success, acceptState state,3,0⟩, ?_, rfl, (show Exit.success ≠ Exit.unfinished by decide), by change 3≤3*0+3;decide,
      execute_accept state pc fuel⟩
    simp only [Nat.sub_zero, true_iff]
    intro i impossible
    omega
  | succ left ih =>
    let i : Fin 4 := ⟨4-(left+1), by omega⟩
    let next := rootCompare state i
    have pc : state.pc = BitVec.ofNat 64 (4096+4*(2719+3*i.val)) := ready.pc
    obtain ⟨cap, claimAccess⟩ := merged_ChainedCheckerCapRoot_root_scan_addresses ready i
    obtain ⟨nextPC, mem, regs⟩ := root_compare_post state i pc
    have executed := execute_root_compare state i (3*left+3+fuel) pc cap claimAccess
    have stable := root_word_unchanged state next mem (regs .x25 (by decide) (by decide))
      (regs .x9 (by decide) (by decide))
    have splitFuel : 3*(left+1)+3+fuel = 3+(3*left+3+fuel) := by omega
    rw [splitFuel, executed]
    by_cases same : rootWordMatches state i
    · have nextReady : RootScanReady next claim left := by
        refine ⟨?_, (regs .x25 (by decide) (by decide)).trans ready.roots,
          (regs .x9 (by decide) (by decide)).trans ready.commitment, ready.claimBound⟩
        change next.pc = _ at nextPC
        rw [nextPC, ite_eq_left same]
        congr 1
        have : i.val = 4-(left+1) := rfl
        omega
      obtain ⟨result, accepted, calls, ended, cycles, continuation⟩ := ih nextReady (by omega) fuel
      refine ⟨result.charge 3 0, ?_, by simpa [Execution.charge] using calls, ended,
        by change 3+result.cycles≤_;omega,?_⟩
      · change result.exit = .success ↔ _
        rw [accepted]
        constructor
        · intro tail j valid
          by_cases first : j = i
          · rwa [first]
          · have jAfter : 4-left ≤ j.val := by
              have : j.val ≠ i.val := fun eq => first (Fin.ext eq)
              have : i.val = 4-(left+1) := rfl
              omega
            exact (stable j).mp (tail j jAfter)
        · intro all j valid
          exact (stable j).mpr (all j (by omega))
      · erw [continuation]
        simp
    · have reject : next.pc = (4096+4*2738) := by
        change next.pc = _ at nextPC
        rw [nextPC, ite_eq_right same]
      refine ⟨⟨.failure,rejectState next,6,0⟩, ?_, rfl, (show Exit.failure ≠ Exit.unfinished by decide), by dsimp;omega,?_⟩
      · constructor
        · intro impossible
          cases impossible
        · intro all
          exact False.elim (same (all i (by rfl)))
      · have terminal := execute_reject next reject (3*left+fuel)
        erw [show 3*left+3+fuel = 3+(3*left+fuel) by omega, terminal]
        simp [Execution.charge]

theorem root_words_iff (state : MachineState) (claim : Nat)
    (roots : state.getReg .x25 = wordAddress 2048)
    (claimReg : state.getReg .x9 = wordAddress claim) :
    (∀ i : Fin 4, rootWordMatches state i) ↔ capRootAt state 1 = readBuffer state (8*claim) 32 := by
  unfold capRootAt
  rw [read_digest_eq_iff _ _ _ _ (by omega) (by omega)]
  constructor
  · intro words j bounded
    have same := words ⟨j,bounded⟩
    unfold rootWordMatches at same
    rw [roots, claimReg, show 32+8*j = 8*(4+j) by omega, word_offset, word_offset] at same
    simpa only [← Nat.mul_add, wordAddress, Nat.add_assoc] using same
  · intro digest i
    unfold rootWordMatches
    rw [roots, claimReg, show 32+8*i.val = 8*(4+i.val) by omega, word_offset, word_offset]
    simpa only [← Nat.mul_add, wordAddress, Nat.add_assoc] using digest i.val i.isLt

theorem execute_root_check (state : MachineState) (claim fuel : Nat) (pc : state.pc = (4096+4*2718))
    (roots : state.getReg .x25 = wordAddress 2048) (claimReg : state.getReg .x9 = wordAddress claim)
    (claimBound : claim+4 ≤ 2^33) :
    ∃ result : Execution,
      (result.exit = .success ↔ state.getReg .x21 = state.getReg .x22 ∧
        capRootAt state 1 = readBuffer state (8*claim) 32) ∧ result.oracleCalls = 0 ∧ result.exit ≠ .unfinished ∧
      result.cycles≤16 ∧
      execute chainedCheckerImage (16+fuel) state false = pure result := by
  obtain ⟨target, mem, stable⟩ := root_length_post state pc
  let next := rootLength state
  have entry : next.getReg .x9 = wordAddress claim := (stable _).trans claimReg
  have endRoots : next.getReg .x25 = wordAddress 2048 := (stable _).trans roots
  have paired (i : Fin 4) := root_word_unchanged state next mem (stable .x25) (stable .x9) i
  rw [show 16+fuel = 1+(15+fuel) by omega, execute_root_length state pc]
  by_cases length : state.getReg .x21 = state.getReg .x22
  · have entered : RootScanReady next claim 4 := by
      refine ⟨?_, endRoots, entry, claimBound⟩
      change next.pc = _
      rw [target, ite_eq_left length]
      rfl
    obtain ⟨result, good, calls, ended, cycles, execution⟩ := execute_root_scan entered (by decide) fuel
    have run : execute chainedCheckerImage (15+fuel) (rootLength state) false = pure result := execution
    refine ⟨result.charge 1 0, ?_, by simpa [Execution.charge] using calls, ended,
      by change 1+result.cycles≤16;omega,?_⟩
    · rw [show (result.charge 1 0).exit = result.exit from rfl, good,
        ← root_words_iff state claim roots claimReg]
      simp only [length, true_and, Nat.sub_self, Nat.zero_le, forall_const]
      exact ⟨fun matched i => (paired i).mp (matched i), fun matched i => (paired i).mpr (matched i)⟩
    · rw [run]
      simp
  · have fail : next.pc = (4096+4*2738) := by rw [target, ite_eq_right length]
    have run : execute chainedCheckerImage (15+fuel) (rootLength state) false =
        pure ⟨.failure, rejectState next, 3, 0⟩ := by
      rw [show 15+fuel = 3+(12+fuel) by omega]
      exact execute_reject next fail _
    refine ⟨⟨.failure,rejectState next,4,0⟩, by simp [length], rfl,
      (show Exit.failure ≠ Exit.unfinished by decide), by change 4≤16;decide,?_⟩
    rw [run]
    simp [Execution.charge]

end CommitGolfCandidate.Chained.Native.CheckerCap.Visit

end
