import CommitGolfCandidate.ChainedCheckerLeafReturn
import CommitGolfCandidate.ChainedCheckerHashRestore
import CommitGolfCandidate.ChainedHashMemory
import CommitGolfCandidate.TwoPermutationPackedOpeningCopy
import CommitGolfCandidate.TwoPermutationPackedCapBytes

/-! Delivered first-sibling dispatch, ordered child preparation and lower hash. -/
namespace CommitGolfCandidate.Chained.Native.RecordLeaf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
open TwoPermutationPrototype TwoPermutationPrototype.Packed TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne MachineState.getReg_setPC
@[local simp] private theorem path_pc_set (s : MachineState) (target : Word) : (s.setPC target).pc=target := rfl
@[local simp] private theorem path_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

def checkerLowerGateOps : List Instr := [.ADDI .x30 .x0 16,.BEQ .x29 .x30 336]
@[irreducible] def checkerLowerGatePrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerLowerGateOps.take n).foldl execInstrBr s
def checkerLowerChoiceOps : List Instr := [.ADDI .x30 .x0 32,.ANDI .x7 .x6 1,.BEQ .x7 .x0 168]
@[irreducible] def checkerLowerChoicePrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerLowerChoiceOps.take n).foldl execInstrBr s

theorem checker_lower_gate_at : OpsAt chainedCheckerImage (4096+4*2437) checkerLowerGateOps :=
  chained_checker_slice_at 2437 2 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_lower_choice_at : OpsAt chainedCheckerImage (4096+4*2522) checkerLowerChoiceOps :=
  chained_checker_slice_at 2522 3 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_lower_gate_pc (s : MachineState) (pc : s.pc=4096+4*2437)
    (counter : s.getReg .x29=16) : (checkerLowerGatePrefix s 2).pc=4096+4*2522 := by
  simp [checkerLowerGatePrefix,checkerLowerGateOps,execInstrBr,pc,counter,signExtend12,signExtend13]

theorem checker_lower_gate_register (s : MachineState) (reg : Reg) (kept : reg≠.x30) :
    (checkerLowerGatePrefix s 2).getReg reg=s.getReg reg := by
  simp only [checkerLowerGatePrefix,checkerLowerGateOps,List.take,List.foldl,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm kept)]
  split_ifs <;> simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm kept)]

theorem checker_lower_gate_execution (s : MachineState) (pc : s.pc=4096+4*2437)
    (counter : s.getReg .x29=16) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLowerGatePrefix s 2) coins
          return result.charge 2 0) := by
  rw [checking_manifest_image]
  have zero : checkerLowerGatePrefix s 0=s := by rw [checkerLowerGatePrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerLowerGatePrefix s)
  intro i inside
  refine ⟨.base (checkerLowerGateOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_lower_gate_at i inside
    interval_cases i <;> simp [checkerLowerGatePrefix,checkerLowerGateOps,execInstrBr,pc]
  · interval_cases i <;> rw [checkerLowerGatePrefix,checkerLowerGatePrefix] <;> rfl
  · interval_cases i <;> rfl

theorem checker_lower_choice_pc (s : MachineState) (pc : s.pc=4096+4*2522) :
    (checkerLowerChoicePrefix s 3).pc=
      if s.getReg .x6 &&& 1=0 then 4096+4*2566 else 4096+4*2525 := by
  simp [checkerLowerChoicePrefix,checkerLowerChoiceOps,execInstrBr,pc,signExtend12,signExtend13]
  split_ifs <;> rfl

theorem checker_lower_choice_register (s : MachineState) (reg : Reg) (kept : reg≠.x30) (scratch : reg≠.x7) :
    (checkerLowerChoicePrefix s 3).getReg reg=s.getReg reg := by
  simp only [checkerLowerChoicePrefix,checkerLowerChoiceOps,List.take,List.foldl,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm kept),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]
  split_ifs <;> simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm kept)]

theorem checker_lower_choice_execution (s : MachineState) (pc : s.pc=4096+4*2522)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (3+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLowerChoicePrefix s 3) coins
          return result.charge 3 0) := by
  rw [checking_manifest_image]
  have zero : checkerLowerChoicePrefix s 0=s := by rw [checkerLowerChoicePrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerLowerChoicePrefix s)
  intro i inside
  refine ⟨.base (checkerLowerChoiceOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_lower_choice_at i inside
    interval_cases i <;> simp [checkerLowerChoicePrefix,checkerLowerChoiceOps,execInstrBr,pc,BitVec.add_assoc]
  · interval_cases i <;> rw [checkerLowerChoicePrefix,checkerLowerChoicePrefix] <;> rfl
  · interval_cases i <;> rfl

@[irreducible] def checkerFirstSiblingState (s : MachineState) : MachineState :=
  checkerLowerChoicePrefix (checkerLowerGatePrefix s 2) 3
theorem checker_first_sibling_eq (s : MachineState) :
    checkerFirstSiblingState s=checkerLowerChoicePrefix (checkerLowerGatePrefix s 2) 3 := by rw [checkerFirstSiblingState]

theorem checker_first_sibling_pc (s : MachineState) (pc : s.pc=4096+4*2437)
    (counter : s.getReg .x29=16) :
    (checkerFirstSiblingState s).pc=if s.getReg .x6 &&& 1=0 then 4096+4*2566 else 4096+4*2525 := by
  rw [checker_first_sibling_eq,checker_lower_choice_pc _ (checker_lower_gate_pc s pc counter),
    checker_lower_gate_register _ .x6 (by decide)]

theorem checker_first_sibling_register (s : MachineState) (reg : Reg) (counter : reg≠.x30) (scratch : reg≠.x7) :
    (checkerFirstSiblingState s).getReg reg=s.getReg reg := by
  rw [checker_first_sibling_eq,checker_lower_choice_register _ reg counter scratch,
    checker_lower_gate_register _ reg counter]

theorem checker_first_sibling_execution (s : MachineState) (pc : s.pc=4096+4*2437)
    (counter : s.getReg .x29=16) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (5+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFirstSiblingState s) coins
          return result.charge 5 0) := by
  rw [show 5+fuel=2+(3+fuel) by omega,checker_lower_gate_execution s pc counter,
    checker_lower_choice_execution _ (checker_lower_gate_pc s pc counter),checker_first_sibling_eq]
  simp [bind_assoc,Execution.charge,←Nat.add_assoc]

theorem checker_first_odd_copy_ready {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState) (ready : CheckerFirstPathReady input s base record)
    (odd : ¬s.getReg .x6 &&& 1=0) :
    CopyReady (checkerCopyCode .firstOdd) (checkerFirstSiblingState s) (base.value+16) 12544 0 := by
  have baseAbove := base.above
  have baseRoom := base.room
  have baseEven := base.even
  refine ⟨?_,?_,?_,?_,by decide,?_,by decide⟩
  · change (checkerFirstSiblingState s).pc=BitVec.ofNat 64 (4096+4*2525)
    rw [checker_first_sibling_pc s ready.pc ready.counter,ite_eq_right odd]
    rfl
  · exact (checker_first_sibling_register s .x21 (by first | decide +kernel | omega) (by first | decide +kernel | omega)).trans ready.source
  · change (checkerFirstSiblingState s).getReg .x24+0=BitVec.ofNat 64 12544
    rw [checker_first_sibling_register s .x24 (by first | decide +kernel | omega) (by first | decide +kernel | omega),ready.pair]
    rfl
  · change base.value+16+32≤MEMORY_BYTES
    omega
  · omega

inductive FirstSiblingOrder where | odd | even
def FirstSiblingOrder.childStart : FirstSiblingOrder → Nat | .odd => 2557 | .even => 2566
def FirstSiblingOrder.childOffset : FirstSiblingOrder → Nat | .odd => 32 | .even => 0
def checkerFirstChildOps (order : FirstSiblingOrder) : List Instr := [
  .LD .x31 .x23 0,.SD .x24 .x31 (BitVec.ofNat 12 order.childOffset),
  .LD .x31 .x23 8,.SD .x24 .x31 (BitVec.ofNat 12 (order.childOffset+8)),
  .LD .x31 .x23 16,.SD .x24 .x31 (BitVec.ofNat 12 (order.childOffset+16)),
  .LD .x31 .x23 24,.SD .x24 .x31 (BitVec.ofNat 12 (order.childOffset+24))]
@[irreducible] def checkerFirstChildPrefix (order : FirstSiblingOrder) (s : MachineState) (n : Nat) : MachineState :=
  (checkerFirstChildOps order |>.take n).foldl execInstrBr s

private theorem child_reg_mem (s : MachineState) (address value : Word) (reg : Reg) :
    (s.setMem address value).getReg reg=s.getReg reg := by cases reg <;> rfl

theorem checker_first_child_at (order : FirstSiblingOrder) :
    OpsAt chainedCheckerImage (BitVec.ofNat 64 (4096+4*order.childStart)) (checkerFirstChildOps order) := by
  cases order
  · exact chained_checker_slice_at 2557 8 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2566 8 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_first_child_register (order : FirstSiblingOrder) (s : MachineState) (n : Nat)
    (small : n≤8) (reg : Reg) (scratch : reg≠.x31) :
    (checkerFirstChildPrefix order s n).getReg reg=s.getReg reg := by
  interval_cases n <;> rw [checkerFirstChildPrefix]
  all_goals simp only [checkerFirstChildOps,List.take,List.foldl,execInstrBr,
    MachineState.getReg_setPC,child_reg_mem,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem checker_first_child_pc (order : FirstSiblingOrder) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*order.childStart)) :
    (checkerFirstChildPrefix order s 8).pc=BitVec.ofNat 64 (4096+4*(order.childStart+8)) := by
  cases order <;> simp [checkerFirstChildPrefix,checkerFirstChildOps,execInstrBr,pc,FirstSiblingOrder.childStart]
  all_goals rfl

theorem checker_first_child_execution (order : FirstSiblingOrder) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*order.childStart))
    (digest : s.getReg .x23=12288) (pair : s.getReg .x24=12544)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (8+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFirstChildPrefix order s 8) coins
          return result.charge 8 0) := by
  rw [checking_manifest_image]
  have zero : checkerFirstChildPrefix order s 0=s := by rw [checkerFirstChildPrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerFirstChildPrefix order s)
  intro i inside
  refine ⟨.base ((checkerFirstChildOps order).getD i .EBREAK),?_,?_,?_⟩
  · apply checker_first_child_at order i inside
    cases order <;> interval_cases i <;> simp [checkerFirstChildPrefix,checkerFirstChildOps,execInstrBr,pc,BitVec.add_assoc]
  · have src := (checker_first_child_register order s i (by omega) .x23 (by decide)).trans digest
    have dst := (checker_first_child_register order s i (by omega) .x24 (by decide)).trans pair
    have valid : memoryArgumentsValid (checkerFirstChildPrefix order s i) ((checkerFirstChildOps order).getD i .EBREAK)=true := by
      cases order <;> interval_cases i <;>
        simp only [checkerFirstChildOps,List.getD_cons_zero,List.getD_cons_succ,memoryArgumentsValid,memAccess,src,dst]
      all_goals decide +kernel
    cases order <;> interval_cases i
    all_goals simp only [checkerFirstChildOps,List.getD_cons_zero,List.getD_cons_succ] at valid ⊢
    all_goals simp only [ordinaryStep,valid,ite_true]
    all_goals rw [checkerFirstChildPrefix,checkerFirstChildPrefix]; rfl
  · cases order <;> interval_cases i <;> rfl

theorem checker_first_even_copy_ready {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState) (ready : CheckerFirstPathReady input s base record)
    (even : s.getReg .x6 &&& 1=0) :
    CopyReady (checkerCopyCode .firstEven) (checkerFirstChildPrefix .even (checkerFirstSiblingState s) 8)
      (base.value+16) 12576 0 := by
  have baseAbove := base.above
  have baseRoom := base.room
  have baseEven := base.even
  refine ⟨?_,?_,?_,?_,by decide,?_,by decide⟩
  · have pc : (checkerFirstSiblingState s).pc=4096+4*2566 := by
      rw [checker_first_sibling_pc s ready.pc ready.counter,if_pos even]
    exact checker_first_child_pc .even _ pc
  · rw [checker_first_child_register _ _ _ (by omega) _ (by first | decide +kernel | omega),
      checker_first_sibling_register _ _ (by first | decide +kernel | omega) (by first | decide +kernel | omega)]
    exact ready.source
  · change (checkerFirstChildPrefix .even (checkerFirstSiblingState s) 8).getReg .x24+32=BitVec.ofNat 64 12576
    rw [checker_first_child_register _ _ _ (by omega) _ (by first | decide +kernel | omega),
      checker_first_sibling_register _ _ (by first | decide +kernel | omega) (by first | decide +kernel | omega),ready.pair]
    rfl
  · change base.value+16+32≤MEMORY_BYTES
    omega
  · omega

@[irreducible] def checkerFirstOrderedState (s : MachineState) : MachineState :=
  if s.getReg .x6 &&& 1=0 then
    checkerCopyState .firstEven (checkerFirstChildPrefix .even (checkerFirstSiblingState s) 8)
  else execInstrBr (checkerFirstChildPrefix .odd (checkerCopyState .firstOdd (checkerFirstSiblingState s)) 8) (.JAL .x0 164)

def checkerFirstOrderingInstructions (s : MachineState) : Nat := if s.getReg .x6 &&& 1=0 then 45 else 46

theorem checker_first_ordered_register (s : MachineState) (reg : Reg)
    (scratch : reg≠.x31) (stride : reg≠.x30) (parity : reg≠.x7) :
    (checkerFirstOrderedState s).getReg reg=s.getReg reg := by
  rw [checkerFirstOrderedState]
  split_ifs
  · rw [checker_copy_register _ _ _ scratch,checker_first_child_register _ _ _ (by omega) _ scratch,
      checker_first_sibling_register _ _ stride parity]
  · have jump (t : MachineState) : (execInstrBr t (.JAL .x0 164)).getReg reg=t.getReg reg := by
      cases reg <;> rfl
    rw [jump,checker_first_child_register _ _ _ (by omega) _ scratch,checker_copy_register _ _ _ scratch,
      checker_first_sibling_register _ _ stride parity]

theorem checker_first_ordered_pc {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState) (ready : CheckerFirstPathReady input s base record) :
    (checkerFirstOrderedState s).pc=4096+4*2606 := by
  rw [checkerFirstOrderedState]
  split_ifs with even
  · have pc := checker_copy_pc .firstEven _ _ _ (checker_first_even_copy_ready input s ready even)
    exact pc
  · have copyPC := checker_copy_pc .firstOdd _ _ _ (checker_first_odd_copy_ready input s ready even)
    have pc := checker_first_child_pc .odd _ copyPC
    change (checkerFirstChildPrefix .odd (checkerCopyState .firstOdd (checkerFirstSiblingState s)) 8).pc+signExtend21 164=_
    rw [pc]
    rfl

theorem checker_first_ordered_execution {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerFirstOrderingInstructions s+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFirstOrderedState s) coins
          return result.charge (checkerFirstOrderingInstructions s) 0) := by
  have digest : (checkerFirstSiblingState s).getReg .x23=12288 :=
    (checker_first_sibling_register _ _ (by decide) (by decide)).trans ready.digest
  have pair : (checkerFirstSiblingState s).getReg .x24=12544 :=
    (checker_first_sibling_register _ _ (by decide) (by decide)).trans ready.pair
  by_cases even : s.getReg .x6 &&& 1=0
  · have pc : (checkerFirstSiblingState s).pc=4096+4*2566 := by
      rw [checker_first_sibling_pc s ready.pc ready.counter,if_pos even]
    have copied := checker_copy_execution .firstEven _ _ _ (checker_first_even_copy_ready input s ready even) fuel coins
    simp only [CheckerCopySite.count,Nat.reduceMul] at copied
    rw [checkerFirstOrderingInstructions,if_pos even,show 45+fuel=5+(8+(32+fuel)) by omega,
      checker_first_sibling_execution s ready.pc ready.counter,checker_first_child_execution .even _ pc digest pair,
      copied,
      checkerFirstOrderedState,if_pos even]
    simp [Execution.charge,←Nat.add_assoc,bind_assoc,CheckerCopySite.count]
  · have copyReady := checker_first_odd_copy_ready input s ready even
    have copyPC := checker_copy_pc .firstOdd _ _ _ copyReady
    have childPC := checker_first_child_pc .odd _ copyPC
    have afterDigest := (checker_copy_register .firstOdd (checkerFirstSiblingState s) .x23 (by decide)).trans digest
    have afterPair := (checker_copy_register .firstOdd (checkerFirstSiblingState s) .x24 (by decide)).trans pair
    have fetched := trunc_fetch _ 2565 (.JAL .x0 164) (by omega) childPC rfl
    have step : ordinaryStep (checkerFirstChildPrefix .odd (checkerCopyState .firstOdd (checkerFirstSiblingState s)) 8)
        (.base (.JAL .x0 164))=some (execInstrBr (checkerFirstChildPrefix .odd
          (checkerCopyState .firstOdd (checkerFirstSiblingState s)) 8) (.JAL .x0 164)) := rfl
    have copied := checker_copy_execution .firstOdd _ _ _ copyReady (8+(1+fuel)) coins
    simp only [CheckerCopySite.count,Nat.reduceMul] at copied
    rw [checkerFirstOrderingInstructions,if_neg even,show 46+fuel=5+(32+(8+(1+fuel))) by omega,
      checker_first_sibling_execution s ready.pc ready.counter,
      copied,
      checker_first_child_execution .odd _ copyPC afterDigest afterPair]
    simp only [CheckerCopySite.count,bind_assoc]
    rw [show 1+fuel=fuel+1 by omega,
      execute_ordinary_step (Artifact.submission.image .check) _ _ _ _ coins fetched step,
      checkerFirstOrderedState,if_neg even]
    simp [Execution.charge,←Nat.add_assoc,instructionCycles]

def checkerFirstHashCallOps : List Instr := [.ADDI .x10 .x24 0,.ADDI .x12 .x23 0,.JAL .x1 596]
@[irreducible] def checkerFirstHashCallPrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerFirstHashCallOps.take n).foldl execInstrBr s
theorem checker_first_hash_call_at : OpsAt chainedCheckerImage (4096+4*2606) checkerFirstHashCallOps :=
  chained_checker_slice_at 2606 3 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_first_hash_call_pc (s : MachineState) (pc : s.pc=4096+4*2606) :
    (checkerFirstHashCallPrefix s 3).pc=4096+4*2757 := by
  simp [checkerFirstHashCallPrefix,checkerFirstHashCallOps,execInstrBr,pc]
  rfl

theorem checker_first_hash_call_register (s : MachineState) (reg : Reg)
    (source : reg≠.x10) (dest : reg≠.x12) (link : reg≠.x1) :
    (checkerFirstHashCallPrefix s 3).getReg reg=s.getReg reg := by
  simp [checkerFirstHashCallPrefix,checkerFirstHashCallOps,execInstrBr,Ne.symm source,Ne.symm dest,Ne.symm link]

theorem checker_first_hash_call_execution (s : MachineState) (pc : s.pc=4096+4*2606)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (3+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFirstHashCallPrefix s 3) coins
          return result.charge 3 0) := by
  rw [checking_manifest_image]
  have zero : checkerFirstHashCallPrefix s 0=s := by rw [checkerFirstHashCallPrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerFirstHashCallPrefix s)
  intro i inside
  refine ⟨.base (checkerFirstHashCallOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_first_hash_call_at i inside
    interval_cases i <;> simp [checkerFirstHashCallPrefix,checkerFirstHashCallOps,execInstrBr,pc,BitVec.add_assoc]
  · interval_cases i <;> rw [checkerFirstHashCallPrefix,checkerFirstHashCallPrefix] <;> rfl
  · interval_cases i <;> rfl

@[irreducible] def checkerFirstSiblingHashTrace (s : MachineState) : OracleComp World MachineState :=
  checkerHashTrace .lower 3 (checkerFirstHashState (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3))

theorem checker_first_sibling_hash_eq (s : MachineState) : checkerFirstSiblingHashTrace s=
    checkerHashTrace .lower 3 (checkerFirstHashState (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3)) := by
  rw [checkerFirstSiblingHashTrace]

theorem checker_first_sibling_hash_prepared {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) :
    CheckerFirstHashReady (checkerFirstHashState (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3)) := by
  apply checker_first_hash_ready _ (checker_first_hash_call_pc _ (checker_first_ordered_pc input s ready))
  · rw [checker_first_hash_call_register _ _ (by decide) (by decide) (by decide),
      checker_first_ordered_register _ _ (by decide) (by decide) (by decide)]
    exact ready.pair
  · rw [checker_first_hash_call_register _ _ (by decide) (by decide) (by decide),
      checker_first_ordered_register _ _ (by decide) (by decide) (by decide)]
    exact ready.counter

theorem checker_first_sibling_hash_execution {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerFirstOrderingInstructions s+120+fuel) s coins=
      (do let out ← checkerFirstSiblingHashTrace s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (checkerFirstOrderingInstructions s+148) 4) := by
  have pair : (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg .x24=12544 := by
    rw [checker_first_hash_call_register _ _ (by decide) (by decide) (by decide),
      checker_first_ordered_register _ _ (by decide) (by decide) (by decide)]
    exact ready.pair
  have counter : (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg .x29=16 := by
    rw [checker_first_hash_call_register _ _ (by decide) (by decide) (by decide),
      checker_first_ordered_register _ _ (by decide) (by decide) (by decide)]
    exact ready.counter
  rw [show checkerFirstOrderingInstructions s+120+fuel=checkerFirstOrderingInstructions s+(3+(117+fuel)) by omega,
    checker_first_ordered_execution input s ready,
    checker_first_hash_call_execution _ (checker_first_ordered_pc input s ready),
    checker_first_hash_execution _ (checker_first_hash_call_pc _ (checker_first_ordered_pc input s ready)) pair counter,
    checker_first_sibling_hash_eq]
  simp [Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,bind_assoc]

theorem checker_first_sibling_hash_pc {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstSiblingHashTrace s)) :
    out.pc=4096+4*2820 := by
  rw [checker_first_sibling_hash_eq] at reached
  exact checker_hash_return_pc .lower 3 _ out (checker_first_sibling_hash_prepared input s ready).pc reached

theorem checker_first_sibling_hash_bounded (s : MachineState) : PublicQueryBound (checkerFirstSiblingHashTrace s) 4 := by
  rw [checker_first_sibling_hash_eq]
  exact checker_hash_trace_bounded .lower 3 _

theorem checker_first_sibling_caller_register (s : MachineState) (reg : Reg)
    (link : reg≠.x1) (arg0 : reg≠.x10) (arg1 : reg≠.x12)
    (scratch : reg≠.x31) (stride : reg≠.x30) (parity : reg≠.x7) :
    (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg reg=s.getReg reg := by
  rw [checker_first_hash_call_register _ _ arg0 arg1 link,checker_first_ordered_register _ _ scratch stride parity]

theorem checker_first_sibling_saved {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstSiblingHashTrace s)) (slot : Fin 31) :
    out.getMem (checkerSaveWord slot)=
      (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg (checkerSnapshotReg slot) := by
  rw [checker_first_sibling_hash_eq] at reached
  apply (checker_hash_saved_memory .lower 3 _ out (checker_first_sibling_hash_prepared input s ready).args reached slot).trans
  apply checker_first_hash_saved
  rw [checker_first_sibling_caller_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact ready.pair

theorem checker_first_sibling_destination {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstSiblingHashTrace s)) :
    out.getMem (checkerSaveWord CheckerHashSite.lower.resultSlot)=12288 := by
  rw [checker_first_sibling_saved input s out ready reached,
    checker_first_sibling_caller_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact ready.digest

theorem checker_first_sibling_return_pc {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstSiblingHashTrace s)) :
    (checkerHashReturned .lower out).pc=4096+4*2609 := by
  apply checker_hash_returned_pc out (checker_first_sibling_destination input s out ready reached)
  rw [checker_first_sibling_saved input s out ready reached]
  have pc := checker_first_ordered_pc input s ready
  simp [checkerFirstHashCallPrefix,checkerFirstHashCallOps,execInstrBr,pc,checkerSnapshotReg,checkerSnapshotRegs]

theorem checker_first_sibling_return_digest {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstSiblingHashTrace s)) :
    (checkerHashReturned .lower out).getReg .x23=12288 := by
  exact (checker_hash_returned_register .lower out (checker_first_sibling_destination input s out ready reached) ⟨22,by omega⟩).trans
    (checker_first_sibling_destination input s out ready reached)

def checkerFirstLowerTrace (s : MachineState) : OracleComp World MachineState := do
  let out ← checkerFirstSiblingHashTrace s
  pure (checkerLowerFinishPrefix (checkerHashReturned .lower out) 10)

theorem checker_first_lower_execution {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerFirstOrderingInstructions s+171+fuel) s coins=
      (do let out ← checkerFirstLowerTrace s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (checkerFirstOrderingInstructions s+199) 4) := by
  rw [show checkerFirstOrderingInstructions s+171+fuel=checkerFirstOrderingInstructions s+120+(41+(10+fuel)) by omega,
    checker_first_sibling_hash_execution input s ready,checkerFirstLowerTrace]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro out reached
  rw [checker_hash_return_execution .lower out (checker_first_sibling_hash_pc input s out ready reached)
    (checker_first_sibling_destination input s out ready reached),
    checker_lower_finish_execution _ (checker_first_sibling_return_pc input s out ready reached)
      (checker_first_sibling_return_digest input s out ready reached)]
  simp [Execution.charge,←Nat.add_assoc]

def checkerFirstOrderingInput (input : CheckInput) (record : Nat := 0) : Nat :=
  if BitVec.ofNat 64 (LENGTH+((input.positions.sort (·≤·))[record]?.getD (⟨0,by decide⟩ : Index)).val) &&& 1=0 then 45 else 46

theorem checker_first_sibling_return_register {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstSiblingHashTrace s)) (slot : Fin 31) :
    (checkerHashReturned .lower out).getReg (checkerSnapshotReg slot)=
      (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg (checkerSnapshotReg slot) :=
  (checker_hash_returned_register .lower out (checker_first_sibling_destination input s out ready reached) slot).trans
    (checker_first_sibling_saved input s out ready reached slot)

theorem checker_first_sibling_return_counter {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstSiblingHashTrace s)) :
    (checkerHashReturned .lower out).getReg .x29=16 := by
  have restored := checker_first_sibling_return_register input s out ready reached ⟨28,by omega⟩
  change (checkerHashReturned .lower out).getReg .x29=
    (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg .x29 at restored
  rw [checker_first_sibling_caller_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at restored
  exact restored.trans ready.counter

theorem checker_first_lower_pc {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstLowerTrace s)) :
    out.pc=4096+4*2437 := by
  simp only [checkerFirstLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  exact checker_lower_finish_return_pc _ (checker_first_sibling_return_pc input s hashed ready last)
    (checker_first_sibling_return_counter input s hashed ready last)

theorem checker_first_ordered_stride (s : MachineState) : (checkerFirstOrderedState s).getReg .x30=32 := by
  have choice : (checkerFirstSiblingState s).getReg .x30=32 := by
    rw [checkerFirstSiblingState]
    simp only [checkerLowerChoicePrefix,checkerLowerChoiceOps,List.take,List.foldl,execInstrBr]
    split_ifs <;> simp_all [MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,signExtend12]
  rw [checkerFirstOrderedState]
  split_ifs
  · rw [checker_copy_register _ _ _ (by decide),checker_first_child_register _ _ _ (by omega) _ (by decide)]
    exact choice
  · have jump (t : MachineState) : (execInstrBr t (.JAL .x0 164)).getReg .x30=t.getReg .x30 := rfl
    rw [jump,checker_first_child_register _ _ _ (by omega) _ (by decide),checker_copy_register _ _ _ (by decide)]
    exact choice

theorem checker_first_lower_values {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstLowerTrace s)) :
    out.getReg .x21=s.getReg .x21+32 ∧ out.getReg .x6=s.getReg .x6 >>> 1 ∧ out.getReg .x29=15 := by
  simp only [checkerFirstLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  have cursor := checker_first_sibling_return_register input s hashed ready last ⟨20,by omega⟩
  have node := checker_first_sibling_return_register input s hashed ready last ⟨5,by omega⟩
  have stride := checker_first_sibling_return_register input s hashed ready last ⟨29,by omega⟩
  change (checkerHashReturned .lower hashed).getReg .x21=(checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg .x21 at cursor
  change (checkerHashReturned .lower hashed).getReg .x6=(checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg .x6 at node
  change (checkerHashReturned .lower hashed).getReg .x30=(checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg .x30 at stride
  rw [checker_first_sibling_caller_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at cursor node
  rw [checker_first_hash_call_register _ _ (by decide) (by decide) (by decide),checker_first_ordered_stride] at stride
  have values := checker_lower_finish_values _ (checker_first_sibling_return_counter input s hashed ready last)
  rwa [cursor,node,stride] at values

theorem checker_first_ordering_input {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) : checkerFirstOrderingInstructions s=checkerFirstOrderingInput input record := by
  rw [checkerFirstOrderingInstructions,ready.node]
  rfl

theorem checker_first_ordering_input_costs (input : CheckInput) (record : Nat := 0) :
    (checkerFirstOrderingInput input record=45 ∨ checkerFirstOrderingInput input record=46) := by
  unfold checkerFirstOrderingInput
  split_ifs <;> simp

theorem checker_decoded_first_sibling_hash_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (fuel : Nat) :
    execute (Artifact.submission.image .check) (2120+checkerFirstOrderingInput input+120+fuel) s false=
      (do let after ← leafQueries (checkerRecordNonceState s) 754975239 (checkerFirstInputIndex input nonempty)
          let out ← checkerFirstSiblingHashTrace (checkerLeafPathState after)
          let result ← execute (Artifact.submission.image .check) fuel out false
          return result.charge (checkerFirstOrderingInput input+2282) 6) := by
  rw [show 2120+checkerFirstOrderingInput input+120+fuel=2120+(checkerFirstOrderingInput input+120+fuel) by omega,
    checker_decoded_path_execution input nonempty footer s ready]
  simp only [leafQueries,bind_assoc,pure_bind]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  have pathReady := checker_first_path_ready input nonempty footer s ready a b
  rw [←checker_first_ordering_input input _ pathReady,
    checker_first_sibling_hash_execution input _ pathReady]
  have cost (n : Nat) : 2134+n+148=n+2282 := by omega
  simp [Execution.charge,←Nat.add_assoc,cost]

end CommitGolfCandidate.Chained.Native.RecordLeaf

/-! Content of the ordered child pair consumed by the first delivered lower hash. -/
namespace CommitGolfCandidate.Chained.Native.RecordLeaf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

private theorem content_reg_mem (s : MachineState) (address value : Word) (reg : Reg) :
    (s.setMem address value).getReg reg=s.getReg reg := by cases reg <;> rfl
private theorem content_mem_reg (s : MachineState) (reg : Reg) (value : Word) :
    (s.setReg reg value).mem=s.mem := by cases reg <;> rfl
private theorem content_mem_pc (s : MachineState) (pc : Word) : (s.setPC pc).mem=s.mem := rfl
private theorem content_mem_store (s : MachineState) (address value : Word) :
    (s.setMem address value).mem=(fun query => if query=address then value else s.mem query) := by
  funext query
  simp [MachineState.setMem]

theorem checker_first_child_memory (order : FirstSiblingOrder) (s : MachineState)
    (digest : s.getReg .x23=12288) (pair : s.getReg .x24=12544) :
    (checkerFirstChildPrefix order s 8).mem=
      (Opening.fourWordStore s 12288 (12544+BitVec.ofNat 64 order.childOffset)).mem := by
  cases order
  all_goals simp [checkerFirstChildPrefix,checkerFirstChildOps,FirstSiblingOrder.childOffset,
    Opening.fourWordStore,execInstrBr,digest,pair,content_reg_mem,signExtend12,
    content_mem_reg,content_mem_pc,content_mem_store,MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq]

theorem checker_first_child_word (order : FirstSiblingOrder) (s : MachineState)
    (digest : s.getReg .x23=12288) (pair : s.getReg .x24=12544) (word : Fin 4) :
    (checkerFirstChildPrefix order s 8).getMem
      (12544+BitVec.ofNat 64 (order.childOffset+8*word.val))=s.getMem (12288+BitVec.ofNat 64 (8*word.val)) := by
  have stored := Checker.four_word_store_word s 12288 (12544+BitVec.ofNat 64 order.childOffset)
    (1568+order.childOffset/8) (by cases order <;> rfl) (by cases order <;> decide) word
  simpa only [MachineState.getMem,checker_first_child_memory order s digest pair,BitVec.ofNat_add,BitVec.add_assoc] using stored

theorem checker_first_child_outside (order : FirstSiblingOrder) (s : MachineState)
    (digest : s.getReg .x23=12288) (pair : s.getReg .x24=12544) (query : Word)
    (away : ∀ word : Fin 4, query≠12544+BitVec.ofNat 64 (order.childOffset+8*word.val)) :
    (checkerFirstChildPrefix order s 8).getMem query=s.getMem query := by
  have frame := Opening.four_word_store_outside s 12288 (12544+BitVec.ofNat 64 order.childOffset) query
    (by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using away)
  simpa only [MachineState.getMem,checker_first_child_memory order s digest pair] using frame

theorem checker_child_mask_words (site : CheckerHashSite) (s : MachineState)
    (source : s.getReg site.childReg=12544) (word : Fin 8) :
    (checkerChildMaskPrefix site s 9).getMem (12544+BitVec.ofNat 64 (8*word.val))=
      if word.val=3 ∨ word.val=7 then (s.getMem (12544+BitVec.ofNat 64 (8*word.val)) <<< 18) >>> 18
      else s.getMem (12544+BitVec.ofNat 64 (8*word.val)) := by
  cases site <;> fin_cases word
  all_goals simp only [CheckerHashSite.childReg] at source
  all_goals simp [checkerChildMaskPrefix,checkerChildMaskOps,CheckerHashSite.childReg,execInstrBr,source,
    MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,content_reg_mem,signExtend12,
    MachineState.getMem,content_mem_pc,content_mem_reg,content_mem_store]

theorem lower_buffer_bytes (left right : MachineState) (target source count : Nat)
    (same : ∀ i, i<count → left.getByte (BitVec.ofNat 64 (target+i))=right.getByte (BitVec.ofNat 64 (source+i))) :
    readBuffer left target count=readBuffer right source count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro i inside
  rw [same i (Finset.mem_range.mp inside)]

theorem checker_copy_buffer (site : CheckerCopySite) (s : MachineState) (source target : Nat)
    (ready : TwoPermutationPrototype.Packed.CopyReady (checkerCopyCode site) s source target 0) (ordered : target≤source) :
    readBuffer (checkerCopyState site s) target (2*site.count)=readBuffer s source (2*site.count) :=
  lower_buffer_bytes _ _ _ _ _ (checker_copy_bytes site s source target ready ordered).1

theorem checker_copy_buffer_outside (site : CheckerCopySite) (s : MachineState) (source target address count : Nat)
    (ready : TwoPermutationPrototype.Packed.CopyReady (checkerCopyCode site) s source target 0) (ordered : target≤source)
    (bounded : address+count≤2^64) (separate : target+2*site.count≤address ∨ address+count≤target) :
    readBuffer (checkerCopyState site s) address count=readBuffer s address count := by
  apply lower_buffer_bytes
  intro i inside
  apply (checker_copy_bytes site s source target ready ordered).2
  intro j small
  have room : target+2*site.count≤2^64 := ready.dstBound.trans (by decide)
  exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

theorem checker_first_sibling_memory (s : MachineState) : (checkerFirstSiblingState s).mem=s.mem := by
  have branch (t : MachineState) (left right : Reg) (offset : BitVec 13) :
      (execInstrBr t (.BEQ left right offset)).mem=t.mem := by
    change MachineState.mem (if t.getReg left==t.getReg right then t.setPC (t.pc+signExtend13 offset) else t.setPC (t.pc+4))=t.mem
    split_ifs <;> rfl
  have addi (t : MachineState) (rd rs : Reg) (offset : BitVec 12) :
      (execInstrBr t (.ADDI rd rs offset)).mem=t.mem := by
    exact content_mem_reg t rd (t.getReg rs+signExtend12 offset)
  have andi (t : MachineState) : (execInstrBr t (.ANDI .x7 .x6 1)).mem=t.mem := rfl
  rw [checker_first_sibling_eq]
  rw [checkerLowerChoicePrefix]
  change (execInstrBr (execInstrBr (execInstrBr (checkerLowerGatePrefix s 2) (.ADDI .x30 .x0 32)) (.ANDI .x7 .x6 1)) (.BEQ .x7 .x0 168)).mem=s.mem
  rw [branch,andi,addi,checkerLowerGatePrefix]
  change (execInstrBr (execInstrBr s (.ADDI .x30 .x0 16)) (.BEQ .x29 .x30 336)).mem=s.mem
  rw [branch,addi]

theorem checker_first_child_buffer (order : FirstSiblingOrder) (s : MachineState)
    (digest : s.getReg .x23=12288) (pair : s.getReg .x24=12544) :
    readBuffer (checkerFirstChildPrefix order s 8) (12544+order.childOffset) 32=readBuffer s 12288 32 := by
  apply output_ext_words
  intro i
  rw [read_digest_word _ _ _ (by cases order <;> decide) i.isLt,read_digest_word _ _ _ (by decide) i.isLt]
  simpa only [BitVec.ofNat_add,show BitVec.ofNat 64 12544=(12544 : Word) from rfl,
    show BitVec.ofNat 64 12288=(12288 : Word) from rfl,BitVec.add_assoc] using
    checker_first_child_word order s digest pair i

theorem checker_first_child_buffer_outside (order : FirstSiblingOrder) (s : MachineState)
    (digest : s.getReg .x23=12288) (pair : s.getReg .x24=12544) (address : Nat)
    (aligned : address%8=0) (bounded : address+32≤2^64)
    (separate : 12544+order.childOffset+32≤address ∨ address+32≤12544+order.childOffset) :
    readBuffer (checkerFirstChildPrefix order s 8) address 32=readBuffer s address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i inside
  apply checker_first_child_outside order s digest pair
  intro j
  rw [show (12544 : Word)=BitVec.ofNat 64 12544 from rfl,←BitVec.ofNat_add]
  have range : order.childOffset≤32 := by cases order <;> decide
  exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

theorem checker_first_child_buffer_above (order : FirstSiblingOrder) (s : MachineState)
    (digest : s.getReg .x23=12288) (pair : s.getReg .x24=12544) (address : Nat)
    (above : 32768≤address) (bounded : address+32≤2^64) :
    readBuffer (checkerFirstChildPrefix order s 8) address 32=readBuffer s address 32 := by
  apply TwoPermutationPrototype.Packed.Checker.read_buffer_above s _ address 32 4096 above bounded
  intro word low high
  change (checkerFirstChildPrefix order s 8).getMem (wordAddress word)=s.getMem (wordAddress word)
  apply checker_first_child_outside order s digest pair
  intro j
  change BitVec.ofNat 64 (8*word)≠12544+BitVec.ofNat 64 (order.childOffset+8*j.val)
  rw [show (12544 : Word)=BitVec.ofNat 64 12544 from rfl,←BitVec.ofNat_add]
  have range : order.childOffset≤32 := by cases order <;> decide
  have := j.isLt
  exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

theorem checker_first_ordered_buffers {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) :
    readBuffer (checkerFirstOrderedState s) 12544 32=
      (if s.getReg .x6 &&& 1=0 then readBuffer s 12288 32 else readBuffer s (base.value+16) 32) ∧
    readBuffer (checkerFirstOrderedState s) 12576 32=
      (if s.getReg .x6 &&& 1=0 then readBuffer s (base.value+16) 32 else readBuffer s 12288 32) := by
  have baseAbove := base.above
  have baseRoom : base.value+528≤2^36 := base.room
  have baseEven := base.even
  have digest : (checkerFirstSiblingState s).getReg .x23=12288 :=
    (checker_first_sibling_register s .x23 (by first | decide +kernel | omega) (by first | decide +kernel | omega)).trans ready.digest
  have pair : (checkerFirstSiblingState s).getReg .x24=12544 :=
    (checker_first_sibling_register s .x24 (by first | decide +kernel | omega) (by first | decide +kernel | omega)).trans ready.pair
  have siblingBuffer (address : Nat) : readBuffer (checkerFirstSiblingState s) address 32=readBuffer s address 32 :=
    read_buffer_memory_congr _ _ (checker_first_sibling_memory s) address 32
  rw [checkerFirstOrderedState]
  by_cases even : s.getReg .x6 &&& 1=0
  · simp only [even,ite_true]
    have copied := checker_first_even_copy_ready input s ready even
    have currentBytes : readBuffer (checkerFirstChildPrefix .even (checkerFirstSiblingState s) 8) 12544 32=
        readBuffer (checkerFirstSiblingState s) 12288 32 := by
      simpa only [FirstSiblingOrder.childOffset,Nat.add_zero] using checker_first_child_buffer .even _ digest pair
    have siblingBytes : readBuffer (checkerCopyState .firstEven (checkerFirstChildPrefix .even (checkerFirstSiblingState s) 8)) 12576 32=
        readBuffer (checkerFirstChildPrefix .even (checkerFirstSiblingState s) 8) (base.value+16) 32 := by
      simpa only [CheckerCopySite.count,Nat.reduceMul] using checker_copy_buffer .firstEven _ (base.value+16) 12576 copied (by first | decide +kernel | omega)
    constructor
    · rw [checker_copy_buffer_outside .firstEven _ (base.value+16) 12576 12544 32 copied
        (by first | decide +kernel | omega) (by first | decide +kernel | omega) (Or.inr (by omega)),
        currentBytes,siblingBuffer]
    · rw [siblingBytes,
        checker_first_child_buffer_above .even _ digest pair (base.value+16)
          (by omega) (by omega),siblingBuffer]
  · simp only [even,ite_false]
    have copied := checker_first_odd_copy_ready input s ready even
    have copyDigest : (checkerCopyState .firstOdd (checkerFirstSiblingState s)).getReg .x23=12288 :=
      (checker_copy_register _ _ _ (by first | decide +kernel | omega)).trans digest
    have copyPair : (checkerCopyState .firstOdd (checkerFirstSiblingState s)).getReg .x24=12544 :=
      (checker_copy_register _ _ _ (by first | decide +kernel | omega)).trans pair
    have siblingBytes : readBuffer (checkerCopyState .firstOdd (checkerFirstSiblingState s)) 12544 32=
        readBuffer (checkerFirstSiblingState s) (base.value+16) 32 := by
      simpa only [CheckerCopySite.count,Nat.reduceMul] using checker_copy_buffer .firstOdd _ (base.value+16) 12544 copied (by first | decide +kernel | omega)
    have currentBytes : readBuffer (checkerFirstChildPrefix .odd (checkerCopyState .firstOdd (checkerFirstSiblingState s)) 8) 12576 32=
        readBuffer (checkerCopyState .firstOdd (checkerFirstSiblingState s)) 12288 32 := by
      simpa only [FirstSiblingOrder.childOffset,Nat.reduceAdd] using checker_first_child_buffer .odd _ copyDigest copyPair
    have jump (t : MachineState) (address : Nat) : readBuffer (execInstrBr t (.JAL .x0 164)) address 32=readBuffer t address 32 := rfl
    simp only [jump]
    constructor
    · rw [checker_first_child_buffer_outside .odd _ copyDigest copyPair 12544 (by first | decide +kernel | omega) (by first | decide +kernel | omega) (Or.inr (by first | decide +kernel | omega)),
        siblingBytes,siblingBuffer]
    · rw [currentBytes,
        checker_copy_buffer_outside .firstOdd _ (base.value+16) 12544 12288 32 copied
          (by first | decide +kernel | omega) (by first | decide +kernel | omega) (Or.inr (by omega)),siblingBuffer]

theorem checker_first_hash_word (s : MachineState) (pair : s.getReg .x24=12544) (word : Fin 8) :
    (checkerFirstHashState s).getMem (12544+BitVec.ofNat 64 (8*word.val))=
      if word.val=3 ∨ word.val=7 then (s.getMem (12544+BitVec.ofNat 64 (8*word.val)) <<< 18) >>> 18
      else s.getMem (12544+BitVec.ofNat 64 (8*word.val)) := by
  have abi (t : MachineState) : (checkerHashABIPrefix t 5).mem=t.mem := by rw [checkerHashABIPrefix]; rfl
  have branch (t : MachineState) : (execInstrBr t (.BLTU .x17 .x30 36)).mem=t.mem := by
    change MachineState.mem (if (t.getReg .x17).ult (t.getReg .x30) then t.setPC (t.pc+signExtend13 36) else t.setPC (t.pc+4))=t.mem
    split_ifs <;> rfl
  have schedule (t : MachineState) : (checkerFirstSchedulePrefix t 7).mem=t.mem := by
    simp only [checkerFirstSchedulePrefix,checkerFirstScheduleOps,List.take,List.foldl,branch]
    rfl
  have memory : (checkerFirstHashState s).mem=(checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).mem := by
    rw [checker_first_hash_eq,abi,schedule]
  change (checkerFirstHashState s).mem _=_
  rw [memory]
  change (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).getMem _=_
  rw [checker_child_mask_words .lower _ (by
      change (checkerSnapshotPrefix 31 s).getReg .x24=12544
      rw [checker_snapshot_register 31 s (by omega)]
      exact pair),
    checker_snapshot_memory_frame 31 s (by omega) _ (by
      intro slot
      rw [show (12544 : Word)=BitVec.ofNat 64 12544 from rfl,←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega))]

theorem lower_child_word (value : Output) (word : Fin 4) :
    childWord (value.setWidth 238) word.val=
      if word.val=3 then (value.extractLsb' (64*word.val) 64 <<< 18) >>> 18
      else value.extractLsb' (64*word.val) 64 := by
  fin_cases word <;> apply BitVec.eq_of_getLsbD_eq <;> intro bit inside
  all_goals simp only [childWord,Fin.reduceFinMk,Nat.reduceMul,Nat.reduceEqDiff,↓reduceIte,
    BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft]
  all_goals simp [show bit<64 by omega,show bit<238 by omega,show 64+bit<238 by omega,
    show 128+bit<238 by omega,show (192+bit<238)↔(18+bit<64) by omega]

theorem checker_first_hash_children (s : MachineState) (pair : s.getReg .x24=12544) (word : Fin 8) :
    (checkerFirstHashState s).getMem (12544+BitVec.ofNat 64 (8*word.val))=
      if word.val<4 then childWord ((readBuffer s 12544 32).setWidth 238) word.val
      else childWord ((readBuffer s 12576 32).setWidth 238) (word.val-4) := by
  have left (i : Fin 4) :
      (checkerFirstHashState s).getMem (12544+BitVec.ofNat 64 (8*i.val))=
        childWord ((readBuffer s 12544 32).setWidth 238) i.val := by
    rw [checker_first_hash_word s pair ⟨i.val,by omega⟩,lower_child_word _ i,
      read_digest_word s 12544 i.val (by decide) i.isLt]
    simp only [show i.val≠7 by omega,or_false,BitVec.ofNat_add,show BitVec.ofNat 64 12544=(12544 : Word) from rfl]
  have right (i : Fin 4) :
      (checkerFirstHashState s).getMem (12544+BitVec.ofNat 64 (8*(i.val+4)))=
        childWord ((readBuffer s 12576 32).setWidth 238) i.val := by
    have address : (12544 : Word)+BitVec.ofNat 64 (8*(i.val+4))=12576+BitVec.ofNat 64 (8*i.val) := by
      change BitVec.ofNat 64 12544+BitVec.ofNat 64 (8*(i.val+4))=BitVec.ofNat 64 12576+BitVec.ofNat 64 (8*i.val)
      rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
      congr 1
      omega
    rw [checker_first_hash_word s pair ⟨i.val+4,by omega⟩,address,lower_child_word _ i,
      read_digest_word s 12576 i.val (by decide) i.isLt]
    simp only [show i.val+4≠3 by omega,false_or,show (i.val+4=7)↔i.val=3 by omega,
      BitVec.ofNat_add,show BitVec.ofNat 64 12576=(12576 : Word) from rfl]
  fin_cases word <;> simp only [Fin.reduceFinMk,Nat.reduceLT,↓reduceIte,Nat.reduceSub]
  all_goals first | exact left 0 | exact left 1 | exact left 2 | exact left 3 | exact right 0 | exact right 1 | exact right 2 | exact right 3

def checkerFirstLeft (s : MachineState) (recordBase : Nat := checkingRawBase) : BitVec 238 :=
  (if s.getReg .x6 &&& 1=0 then readBuffer s 12288 32 else readBuffer s (recordBase+16) 32).setWidth 238
def checkerFirstRight (s : MachineState) (recordBase : Nat := checkingRawBase) : BitVec 238 :=
  (if s.getReg .x6 &&& 1=0 then readBuffer s (recordBase+16) 32 else readBuffer s 12288 32).setWidth 238

theorem checker_first_sibling_hash_children {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) (word : Fin 8) :
    (checkerFirstHashState (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3)).getMem
      ((checkerFirstHashState (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3)).getReg .x14+BitVec.ofNat 64 (8*word.val))=
      if word.val<4 then childWord (checkerFirstLeft s base.value) word.val else childWord (checkerFirstRight s base.value) (word.val-4) := by
  rw [(checker_first_sibling_hash_prepared input s ready).source]
  have pair : (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg .x24=12544 := by
    rw [checker_first_hash_call_register _ _ (by decide) (by decide) (by decide),
      checker_first_ordered_register _ _ (by decide) (by decide) (by decide)]
    exact ready.pair
  rw [checker_first_hash_children _ pair]
  have memory : (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).mem=(checkerFirstOrderedState s).mem := by
    rw [checkerFirstHashCallPrefix]; rfl
  rw [read_buffer_memory_congr _ _ memory 12544 32,read_buffer_memory_congr _ _ memory 12576 32,
    (checker_first_ordered_buffers input s ready).1,(checker_first_ordered_buffers input s ready).2]
  rfl

theorem checker_first_sibling_hash_content {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) :
    (do let out ← checkerFirstSiblingHashTrace s; pure (readBuffer out 256 32))=
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first ⟨0,by decide⟩ (checkerFirstRight s base.value ++ checkerFirstLeft s base.value))))) : OracleComp World Output)
          let value ← continuationTrace ⟨0,by decide⟩ 0 3 answer
          pure (finalValue ⟨0,by decide⟩ value)) := by
  rw [checker_first_sibling_hash_eq]
  have prepared := checker_first_sibling_hash_prepared input s ready
  exact checker_hash_content .lower 3 (by decide) _ prepared.args ⟨0,by decide⟩ _ _ prepared.height prepared.mask
    (checker_first_sibling_hash_children input s ready)

def checkerDecodedFirstSibling : InteriorCodec.Record → BitVec 238
  | .cons _ (.cons sibling _) => sibling

theorem checker_record_raw_sibling_byte (record : InteriorCodec.Record) (index : Nat) (inside : index<32) :
    (rawFieldsBytes (recordRawFields record)).getD (16+index) 0=
      (checkerDecodedFirstSibling record).extractLsb' (8*index) 8 := by
  cases record with
  | cons nonce tail =>
    cases tail with
    | cons sibling tail =>
      change ((cachedRawField 120 1 nonce 0 (by decide) (by decide)).bytes++
        ((cachedRawField 232 6 sibling 2 (by decide) (by decide)).bytes++_)).getD (16+index) 0=_
      have nonceLength : (cachedRawField 120 1 nonce 0 (by decide) (by decide)).bytes.length=16 := by
        rw [cached_raw_field_bytes 120 1 nonce 0 (by decide) (by decide) (by decide)]
        rfl
      have siblingLength : (cachedRawField 232 6 sibling 2 (by decide) (by decide)).bytes.length=32 := by
        rw [cached_raw_field_bytes 232 6 sibling 2 (by decide) (by decide) (by decide)]
        rfl
      rw [List.getD_append_right _ _ 0 (16+index) (by omega),nonceLength,Nat.add_sub_cancel_left,
        List.getD_append _ _ 0 index (by omega),cached_raw_field_byte 232 6 sibling 2 index
          (by decide) (by decide) (by decide) inside]
      rfl

theorem checker_decoded_first_sibling (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    readBuffer s (checkingRawBase+16) 32=(checkerDecodedFirstSibling (checkerFirstDecodedRecord input)).setWidth 256 := by
  have bytes (index : Nat) (inside : index<32) :
      s.getByte (BitVec.ofNat 64 (checkingRawBase+16+index))=
        (checkerDecodedFirstSibling (checkerFirstDecodedRecord input)).extractLsb' (8*index) 8 := by
    have bound : 16+index<(rawFieldsBytes (recordRawFields (checkerFirstDecodedRecord input))).length := by
      rw [record_raw_fields_length]; omega
    have memory := checker_decoded_head_memory input nonempty footer s ready (16+index) bound
    rw [←BitVec.ofNat_add] at memory
    rw [show checkingRawBase+16+index=checkingRawBase+(16+index) by omega,memory]
    have raw := checker_record_raw_sibling_byte (checkerFirstDecodedRecord input) index inside
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using raw
  have decoded := read_serialized_slice s (checkerDecodedFirstSibling (checkerFirstDecodedRecord input))
    (checkingRawBase+16) 0 32 (by intro index inside; simpa only [Nat.zero_add] using bytes index inside)
  apply decoded.trans
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth]

theorem checker_first_path_sibling (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (a b : Block) :
    readBuffer (checkerLeafPathState (secondReplyState (checkerRecordNonceState s) 754975239 a b))
      (checkingRawBase+16) 32=(checkerDecodedFirstSibling (checkerFirstDecodedRecord input)).setWidth 256 := by
  have low : 2^33≤checkingRawBase := by decide +kernel
  have high : checkingRawBase+48<2^36 := by decide +kernel
  have aligned : (checkingRawBase+16)%8=0 := by decide +kernel
  have baseAligned : checkingRawBase%8=0 := by decide +kernel
  have place (i : Nat) : wordAddress (checkingRawBase/8+2+i)=BitVec.ofNat 64 (checkingRawBase+16+8*i) := by
    have numeric : 8*(checkingRawBase/8+2+i)=checkingRawBase+16+8*i := by omega
    exact congrArg (BitVec.ofNat 64) numeric
  have nonceBuffer : readBuffer (checkerRecordNonceState s) (checkingRawBase+16) 32=readBuffer s (checkingRawBase+16) 32 := by
    rw [checker_record_nonce_eq,checker_copy_buffer_outside .nonce _ checkingRawBase 12272 (checkingRawBase+16) 32
      (checker_record_nonce_ready input footer s ready) (by decide +kernel) (by omega) (Or.inl (by simp only [CheckerCopySite.count]; omega))]
    apply read_digest_congr _ _ _ aligned
    intro i inside
    rw [checker_leaf_head_memory 7 _ (by omega)]
    apply checker_crypto_record_memory
    intro node small
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  have args := checker_record_leaf_ready input nonempty footer s ready
  have leafBuffer : readBuffer (secondReplyState (checkerRecordNonceState s) 754975239 a b) (checkingRawBase+16) 32=
      readBuffer (checkerRecordNonceState s) (checkingRawBase+16) 32 := by
    apply read_digest_congr _ _ _ aligned
    intro i inside
    have frame := checker_leaf_frame args a b (checkingRawBase/8+2+i) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    change (secondReplyState (checkerRecordNonceState s) 754975239 a b).getMem (wordAddress (checkingRawBase/8+2+i))=
      (checkerRecordNonceState s).getMem (wordAddress (checkingRawBase/8+2+i)) at frame
    rwa [place] at frame
  have destination : (secondReplyState (checkerRecordNonceState s) 754975239 a b).getReg .x23=12288 :=
    (checker_leaf_preserved_register _ _ _ _ .x23 (by decide) (by decide) (by decide)).trans args.destination
  have pathBuffer : readBuffer (checkerLeafPathState (secondReplyState (checkerRecordNonceState s) 754975239 a b)) (checkingRawBase+16) 32=
      readBuffer (secondReplyState (checkerRecordNonceState s) 754975239 a b) (checkingRawBase+16) 32 := by
    rw [checker_leaf_path_eq]
    apply read_digest_congr _ _ _ aligned
    intro i inside
    have frame := trunc_lower_frame _ destination (checkingRawBase/8+2+i) (by omega) (by omega)
    change (truncLower _).getMem (wordAddress (checkingRawBase/8+2+i))=
      (secondReplyState (checkerRecordNonceState s) 754975239 a b).getMem (wordAddress (checkingRawBase/8+2+i)) at frame
    rwa [place] at frame
  exact pathBuffer.trans (leafBuffer.trans (nonceBuffer.trans (checker_decoded_first_sibling input nonempty footer s ready)))

theorem checker_first_path_children (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (a b : Block) :
    let out := checkerLeafPathState (secondReplyState (checkerRecordNonceState s) 754975239 a b)
    let leaf := (outputDigest b).setWidth 238
    let sibling := checkerDecodedFirstSibling (checkerFirstDecodedRecord input)
    checkerFirstLeft out=(if out.getReg .x6 &&& 1=0 then leaf else sibling) ∧
    checkerFirstRight out=(if out.getReg .x6 &&& 1=0 then sibling else leaf) := by
  dsimp only
  have leaf := checker_leaf_path_digest (checker_record_leaf_ready input nonempty footer s ready) a b
  have sibling := checker_first_path_sibling input nonempty footer s ready a b
  simp only [checkerFirstLeft,checkerFirstRight]
  split_ifs <;> rw [leaf,sibling]
  all_goals constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_mod_of_dvd _ (by decide : 2^238∣2^256),Nat.mod_mod,
      Nat.mod_eq_of_lt (checkerDecodedFirstSibling (checkerFirstDecodedRecord input)).isLt]

end CommitGolfCandidate.Chained.Native.RecordLeaf

/-! Height-indexed delivered lower-wrapper schedule, including its exceptional rows. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
@[local simp] private theorem schedule_zero (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem schedule_pc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem schedule_set_zero (s : MachineState) (value : Word) : s.setReg .x0 value=s := rfl

def checkerLowerScheduleOps (height : Fin 16) : List Instr := checkerFirstScheduleOps++
  if height.val<8 then [] else [.BEQ .x17 .x30 24]++
    if height.val=8 then [.ADDI .x18 .x0 5,.SRLI .x16 .x16 1] else
      [.ADDI .x30 .x0 15,.BGEU .x17 .x30 24]++
        if height.val=15 then [] else [.ADDI .x18 .x0 7,.SRLI .x16 .x16 2,.JAL .x0 12]

def checkerLowerScheduleInstructions (height : Fin 16) : Nat :=
  if height.val<8 then 7 else if height.val=8 ∨ height.val=15 then 10 else 13
def checkerLowerRemaining (height : Fin 16) : Nat :=
  if height.val<8 ∨ height.val=15 then 3 else if height.val=8 then 5 else 7

@[irreducible] def checkerLowerSchedulePrefix (height : Fin 16) (s : MachineState) (n : Nat) : MachineState :=
  ((checkerLowerScheduleOps height).take n).foldl execInstrBr s

def checkerLowerScheduleIndex (height : Fin 16) (step : Nat) : Nat :=
  if step=checkerLowerScheduleInstructions height then 2812
  else if height.val=8 ∧ 8≤step then 2802+step else 2797+step

theorem checker_lower_schedule_zero (height : Fin 16) (s : MachineState) : checkerLowerSchedulePrefix height s 0=s := by
  rw [checkerLowerSchedulePrefix]; rfl
theorem checker_lower_schedule_succ (height : Fin 16) (s : MachineState) (n : Nat)
    (inside : n<(checkerLowerScheduleOps height).length) :
    checkerLowerSchedulePrefix height s (n+1)=execInstrBr (checkerLowerSchedulePrefix height s n) ((checkerLowerScheduleOps height).getD n .EBREAK) := by
  rw [checkerLowerSchedulePrefix,checkerLowerSchedulePrefix,List.take_succ_eq_append_getElem inside,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some]

theorem checker_lower_schedule_length (height : Fin 16) :
    (checkerLowerScheduleOps height).length=checkerLowerScheduleInstructions height := by
  revert height
  decide +kernel

theorem checker_lower_remaining_calls (height : Fin 16) :
    checkerLowerRemaining height+1=calls ⟨height.val,by omega⟩ := by revert height; decide +kernel

theorem checker_lower_schedule_opcode (height : Fin 16) (step : Fin 13)
    (inside : step.val<checkerLowerScheduleInstructions height) :
    chainedCheckerOps.getD (checkerLowerScheduleIndex height step.val) .EBREAK=(checkerLowerScheduleOps height).getD step.val .EBREAK := by
  revert height step
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem checker_lower_schedule_pc (height : Fin 16) (s : MachineState)
    (counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)) (pc : s.pc=4096+4*2797)
    (n : Nat) (small : n≤checkerLowerScheduleInstructions height) :
    (checkerLowerSchedulePrefix height s n).pc=BitVec.ofNat 64 (4096+4*checkerLowerScheduleIndex height n) := by
  fin_cases height
  all_goals simp only [Fin.reduceFinMk,Nat.reduceSub] at counter
  all_goals norm_num [checkerLowerScheduleInstructions] at small
  all_goals interval_cases n
  all_goals simp [checkerLowerSchedulePrefix,checkerLowerScheduleOps,checkerLowerScheduleInstructions,
    checkerLowerScheduleIndex,checkerFirstScheduleOps,execInstrBr,counter,pc,
    MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,signExtend12,signExtend13,signExtend21]

theorem checker_lower_schedule_values (height : Fin 16) (s : MachineState)
    (counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)) (pc : s.pc=4096+4*2797) :
    let out := checkerLowerSchedulePrefix height s (checkerLowerScheduleInstructions height)
    out.getReg .x17=BitVec.ofNat 64 height.val ∧
    out.getReg .x18=BitVec.ofNat 64 (checkerLowerRemaining height) ∧
    out.getReg .x16=finalMask ⟨height.val,by omega⟩ ∧ out.pc=4096+4*2812 := by
  fin_cases height
  all_goals simp only [Fin.reduceFinMk,Nat.reduceSub] at counter
  all_goals simp [checkerLowerSchedulePrefix,checkerLowerScheduleOps,checkerLowerScheduleInstructions,
    checkerLowerRemaining,checkerFirstScheduleOps,execInstrBr,counter,pc,
    MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,signExtend12,signExtend13,
    signExtend21,finalMask,width]

theorem checker_lower_schedule_ordinary (height : Fin 16) (step : Fin 13)
    (inside : step.val<checkerLowerScheduleInstructions height) (s : MachineState) :
    ordinaryStep s (.base ((checkerLowerScheduleOps height).getD step.val .EBREAK))=
      some (execInstrBr s ((checkerLowerScheduleOps height).getD step.val .EBREAK)) ∧
    instructionCycles (.base ((checkerLowerScheduleOps height).getD step.val .EBREAK))=1 := by
  fin_cases height <;> fin_cases step <;> norm_num [checkerLowerScheduleInstructions] at inside <;> exact ⟨rfl,rfl⟩

theorem checker_lower_schedule_execution (height : Fin 16) (s : MachineState)
    (counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)) (pc : s.pc=4096+4*2797)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerLowerScheduleInstructions height+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel
            (checkerLowerSchedulePrefix height s (checkerLowerScheduleInstructions height)) coins
          return result.charge (checkerLowerScheduleInstructions height) 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_lower_schedule_zero height s]
  apply execute_unit_steps (states := checkerLowerSchedulePrefix height s)
  intro i inside
  have length : checkerLowerScheduleInstructions height≤13 := by unfold checkerLowerScheduleInstructions; split_ifs <;> omega
  have ordinary := checker_lower_schedule_ordinary height ⟨i,by omega⟩ inside (checkerLowerSchedulePrefix height s i)
  refine ⟨.base ((checkerLowerScheduleOps height).getD i .EBREAK),?_,?_,ordinary.2⟩
  · rw [←checker_lower_schedule_opcode height ⟨i,by omega⟩ inside]
    apply chained_checker_ops_at
    · rw [chained_checker_ops_length]
      unfold checkerLowerScheduleIndex
      split_ifs <;> omega
    · have position := checker_lower_schedule_pc height s counter pc i (by omega)
      simpa only [BitVec.ofNat_add,show BitVec.ofNat 64 4096=(4096 : Word) from rfl] using position
  · rw [checker_lower_schedule_succ height s i (by rw [checker_lower_schedule_length]; exact inside)]
    exact ordinary.1

theorem checker_lower_schedule_register (height : Fin 16) (s : MachineState)
    (counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)) (reg : Reg)
    (level : reg≠.x17) (count : reg≠.x18) (mask : reg≠.x16) (temp : reg≠.x30) :
    (checkerLowerSchedulePrefix height s (checkerLowerScheduleInstructions height)).getReg reg=s.getReg reg := by
  fin_cases height
  all_goals simp only [Fin.reduceFinMk,Nat.reduceSub] at counter
  all_goals simp [checkerLowerSchedulePrefix,checkerLowerScheduleOps,checkerLowerScheduleInstructions,
    checkerFirstScheduleOps,execInstrBr,counter,Ne.symm level,Ne.symm count,Ne.symm mask,Ne.symm temp,
    MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,signExtend12]

@[irreducible] def checkerLowerHashState (height : Fin 16) (s : MachineState) : MachineState :=
  checkerHashABIPrefix (checkerLowerSchedulePrefix height
    (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9) (checkerLowerScheduleInstructions height)) 5

structure CheckerLowerHashReady (level : Fin 16) (s : MachineState) : Prop where
  pc : s.pc=CheckerHashSite.lower.base
  args : LoopArgs s 256
  remaining : s.getReg .x18=BitVec.ofNat 64 (checkerLowerRemaining level)
  height : s.getReg .x17=BitVec.ofNat 64 level.val
  mask : s.getReg .x16=finalMask ⟨level.val,by omega⟩
  source : s.getReg .x14=12544

theorem checker_lower_hash_ready (height : Fin 16) (s : MachineState)
    (pc : s.pc=4096+4*2757) (pair : s.getReg .x24=12544)
    (counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)) :
    CheckerLowerHashReady height (checkerLowerHashState height s) := by
  have snapPC : (checkerSnapshotPrefix 31 s).pc=4096+4*2788 := by
    rw [checker_snapshot_pc _ _ (by omega),pc]; rfl
  have maskPC : (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).pc=4096+4*2797 := by
    rw [checker_child_mask_pc _ _ _ (by omega),snapPC]; rfl
  have maskCounter : (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).getReg .x29=BitVec.ofNat 64 (16-height.val) := by
    rw [checker_child_mask_register _ _ _ (by omega) _ (by decide) (by decide),checker_snapshot_register _ _ (by omega),counter]
  have values := checker_lower_schedule_values height _ maskCounter maskPC
  rw [checkerLowerHashState]
  refine ⟨checker_hash_abi_pc _ values.2.2.2,checker_hash_abi_args _,?_,?_,?_,?_⟩
  · rw [checker_hash_abi_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact values.2.1
  · rw [checker_hash_abi_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact values.1
  · rw [checker_hash_abi_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact values.2.2.1
  · rw [checker_hash_abi_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checker_lower_schedule_register height _ maskCounter _ (by decide) (by decide) (by decide) (by decide),
      checker_child_mask_source _ _ _ (by omega) (by omega),checker_snapshot_register _ _ (by omega)]
    exact pair

theorem checker_lower_hash_setup_execution (height : Fin 16) (s : MachineState)
    (pc : s.pc=4096+4*2757) (pair : s.getReg .x24=12544)
    (counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (45+checkerLowerScheduleInstructions height+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLowerHashState height s) coins
          return result.charge (45+checkerLowerScheduleInstructions height) 0) := by
  have snapPC : (checkerSnapshotPrefix 31 s).pc=4096+4*2788 := by
    rw [checker_snapshot_pc _ _ (by omega),pc]; rfl
  have maskPC : (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).pc=4096+4*2797 := by
    rw [checker_child_mask_pc _ _ _ (by omega),snapPC]; rfl
  have maskCounter : (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).getReg .x29=BitVec.ofNat 64 (16-height.val) := by
    rw [checker_child_mask_register _ _ _ (by omega) _ (by decide) (by decide),checker_snapshot_register _ _ (by omega),counter]
  rw [show 45+checkerLowerScheduleInstructions height+fuel=31+(9+(checkerLowerScheduleInstructions height+(5+fuel))) by omega,
    checker_snapshot_execution .lower s pc,
    checker_child_mask_execution .lower _ snapPC ((checker_snapshot_register _ _ (by omega) .x24).trans pair)]
  simp only [bind_assoc]
  rw [checker_lower_schedule_execution height _ maskCounter maskPC,
    checker_hash_abi_execution _ (checker_lower_schedule_values height _ maskCounter maskPC).2.2.2,checkerLowerHashState]
  simp [Execution.charge,←Nat.add_assoc,
    show 40+checkerLowerScheduleInstructions height+5=45+checkerLowerScheduleInstructions height by omega]

def checkerLowerHashInstructions (height : Fin 16) : Nat :=
  79+checkerLowerScheduleInstructions height+continuationInstructions (checkerLowerRemaining height)
def checkerLowerHashCycles (height : Fin 16) : Nat :=
  86+checkerLowerScheduleInstructions height+continuationCycles (checkerLowerRemaining height)

theorem checker_lower_hash_execution (height : Fin 16) (s : MachineState)
    (pc : s.pc=4096+4*2757) (pair : s.getReg .x24=12544)
    (counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerLowerHashInstructions height+fuel) s coins=
      (do let out ← checkerHashTrace .lower (checkerLowerRemaining height) (checkerLowerHashState height s)
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (checkerLowerHashCycles height) (calls ⟨height.val,by omega⟩)) := by
  have ready := checker_lower_hash_ready height s pc pair counter
  have small : checkerLowerRemaining height≤7 := by unfold checkerLowerRemaining; split_ifs <;> omega
  have inputs : ∀ k : Fin 8, accessValid ((checkerLowerHashState height s).getReg .x14+BitVec.ofNat 64 (8*k.val)) 8=true := by
    intro k
    rw [ready.source]
    fin_cases k <;> decide +kernel
  rw [show checkerLowerHashInstructions height+fuel=(45+checkerLowerScheduleInstructions height)+(34+continuationInstructions (checkerLowerRemaining height)+fuel) by unfold checkerLowerHashInstructions; omega,
    checker_lower_hash_setup_execution height s pc pair counter,
    artifact_checking_hash .lower _ small _ ready.args ready.pc ready.remaining inputs]
  simp only [bind_assoc]
  simp [Execution.charge,checkerLowerHashCycles,checker_lower_remaining_calls,←Nat.add_assoc,
    show 45+checkerLowerScheduleInstructions height+41=86+checkerLowerScheduleInstructions height by omega]

theorem checker_lower_schedule_memory (height : Fin 16) (s : MachineState) (query : Word) :
    (checkerLowerSchedulePrefix height s (checkerLowerScheduleInstructions height)).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Fin 13) (inside : i.val<checkerLowerScheduleInstructions height) :
      (execInstrBr t ((checkerLowerScheduleOps height).getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases height <;> fin_cases i <;> norm_num [checkerLowerScheduleInstructions] at inside
    all_goals simp only [checkerLowerScheduleOps,checkerFirstScheduleOps,Fin.reduceFinMk,Nat.reduceLT,
      Nat.reduceEqDiff,↓reduceIte,List.nil_append,List.cons_append,List.getD_cons_zero,List.getD_cons_succ]
    all_goals first | rfl | (simp only [execInstrBr]; split_ifs <;> rfl)
  have all (n : Nat) (small : n≤checkerLowerScheduleInstructions height) :
      (checkerLowerSchedulePrefix height s n).getMem query=s.getMem query := by
    induction n with
    | zero => rw [checker_lower_schedule_zero]
    | succ n ih =>
      have bound : checkerLowerScheduleInstructions height≤13 := by unfold checkerLowerScheduleInstructions; split_ifs <;> omega
      rw [checker_lower_schedule_succ height s n (by rw [checker_lower_schedule_length]; omega),
        step _ ⟨n,by omega⟩ (show n<checkerLowerScheduleInstructions height from by omega),ih (by omega)]
  exact all _ (by omega)

theorem checker_lower_hash_saved (height : Fin 16) (s : MachineState) (pair : s.getReg .x24=12544) (slot : Fin 31) :
    (checkerLowerHashState height s).getMem (checkerSaveWord slot)=s.getReg (checkerSnapshotReg slot) := by
  rw [checkerLowerHashState,checker_hash_abi_memory,checker_lower_schedule_memory,
    checker_child_mask_saved_memory .lower _ 9 (by omega)]
  · exact checker_snapshot_saved 31 s (by omega) slot slot.isLt
  · exact (checker_snapshot_register 31 s (by omega) .x24).trans pair

theorem checker_lower_hash_memory (height : Fin 16) (s : MachineState) (query : Word) :
    (checkerLowerHashState height s).getMem query=(checkerFirstHashState s).getMem query := by
  rw [checkerLowerHashState,checker_first_hash_eq,checker_hash_abi_memory,checker_hash_abi_memory,
    checker_lower_schedule_memory,checker_first_schedule_memory]

theorem checker_lower_hash_content (height : Fin 16) (s : MachineState)
    (pc : s.pc=4096+4*2757) (pair : s.getReg .x24=12544)
    (counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)) :
    (do let out ← checkerHashTrace .lower (checkerLowerRemaining height) (checkerLowerHashState height s)
        pure (readBuffer out 256 32))=
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first ⟨height.val,by omega⟩
            ((readBuffer s 12576 32).setWidth 238 ++ (readBuffer s 12544 32).setWidth 238))))) : OracleComp World Output)
          let value ← continuationTrace ⟨height.val,by omega⟩ 0 (checkerLowerRemaining height) answer
          pure (finalValue ⟨height.val,by omega⟩ value)) := by
  have ready := checker_lower_hash_ready height s pc pair counter
  have small : checkerLowerRemaining height≤7 := by unfold checkerLowerRemaining; split_ifs <;> omega
  apply checker_hash_content .lower _ small _ ready.args ⟨height.val,by omega⟩ _ _ ready.height ready.mask
  intro word
  rw [ready.source,checker_lower_hash_memory]
  exact RecordLeaf.checker_first_hash_children s pair word

end CommitGolfCandidate.Chained.Native

/-! Delivered later-height sibling dispatch and the padded 232-bit sibling path. -/
namespace CommitGolfCandidate.Chained.Native.RecordLeaf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Packed
set_option maxRecDepth 8192

@[local simp] private theorem later_zero (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem later_pc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem later_set_zero (s : MachineState) (value : Word) : s.setReg .x0 value=s := rfl

def checkerLowerCursor (height : Fin 17) (recordBase : Nat := checkingRawBase) : Nat :=
  recordBase+if height.val=0 then 16 else 48+30*(height.val-1)

structure CheckerLaterPathReady (level : Fin 16) (s : MachineState)
    (base : CheckerRecordBase := checkerDefaultRecordBase) : Prop where
  positive : 0<level.val
  pc : s.pc=4096+4*2437
  source : s.getReg .x21=BitVec.ofNat 64 (checkerLowerCursor ⟨level.val,by omega⟩ base.value)
  digest : s.getReg .x23=12288
  pair : s.getReg .x24=12544
  counter : s.getReg .x29=BitVec.ofNat 64 (16-level.val)

def checkerLaterDispatchOps : List Instr := checkerLowerGateOps++[
  .ADDI .x30 .x0 30,.ANDI .x7 .x6 1,.BEQ .x7 .x0 164]
@[irreducible] def checkerLaterDispatchPrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerLaterDispatchOps.take n).foldl execInstrBr s

theorem checker_later_counter {base : CheckerRecordBase} (height : Fin 16) (s : MachineState) (ready : CheckerLaterPathReady height s base) :
    s.getReg .x29≠16 := by
  rw [ready.counter]
  intro same
  have numeric := congrArg BitVec.toNat same
  have bound : 16-height.val<2^64 := by omega
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] at numeric
  have := ready.positive
  norm_num at numeric
  omega

theorem checker_later_dispatch_pc (s : MachineState) (pc : s.pc=4096+4*2437)
    (counter : s.getReg .x29≠16) (n : Nat) (small : n<5) :
    (checkerLaterDispatchPrefix s n).pc=4096+BitVec.ofNat 64 (4*(2437+n)) := by
  have counter' : s.getReg .x29≠16#64 := counter
  interval_cases n <;> simp [checkerLaterDispatchPrefix,checkerLaterDispatchOps,checkerLowerGateOps,
    execInstrBr,pc,counter,counter',signExtend12,signExtend13,MachineState.getReg_setPC,MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq]

theorem checker_later_dispatch_end (s : MachineState) (pc : s.pc=4096+4*2437)
    (counter : s.getReg .x29≠16) :
    (checkerLaterDispatchPrefix s 5).pc=if s.getReg .x6 &&& 1=0 then 4096+4*2482 else 4096+4*2442 := by
  have counter' : s.getReg .x29≠16#64 := counter
  simp [checkerLaterDispatchPrefix,checkerLaterDispatchOps,checkerLowerGateOps,execInstrBr,pc,counter,
    counter',signExtend12,signExtend13,MachineState.getReg_setPC,MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq]
  split_ifs <;> rfl

theorem checker_later_dispatch_register (s : MachineState) (reg : Reg) (temp : reg≠.x30) (scratch : reg≠.x7) :
    (checkerLaterDispatchPrefix s 5).getReg reg=s.getReg reg := by
  simp only [checkerLaterDispatchPrefix,checkerLaterDispatchOps,checkerLowerGateOps,List.take,List.foldl,List.cons_append,List.nil_append,
    execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm temp),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]
  split_ifs <;> simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm temp),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem checker_later_dispatch_execution (s : MachineState) (pc : s.pc=4096+4*2437)
    (counter : s.getReg .x29≠16) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (5+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLaterDispatchPrefix s 5) coins
          return result.charge 5 0) := by
  rw [checking_manifest_image]
  have zero : checkerLaterDispatchPrefix s 0=s := by rw [checkerLaterDispatchPrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerLaterDispatchPrefix s)
  intro i inside
  refine ⟨.base (checkerLaterDispatchOps.getD i .EBREAK),?_,?_,?_⟩
  · have opcode : checkerLaterDispatchOps.getD i .EBREAK=chainedCheckerOps.getD (2437+i) .EBREAK := by
      interval_cases i <;> decide +kernel
    rw [opcode]
    exact chained_checker_ops_at (2437+i) (by rw [chained_checker_ops_length]; omega)
      (checkerLaterDispatchPrefix s i) (checker_later_dispatch_pc s pc counter i inside)
  · interval_cases i <;> rw [checkerLaterDispatchPrefix,checkerLaterDispatchPrefix] <;> rfl
  · interval_cases i <;> rfl

def FirstSiblingOrder.laterChildStart : FirstSiblingOrder → Nat | .odd => 2473 | .even => 2482
def FirstSiblingOrder.laterPadStart : FirstSiblingOrder → Nat | .odd => 2472 | .even => 2520
def FirstSiblingOrder.laterPadOffset : FirstSiblingOrder → BitVec 12 | .odd => 30 | .even => 62

theorem checker_later_child_at (order : FirstSiblingOrder) (i : Nat) (small : i<8)
    (s : MachineState) (pc : s.pc=4096+BitVec.ofNat 64 (4*(order.laterChildStart+i))) :
    fetch chainedCheckerImage s=some (.base ((checkerFirstChildOps order).getD i .EBREAK)) := by
  have opcode : (checkerFirstChildOps order).getD i .EBREAK=chainedCheckerOps.getD (order.laterChildStart+i) .EBREAK := by
    cases order <;> interval_cases i <;> decide +kernel
  rw [opcode]
  exact chained_checker_ops_at (order.laterChildStart+i) (by cases order <;> rw [chained_checker_ops_length] <;> simp only [FirstSiblingOrder.laterChildStart] <;> omega) s pc

theorem checker_later_child_execution (order : FirstSiblingOrder) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*order.laterChildStart))
    (digest : s.getReg .x23=12288) (pair : s.getReg .x24=12544) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (8+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFirstChildPrefix order s 8) coins
          return result.charge 8 0) := by
  rw [checking_manifest_image]
  have zero : checkerFirstChildPrefix order s 0=s := by rw [checkerFirstChildPrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerFirstChildPrefix order s)
  intro i inside
  refine ⟨.base ((checkerFirstChildOps order).getD i .EBREAK),?_,?_,?_⟩
  · apply checker_later_child_at order i inside
    cases order <;> interval_cases i <;> simp [checkerFirstChildPrefix,checkerFirstChildOps,execInstrBr,pc,FirstSiblingOrder.laterChildStart,BitVec.add_assoc]
  · have src := (checker_first_child_register order s i (by omega) .x23 (by decide)).trans digest
    have dst := (checker_first_child_register order s i (by omega) .x24 (by decide)).trans pair
    have valid : memoryArgumentsValid (checkerFirstChildPrefix order s i) ((checkerFirstChildOps order).getD i .EBREAK)=true := by
      cases order <;> interval_cases i <;>
        simp only [checkerFirstChildOps,List.getD_cons_zero,List.getD_cons_succ,memoryArgumentsValid,memAccess,src,dst]
      all_goals decide +kernel
    cases order <;> interval_cases i
    all_goals simp only [checkerFirstChildOps,List.getD_cons_zero,List.getD_cons_succ] at valid ⊢
    all_goals simp only [ordinaryStep,valid,ite_true]
    all_goals rw [checkerFirstChildPrefix,checkerFirstChildPrefix]; rfl
  · cases order <;> interval_cases i <;> rfl

@[irreducible] def checkerLaterPadState (order : FirstSiblingOrder) (s : MachineState) : MachineState :=
  execInstrBr s (.SH .x24 .x0 order.laterPadOffset)

theorem checker_later_pad_register (order : FirstSiblingOrder) (s : MachineState) (reg : Reg) :
    (checkerLaterPadState order s).getReg reg=s.getReg reg := by
  rw [checkerLaterPadState]
  cases reg <;> rfl

theorem checker_later_pad_pc (order : FirstSiblingOrder) (s : MachineState) :
    (checkerLaterPadState order s).pc=s.pc+4 := by rw [checkerLaterPadState]; rfl

theorem checker_later_pad_execution (order : FirstSiblingOrder) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*order.laterPadStart)) (pair : s.getReg .x24=12544)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (1+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLaterPadState order s) coins
          return result.charge 1 0) := by
  have fetched := trunc_fetch s order.laterPadStart (.SH .x24 .x0 order.laterPadOffset)
    (by cases order <;> decide) pc (by cases order <;> decide +kernel)
  have valid : memoryArgumentsValid s (.SH .x24 .x0 order.laterPadOffset)=true := by
    cases order <;> simp only [memoryArgumentsValid,memAccess,pair,FirstSiblingOrder.laterPadOffset] <;> decide +kernel
  have step : ordinaryStep s (.base (.SH .x24 .x0 order.laterPadOffset))=some (checkerLaterPadState order s) := by
    rw [checkerLaterPadState]
    simp only [ordinaryStep,valid,ite_true]
  rw [show 1+fuel=fuel+1 by omega,execute_ordinary_step _ _ _ _ _ coins fetched step]
  rfl

theorem checker_lower_cursor_geometry (height : Fin 17)
    (base : CheckerRecordBase := checkerDefaultRecordBase) :
    checkerLowerCursor height base.value+30≤MEMORY_BYTES ∧ checkerLowerCursor height base.value%2=0 := by
  have room := base.room
  have even := base.even
  fin_cases height <;> simp [checkerLowerCursor,Nat.add_mod,even] <;> omega

theorem checker_later_child_pc (order : FirstSiblingOrder) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*order.laterChildStart)) :
    (checkerFirstChildPrefix order s 8).pc=BitVec.ofNat 64 (4096+4*(order.laterChildStart+8)) := by
  cases order <;> simp [checkerFirstChildPrefix,checkerFirstChildOps,execInstrBr,pc,FirstSiblingOrder.laterChildStart]
  all_goals rfl

theorem checker_later_odd_copy_ready {base : CheckerRecordBase} (height : Fin 16) (s : MachineState)
    (ready : CheckerLaterPathReady height s base) (odd : ¬s.getReg .x6 &&& 1=0) :
    CopyReady (checkerCopyCode .odd) (checkerLaterDispatchPrefix s 5)
      (checkerLowerCursor ⟨height.val,by omega⟩ base.value) 12544 0 := by
  have geometry := checker_lower_cursor_geometry ⟨height.val,by omega⟩ base
  refine ⟨?_,?_,?_,geometry.1,by decide,geometry.2,by decide⟩
  · change (checkerLaterDispatchPrefix s 5).pc=BitVec.ofNat 64 (4096+4*2442)
    rw [checker_later_dispatch_end s ready.pc (checker_later_counter height s ready),if_neg odd]
    rfl
  · exact (checker_later_dispatch_register s .x21 (by decide) (by decide)).trans ready.source
  · change (checkerLaterDispatchPrefix s 5).getReg .x24+0=BitVec.ofNat 64 12544
    rw [checker_later_dispatch_register s .x24 (by decide) (by decide),ready.pair]
    rfl

theorem checker_later_even_copy_ready {base : CheckerRecordBase} (height : Fin 16) (s : MachineState)
    (ready : CheckerLaterPathReady height s base) (even : s.getReg .x6 &&& 1=0) :
    CopyReady (checkerCopyCode .even) (checkerFirstChildPrefix .even (checkerLaterDispatchPrefix s 5) 8)
      (checkerLowerCursor ⟨height.val,by omega⟩ base.value) 12576 0 := by
  have geometry := checker_lower_cursor_geometry ⟨height.val,by omega⟩ base
  refine ⟨?_,?_,?_,geometry.1,by decide,geometry.2,by decide⟩
  · have pc : (checkerLaterDispatchPrefix s 5).pc=4096+4*2482 := by
      rw [checker_later_dispatch_end s ready.pc (checker_later_counter height s ready),if_pos even]
    exact checker_later_child_pc .even _ pc
  · rw [checker_first_child_register _ _ _ (by omega) _ (by decide),
      checker_later_dispatch_register _ _ (by decide) (by decide)]
    exact ready.source
  · change (checkerFirstChildPrefix .even (checkerLaterDispatchPrefix s 5) 8).getReg .x24+32=BitVec.ofNat 64 12576
    rw [checker_first_child_register _ _ _ (by omega) _ (by decide),
      checker_later_dispatch_register _ _ (by decide) (by decide),ready.pair]
    rfl

def FirstSiblingOrder.laterJumpStart : FirstSiblingOrder → Nat | .odd => 2481 | .even => 2521
def FirstSiblingOrder.laterJumpOffset : FirstSiblingOrder → BitVec 21 | .odd => 500 | .even => 340
@[irreducible] def checkerLaterJumpState (order : FirstSiblingOrder) (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x0 order.laterJumpOffset)

theorem checker_later_jump_register (order : FirstSiblingOrder) (s : MachineState) (reg : Reg) :
    (checkerLaterJumpState order s).getReg reg=s.getReg reg := by
  rw [checkerLaterJumpState]
  cases reg <;> rfl

theorem checker_later_jump_pc (order : FirstSiblingOrder) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*order.laterJumpStart)) :
    (checkerLaterJumpState order s).pc=4096+4*2606 := by
  rw [checkerLaterJumpState]
  change s.pc+signExtend21 order.laterJumpOffset=_
  rw [pc]
  cases order <;> rfl

theorem checker_later_jump_execution (order : FirstSiblingOrder) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*order.laterJumpStart)) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (1+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLaterJumpState order s) coins
          return result.charge 1 0) := by
  have fetched := trunc_fetch s order.laterJumpStart (.JAL .x0 order.laterJumpOffset)
    (by cases order <;> decide) pc (by cases order <;> decide +kernel)
  have step : ordinaryStep s (.base (.JAL .x0 order.laterJumpOffset))=some (checkerLaterJumpState order s) := by
    rw [checkerLaterJumpState]; rfl
  rw [show 1+fuel=fuel+1 by omega,execute_ordinary_step _ _ _ _ _ coins fetched step]
  rfl

@[irreducible] def checkerLaterOrderedState (s : MachineState) : MachineState :=
  if s.getReg .x6 &&& 1=0 then
    checkerLaterJumpState .even (checkerLaterPadState .even
      (checkerCopyState .even (checkerFirstChildPrefix .even (checkerLaterDispatchPrefix s 5) 8)))
  else checkerLaterJumpState .odd (checkerFirstChildPrefix .odd
    (checkerLaterPadState .odd (checkerCopyState .odd (checkerLaterDispatchPrefix s 5))) 8)

theorem checker_later_ordered_register (s : MachineState) (reg : Reg)
    (scratch : reg≠.x31) (stride : reg≠.x30) (parity : reg≠.x7) :
    (checkerLaterOrderedState s).getReg reg=s.getReg reg := by
  rw [checkerLaterOrderedState]
  split_ifs
  · rw [checker_later_jump_register,checker_later_pad_register,checker_copy_register _ _ _ scratch,
      checker_first_child_register _ _ _ (by omega) _ scratch,checker_later_dispatch_register _ _ stride parity]
  · rw [checker_later_jump_register,checker_first_child_register _ _ _ (by omega) _ scratch,
      checker_later_pad_register,checker_copy_register _ _ _ scratch,checker_later_dispatch_register _ _ stride parity]

theorem checker_later_ordered_pc {base : CheckerRecordBase} (height : Fin 16) (s : MachineState) (ready : CheckerLaterPathReady height s base) :
    (checkerLaterOrderedState s).pc=4096+4*2606 := by
  rw [checkerLaterOrderedState]
  split_ifs with even
  · apply checker_later_jump_pc .even
    rw [checker_later_pad_pc,checker_copy_pc .even _ _ _ (checker_later_even_copy_ready height s ready even)]
    rfl
  · apply checker_later_jump_pc .odd
    have copyPC := checker_copy_pc .odd _ _ _ (checker_later_odd_copy_ready height s ready even)
    have padPC : (checkerLaterPadState .odd (checkerCopyState .odd (checkerLaterDispatchPrefix s 5))).pc=4096+4*2473 := by
      rw [checker_later_pad_pc,copyPC]; rfl
    exact checker_later_child_pc .odd _ padPC

theorem checker_later_ordered_execution {base : CheckerRecordBase} (height : Fin 16) (s : MachineState)
    (ready : CheckerLaterPathReady height s base) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (45+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLaterOrderedState s) coins
          return result.charge 45 0) := by
  have counter := checker_later_counter height s ready
  have digest : (checkerLaterDispatchPrefix s 5).getReg .x23=12288 :=
    (checker_later_dispatch_register _ _ (by decide) (by decide)).trans ready.digest
  have pair : (checkerLaterDispatchPrefix s 5).getReg .x24=12544 :=
    (checker_later_dispatch_register _ _ (by decide) (by decide)).trans ready.pair
  by_cases even : s.getReg .x6 &&& 1=0
  · have childPC : (checkerLaterDispatchPrefix s 5).pc=4096+4*2482 := by
      rw [checker_later_dispatch_end s ready.pc counter,if_pos even]
    have copiedReady := checker_later_even_copy_ready height s ready even
    have copyPC := checker_copy_pc .even _ _ _ copiedReady
    have childPair := (checker_first_child_register .even (checkerLaterDispatchPrefix s 5) 8 (by omega) .x24 (by decide)).trans pair
    have copyPair := (checker_copy_register .even _ .x24 (by decide)).trans childPair
    have padPC : (checkerLaterPadState .even (checkerCopyState .even
        (checkerFirstChildPrefix .even (checkerLaterDispatchPrefix s 5) 8))).pc=4096+4*2521 := by
      rw [checker_later_pad_pc,copyPC]; rfl
    have copied := checker_copy_execution .even _ _ _ copiedReady (1+(1+fuel)) coins
    simp only [CheckerCopySite.count,Nat.reduceMul] at copied
    rw [show 45+fuel=5+(8+(30+(1+(1+fuel)))) by omega,
      checker_later_dispatch_execution s ready.pc counter,
      checker_later_child_execution .even _ childPC digest pair,copied,
      checker_later_pad_execution .even _ copyPC copyPair,
      checker_later_jump_execution .even _ padPC,checkerLaterOrderedState,if_pos even]
    simp [Execution.charge,←Nat.add_assoc,bind_assoc]
  · have copiedReady := checker_later_odd_copy_ready height s ready even
    have copyPC := checker_copy_pc .odd _ _ _ copiedReady
    have copyPair := (checker_copy_register .odd _ .x24 (by decide)).trans pair
    have padPC : (checkerLaterPadState .odd (checkerCopyState .odd (checkerLaterDispatchPrefix s 5))).pc=4096+4*2473 := by
      rw [checker_later_pad_pc,copyPC]; rfl
    have padPair := (checker_later_pad_register .odd _ .x24).trans copyPair
    have padDigest := (checker_later_pad_register .odd _ .x23).trans
      ((checker_copy_register .odd _ .x23 (by decide)).trans digest)
    have childPC := checker_later_child_pc .odd _ padPC
    have copied := checker_copy_execution .odd _ _ _ copiedReady (1+(8+(1+fuel))) coins
    simp only [CheckerCopySite.count,Nat.reduceMul] at copied
    rw [show 45+fuel=5+(30+(1+(8+(1+fuel)))) by omega,
      checker_later_dispatch_execution s ready.pc counter,copied,
      checker_later_pad_execution .odd _ copyPC copyPair,
      checker_later_child_execution .odd _ padPC padDigest padPair,
      checker_later_jump_execution .odd _ childPC,checkerLaterOrderedState,if_neg even]
    simp [Execution.charge,←Nat.add_assoc,bind_assoc]

private theorem later_reg_mem (s : MachineState) (address value : Word) (reg : Reg) :
    (s.setMem address value).getReg reg=s.getReg reg := by cases reg <;> rfl

theorem checker_lower_finish_transition (s : MachineState) :
    (checkerLowerFinishPrefix s 10).getReg .x21=s.getReg .x21+s.getReg .x30 ∧
    (checkerLowerFinishPrefix s 10).getReg .x6=s.getReg .x6 >>> 1 ∧
    (checkerLowerFinishPrefix s 10).getReg .x29=s.getReg .x29-1 := by
  repeat rw [checker_lower_finish_succ]
  simp (disch := decide) only [checker_lower_finish_zero,checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
    MachineState.getReg_setPC,later_reg_mem,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,reduceCtorEq,later_zero]
  split_ifs <;> simp (disch := decide) only [MachineState.getReg_setPC,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,reduceCtorEq]
  all_goals exact ⟨True.intro,rfl,by rw [BitVec.sub_eq_add_neg]; rfl⟩

theorem checker_lower_finish_counter_pc (height : Fin 16) (s : MachineState)
    (pc : s.pc=4096+4*2609) (counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)) :
    (checkerLowerFinishPrefix s 10).pc=if height.val=15 then 4096+4*2614 else 4096+4*2437 := by
  have before := checker_lower_finish_pc s pc ⟨9,by omega⟩
  have count : (checkerLowerFinishPrefix s 9).getReg .x29=BitVec.ofNat 64 (15-height.val) := by
    repeat rw [checker_lower_finish_succ]
    simp (disch := decide) only [checker_lower_finish_zero,checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
      MachineState.getReg_setPC,later_reg_mem,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,reduceCtorEq,counter,later_zero]
    fin_cases height <;> rfl
  rw [show 10=9+1 from rfl,checker_lower_finish_succ]
  simp only [checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,later_zero,count]
  fin_cases height <;> simp [before,checkerLowerFinishIndex,signExtend13]

end CommitGolfCandidate.Chained.Native.RecordLeaf

/-! Height-indexed delivered lower hash return and loop transitions. -/
namespace CommitGolfCandidate.Chained.Native.RecordLeaf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling SplitCodec
set_option maxRecDepth 8192
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne MachineState.getReg_setPC
@[local simp] private theorem loop_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem loop_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

@[irreducible] def checkerLaterCaller (s : MachineState) : MachineState :=
  checkerFirstHashCallPrefix (checkerLaterOrderedState s) 3

theorem checker_later_caller_register (s : MachineState) (reg : Reg)
    (link : reg≠.x1) (arg0 : reg≠.x10) (arg1 : reg≠.x12)
    (scratch : reg≠.x31) (stride : reg≠.x30) (parity : reg≠.x7) :
    (checkerLaterCaller s).getReg reg=s.getReg reg := by
  rw [checkerLaterCaller,checker_first_hash_call_register _ _ arg0 arg1 link,
    checker_later_ordered_register _ _ scratch stride parity]

theorem checker_later_caller_pc {base : CheckerRecordBase} (height : Fin 16) (s : MachineState) (ready : CheckerLaterPathReady height s base) :
    (checkerLaterCaller s).pc=4096+4*2757 := by
  rw [checkerLaterCaller]
  exact checker_first_hash_call_pc _ (checker_later_ordered_pc height s ready)

theorem checker_later_caller_pair {base : CheckerRecordBase} (height : Fin 16) (s : MachineState) (ready : CheckerLaterPathReady height s base) :
    (checkerLaterCaller s).getReg .x24=12544 :=
  (checker_later_caller_register s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.pair

theorem checker_later_caller_counter {base : CheckerRecordBase} (height : Fin 16) (s : MachineState) (ready : CheckerLaterPathReady height s base) :
    (checkerLaterCaller s).getReg .x29=BitVec.ofNat 64 (16-height.val) :=
  (checker_later_caller_register s .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.counter

theorem checker_later_hash_ready {base : CheckerRecordBase} (height : Fin 16) (s : MachineState) (ready : CheckerLaterPathReady height s base) :
    CheckerLowerHashReady height (checkerLowerHashState height (checkerLaterCaller s)) :=
  checker_lower_hash_ready height _ (checker_later_caller_pc height s ready)
    (checker_later_caller_pair height s ready) (checker_later_caller_counter height s ready)

def checkerLaterHashTrace (height : Fin 16) (s : MachineState) : OracleComp World MachineState :=
  checkerHashTrace .lower (checkerLowerRemaining height) (checkerLowerHashState height (checkerLaterCaller s))

theorem checker_later_hash_saved {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterHashTrace height s)) (slot : Fin 31) :
    out.getMem (checkerSaveWord slot)=(checkerLaterCaller s).getReg (checkerSnapshotReg slot) := by
  exact (checker_hash_saved_memory .lower _ _ out (checker_later_hash_ready height s ready).args reached slot).trans
    (checker_lower_hash_saved height _ (checker_later_caller_pair height s ready) slot)

theorem checker_later_hash_destination {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterHashTrace height s)) :
    out.getMem (checkerSaveWord CheckerHashSite.lower.resultSlot)=12288 := by
  rw [checker_later_hash_saved height s out ready reached,
    checker_later_caller_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact ready.digest

theorem checker_later_return_register {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterHashTrace height s)) (slot : Fin 31) :
    (checkerHashReturned .lower out).getReg (checkerSnapshotReg slot)=
      (checkerLaterCaller s).getReg (checkerSnapshotReg slot) :=
  (checker_hash_returned_register .lower out (checker_later_hash_destination height s out ready reached) slot).trans
    (checker_later_hash_saved height s out ready reached slot)

theorem checker_later_return_pc {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterHashTrace height s)) :
    (checkerHashReturned .lower out).pc=4096+4*2609 := by
  apply checker_hash_returned_pc out (checker_later_hash_destination height s out ready reached)
  rw [checker_later_hash_saved height s out ready reached,checkerLaterCaller]
  have pc := checker_later_ordered_pc height s ready
  simp [checkerFirstHashCallPrefix,checkerFirstHashCallOps,execInstrBr,pc,checkerSnapshotReg,checkerSnapshotRegs]

theorem checker_later_return_digest {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterHashTrace height s)) :
    (checkerHashReturned .lower out).getReg .x23=12288 :=
  (checker_hash_returned_register .lower out (checker_later_hash_destination height s out ready reached) ⟨22,by omega⟩).trans
    (checker_later_hash_destination height s out ready reached)

theorem checker_later_hash_execution {base : CheckerRecordBase} (height : Fin 16) (s : MachineState)
    (ready : CheckerLaterPathReady height s base) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (48+checkerLowerHashInstructions height+fuel) s coins=
      (do let out ← checkerLaterHashTrace height s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (48+checkerLowerHashCycles height) (calls ⟨height.val,by omega⟩)) := by
  rw [show 48+checkerLowerHashInstructions height+fuel=45+(3+(checkerLowerHashInstructions height+fuel)) by omega,
    checker_later_ordered_execution height s ready,
    checker_first_hash_call_execution _ (checker_later_ordered_pc height s ready),←checkerLaterCaller,
    checker_lower_hash_execution height _ (checker_later_caller_pc height s ready)
      (checker_later_caller_pair height s ready) (checker_later_caller_counter height s ready),checkerLaterHashTrace]
  simp [Execution.charge,←Nat.add_assoc,bind_assoc]

def checkerLaterLowerTrace (height : Fin 16) (s : MachineState) : OracleComp World MachineState := do
  let out ← checkerLaterHashTrace height s
  pure (checkerLowerFinishPrefix (checkerHashReturned .lower out) 10)

theorem checker_later_lower_execution {base : CheckerRecordBase} (height : Fin 16) (s : MachineState)
    (ready : CheckerLaterPathReady height s base) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (99+checkerLowerHashInstructions height+fuel) s coins=
      (do let out ← checkerLaterLowerTrace height s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (99+checkerLowerHashCycles height) (calls ⟨height.val,by omega⟩)) := by
  rw [show 99+checkerLowerHashInstructions height+fuel=(48+checkerLowerHashInstructions height)+(41+(10+fuel)) by omega,
    checker_later_hash_execution height s ready,checkerLaterLowerTrace]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro out reached
  have hashPC := checker_hash_return_pc .lower _ _ out (checker_later_hash_ready height s ready).pc reached
  rw [checker_hash_return_execution .lower out hashPC (checker_later_hash_destination height s out ready reached),
    checker_lower_finish_execution _ (checker_later_return_pc height s out ready reached) (checker_later_return_digest height s out ready reached)]
  simp [Execution.charge,←Nat.add_assoc,
    show 48+checkerLowerHashCycles height+41+10=99+checkerLowerHashCycles height by omega]

theorem checker_later_ordered_stride (s : MachineState) : (checkerLaterOrderedState s).getReg .x30=30 := by
  have dispatch : (checkerLaterDispatchPrefix s 5).getReg .x30=30 := by
    simp (disch := decide) only [checkerLaterDispatchPrefix,checkerLaterDispatchOps,checkerLowerGateOps,List.take,List.foldl,List.cons_append,List.nil_append,execInstrBr,
      MachineState.getReg_setPC,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,reduceCtorEq,loop_zero]
    split_ifs <;> simp_all [signExtend12]
  rw [checkerLaterOrderedState]
  split_ifs
  · rw [checker_later_jump_register,checker_later_pad_register,checker_copy_register _ _ _ (by decide),
      checker_first_child_register _ _ _ (by omega) _ (by decide)]
    exact dispatch
  · rw [checker_later_jump_register,checker_first_child_register _ _ _ (by omega) _ (by decide),
      checker_later_pad_register,checker_copy_register _ _ _ (by decide)]
    exact dispatch

theorem checker_later_lower_values {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterLowerTrace height s)) :
    out.getReg .x21=s.getReg .x21+30 ∧ out.getReg .x6=s.getReg .x6 >>> 1 ∧
      out.getReg .x29=BitVec.ofNat 64 (15-height.val) := by
  simp only [checkerLaterLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  have cursor := checker_later_return_register height s hashed ready last ⟨20,by omega⟩
  have node := checker_later_return_register height s hashed ready last ⟨5,by omega⟩
  have stride := checker_later_return_register height s hashed ready last ⟨29,by omega⟩
  have count := checker_later_return_register height s hashed ready last ⟨28,by omega⟩
  change (checkerHashReturned .lower hashed).getReg .x21=(checkerLaterCaller s).getReg .x21 at cursor
  change (checkerHashReturned .lower hashed).getReg .x6=(checkerLaterCaller s).getReg .x6 at node
  change (checkerHashReturned .lower hashed).getReg .x30=(checkerLaterCaller s).getReg .x30 at stride
  change (checkerHashReturned .lower hashed).getReg .x29=(checkerLaterCaller s).getReg .x29 at count
  rw [checker_later_caller_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at cursor node
  rw [checkerLaterCaller,checker_first_hash_call_register _ _ (by decide) (by decide) (by decide),checker_later_ordered_stride] at stride
  rw [checker_later_caller_counter height s ready] at count
  have values := checker_lower_finish_transition (checkerHashReturned .lower hashed)
  rw [cursor,node,stride,count] at values
  exact ⟨values.1,values.2.1,values.2.2.trans (by fin_cases height <;> rfl)⟩

theorem checker_later_lower_pc {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterLowerTrace height s)) :
    out.pc=if height.val=15 then 4096+4*2614 else 4096+4*2437 := by
  simp only [checkerLaterLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  apply checker_lower_finish_counter_pc height _ (checker_later_return_pc height s hashed ready last)
  have count := checker_later_return_register height s hashed ready last ⟨28,by omega⟩
  exact count.trans (checker_later_caller_counter height s ready)

private theorem loop_reg_mem (s : MachineState) (address value : Word) (reg : Reg) :
    (s.setMem address value).getReg reg=s.getReg reg := by cases reg <;> rfl

theorem checker_lower_finish_pair (s : MachineState) (n : Nat) (small : n≤10) :
    (checkerLowerFinishPrefix s n).getReg .x24=s.getReg .x24 := by
  have step (t : MachineState) (i : Fin 10) :
      (execInstrBr t (checkerLowerFinishOps.getD i.val .EBREAK)).getReg .x24=t.getReg .x24 := by
    fin_cases i
    all_goals simp (disch := decide) only [checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
      MachineState.getReg_setPC,loop_reg_mem,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,reduceCtorEq]
    all_goals split_ifs <;> simp only [MachineState.getReg_setPC]
  induction n with
  | zero => rw [checker_lower_finish_zero]
  | succ n ih => rw [checker_lower_finish_succ,step _ ⟨n,by omega⟩,ih (by omega)]

structure CheckerLowerLoopReady (height : Fin 17) (s : MachineState)
    (base : CheckerRecordBase := checkerDefaultRecordBase) : Prop where
  pc : s.pc=if height.val=16 then 4096+4*2614 else 4096+4*2437
  source : s.getReg .x21=BitVec.ofNat 64 (checkerLowerCursor height base.value)
  digest : s.getReg .x23=12288
  pair : s.getReg .x24=12544
  counter : s.getReg .x29=BitVec.ofNat 64 (16-height.val)

theorem checker_lower_loop_later {base : CheckerRecordBase} (height : Fin 17) (s : MachineState)
    (positive : 0<height.val) (active : height.val<16) (ready : CheckerLowerLoopReady height s base) :
    CheckerLaterPathReady ⟨height.val,active⟩ s base := by
  refine ⟨positive,?_,ready.source,ready.digest,ready.pair,ready.counter⟩
  simpa only [ite_eq_right (show height.val≠16 by omega)] using ready.pc

theorem checker_lower_cursor_advance (height : Fin 16) (recordBase : Nat := checkingRawBase) :
    BitVec.ofNat 64 (checkerLowerCursor ⟨height.val,by omega⟩ recordBase)+(if height.val=0 then 32 else 30)=
      BitVec.ofNat 64 (checkerLowerCursor ⟨height.val+1,by omega⟩ recordBase) := by
  fin_cases height <;> simp [checkerLowerCursor,←BitVec.ofNat_add,Nat.add_assoc]

theorem checker_later_lower_next {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterLowerTrace height s)) :
    CheckerLowerLoopReady ⟨height.val+1,by omega⟩ out base := by
  have values := checker_later_lower_values height s out ready reached
  have digest : out.getReg .x23=12288 := by
    simp only [checkerLaterLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
    obtain ⟨hashed,last,rfl⟩ := reached
    rw [checker_lower_finish_digest _ _ (by omega)]
    exact checker_later_return_digest height s hashed ready last
  have pair : out.getReg .x24=12544 := by
    simp only [checkerLaterLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
    obtain ⟨hashed,last,rfl⟩ := reached
    rw [checker_lower_finish_pair _ _ (by omega)]
    exact (checker_later_return_register height s hashed ready last ⟨23,by omega⟩).trans (checker_later_caller_pair height s ready)
  refine ⟨?_,?_,digest,pair,?_⟩
  · have pc := checker_later_lower_pc height s out ready reached
    simpa only [show height.val+1=16 ↔ height.val=15 by omega] using pc
  · rw [values.1,ready.source]
    simpa only [ite_eq_right (show height.val≠0 by have := ready.positive; omega)] using checker_lower_cursor_advance height base.value
  · simpa only [show 16-(height.val+1)=15-height.val by omega] using values.2.2

theorem checker_first_lower_next {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstLowerTrace s)) :
    CheckerLowerLoopReady ⟨1,by omega⟩ out base := by
  have values := checker_first_lower_values input s out ready reached
  have digest : out.getReg .x23=12288 := by
    simp only [checkerFirstLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
    obtain ⟨hashed,last,rfl⟩ := reached
    rw [checker_lower_finish_digest _ _ (by omega)]
    exact checker_first_sibling_return_digest input s hashed ready last
  have pair : out.getReg .x24=12544 := by
    simp only [checkerFirstLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
    obtain ⟨hashed,last,rfl⟩ := reached
    rw [checker_lower_finish_pair _ _ (by omega)]
    exact (checker_first_sibling_return_register input s hashed ready last ⟨23,by omega⟩).trans
      ((checker_first_sibling_caller_register s .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.pair)
  refine ⟨checker_first_lower_pc input s out ready reached,?_,digest,pair,values.2.2⟩
  rw [values.1,ready.source]
  simp [checkerLowerCursor,←BitVec.ofNat_add,Nat.add_assoc]

def checkerLowerSuffixTrace : (count : Nat) → (height : Fin 17) →
    (height.val+count≤16) → MachineState → OracleComp World MachineState
  | 0,_,_,s => pure s
  | count+1,height,room,s => do
    let out ← checkerLaterLowerTrace ⟨height.val,by omega⟩ s
    checkerLowerSuffixTrace count ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega) out

def checkerLowerSuffixInstructions : (count : Nat) → (height : Fin 17) → (height.val+count≤16) → Nat
  | 0,_,_ => 0
  | count+1,height,room => 99+checkerLowerHashInstructions ⟨height.val,by omega⟩+
    checkerLowerSuffixInstructions count ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega)

def checkerLowerSuffixCycles : (count : Nat) → (height : Fin 17) → (height.val+count≤16) → Nat
  | 0,_,_ => 0
  | count+1,height,room => 99+checkerLowerHashCycles ⟨height.val,by omega⟩+
    checkerLowerSuffixCycles count ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega)

def checkerLowerSuffixCalls : (count : Nat) → (height : Fin 17) → (height.val+count≤16) → Nat
  | 0,_,_ => 0
  | count+1,height,room => calls ⟨height.val,by omega⟩+
    checkerLowerSuffixCalls count ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega)

theorem checker_lower_suffix_execution {base : CheckerRecordBase} (count : Nat) (height : Fin 17) (room : height.val+count≤16)
    (s : MachineState) (positive : 0<height.val) (ready : CheckerLowerLoopReady height s base) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerLowerSuffixInstructions count height room+fuel) s coins=
      (do let out ← checkerLowerSuffixTrace count height room s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (checkerLowerSuffixCycles count height room) (checkerLowerSuffixCalls count height room)) := by
  induction count generalizing height s with
  | zero => simp [checkerLowerSuffixInstructions,checkerLowerSuffixCycles,checkerLowerSuffixCalls,checkerLowerSuffixTrace,Execution.charge]
  | succ count ih =>
    have active : height.val<16 := by omega
    have stepReady := checker_lower_loop_later height s positive active ready
    rw [checkerLowerSuffixInstructions,checkerLowerSuffixCycles,checkerLowerSuffixCalls,checkerLowerSuffixTrace,
      Nat.add_assoc,checker_later_lower_execution ⟨height.val,active⟩ s stepReady]
    simp only [bind_assoc,pure_bind]
    apply bind_congr_of_forall_mem_support
    intro out reached
    rw [ih ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega) out
      (by change 0<height.val+1; omega) (checker_later_lower_next _ s out stepReady reached)]
    simp [Execution.charge,Nat.add_assoc]

theorem checker_lower_suffix_values :
    checkerLowerSuffixInstructions 15 ⟨1,by decide⟩ (by decide)=3438 ∧
    checkerLowerSuffixCycles 15 ⟨1,by decide⟩ (by decide)=4040 ∧
    checkerLowerSuffixCalls 15 ⟨1,by decide⟩ (by decide)=86 := by
  decide +kernel

theorem checker_lower_suffix_ready {base : CheckerRecordBase} (count : Nat) (height : Fin 17) (room : height.val+count≤16)
    (s out : MachineState) (positive : 0<height.val) (ready : CheckerLowerLoopReady height s base)
    (reached : out∈support (checkerLowerSuffixTrace count height room s)) :
    CheckerLowerLoopReady ⟨height.val+count,by omega⟩ out base := by
  induction count generalizing height s with
  | zero =>
    simp only [checkerLowerSuffixTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    simpa only [Nat.add_zero] using ready
  | succ count ih =>
    have active : height.val<16 := by omega
    have stepReady := checker_lower_loop_later height s positive active ready
    simp only [checkerLowerSuffixTrace,mem_support_bind_iff] at reached
    obtain ⟨middle,first,last⟩ := reached
    have next := checker_later_lower_next _ s middle stepReady first
    have result := ih ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega)
      middle (by change 0<height.val+1; omega) next last
    have same : (⟨height.val+1+count,by omega⟩ : Fin 17)=⟨height.val+(count+1),by omega⟩ := by
      apply Fin.ext; dsimp; omega
    rw [same] at result
    exact result

def checkerLowerSixteenTrace (s : MachineState) : OracleComp World MachineState := do
  let out ← checkerFirstLowerTrace s
  checkerLowerSuffixTrace 15 ⟨1,by decide⟩ (by decide) out

theorem checker_lower_sixteen_execution {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerFirstOrderingInstructions s+3609+fuel) s coins=
      (do let out ← checkerLowerSixteenTrace s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (checkerFirstOrderingInstructions s+4239) 90) := by
  rw [show checkerFirstOrderingInstructions s+3609+fuel=checkerFirstOrderingInstructions s+171+(3438+fuel) by omega,
    checker_first_lower_execution input s ready,checkerLowerSixteenTrace]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro out reached
  have suffix := checker_lower_suffix_execution 15 ⟨1,by decide⟩ (by decide) out (by decide)
    (checker_first_lower_next input s out ready reached) fuel coins
  rw [checker_lower_suffix_values.1,checker_lower_suffix_values.2.1,checker_lower_suffix_values.2.2] at suffix
  rw [suffix]
  simp [Execution.charge,←Nat.add_assoc,
    show checkerFirstOrderingInstructions s+199+4040=checkerFirstOrderingInstructions s+4239 by omega]

private theorem loop_shift_add (value : Word) (first second : Nat) :
    (value >>> first) >>> second=value >>> (first+second) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit _
  simp only [BitVec.getLsbD_ushiftRight,Nat.add_assoc]

theorem checker_lower_suffix_node {base : CheckerRecordBase} (count : Nat) (height : Fin 17) (room : height.val+count≤16)
    (s out : MachineState) (positive : 0<height.val) (ready : CheckerLowerLoopReady height s base)
    (reached : out∈support (checkerLowerSuffixTrace count height room s)) :
    out.getReg .x6=s.getReg .x6 >>> count := by
  induction count generalizing height s with
  | zero =>
    simp only [checkerLowerSuffixTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact (BitVec.ushiftRight_zero _).symm
  | succ count ih =>
    have active : height.val<16 := by omega
    have stepReady := checker_lower_loop_later height s positive active ready
    simp only [checkerLowerSuffixTrace,mem_support_bind_iff] at reached
    obtain ⟨middle,first,last⟩ := reached
    rw [ih ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega) middle
      (by change 0<height.val+1; omega) (checker_later_lower_next _ s middle stepReady first) last,
      (checker_later_lower_values _ s middle stepReady first).2.1,loop_shift_add,Nat.add_comm 1 count]

theorem checker_lower_sixteen_ready {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerLowerSixteenTrace s)) :
    CheckerLowerLoopReady ⟨16,by decide⟩ out base := by
  simp only [checkerLowerSixteenTrace,mem_support_bind_iff] at reached
  obtain ⟨middle,first,last⟩ := reached
  exact checker_lower_suffix_ready 15 ⟨1,by decide⟩ (by decide) middle out (by decide)
    (checker_first_lower_next input s middle ready first) last

theorem checker_lower_sixteen_pc {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerLowerSixteenTrace s)) :
    out.pc=4096+4*2614 :=
  (checker_lower_sixteen_ready input s out ready reached).pc

theorem checker_lower_sixteen_node {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerLowerSixteenTrace s)) :
    out.getReg .x6=s.getReg .x6 >>> 16 := by
  simp only [checkerLowerSixteenTrace,mem_support_bind_iff] at reached
  obtain ⟨middle,first,last⟩ := reached
  rw [checker_lower_suffix_node 15 ⟨1,by decide⟩ (by decide) middle out (by decide)
      (checker_first_lower_next input s middle ready first) last,
    (checker_first_lower_values input s middle ready first).2.1,loop_shift_add]

theorem checker_lower_sixteen_input_execution {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState)
    (ready : CheckerFirstPathReady input s base record) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerFirstOrderingInput input record+3609+fuel) s coins=
      (do let out ← checkerLowerSixteenTrace s
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge (checkerFirstOrderingInput input record+4239) 90) := by
  simpa only [checker_first_ordering_input input s ready] using checker_lower_sixteen_execution input s ready fuel coins

def checkerDecodedLowerTrace (input : CheckInput) (nonempty : input.positions.card≠0) (s : MachineState) : OracleComp World MachineState := do
  let after ← leafQueries (checkerRecordNonceState s) 754975239 (checkerFirstInputIndex input nonempty)
  checkerLowerSixteenTrace (checkerLeafPathState after)

theorem checker_decoded_lower_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (fuel : Nat) :
    execute (Artifact.submission.image .check) (checkerFirstOrderingInput input+5729+fuel) s false=
      (do let out ← checkerDecodedLowerTrace input nonempty s
          let result ← execute (Artifact.submission.image .check) fuel out false
          return result.charge (checkerFirstOrderingInput input+6373) 92) := by
  rw [show checkerFirstOrderingInput input+5729+fuel=2120+(checkerFirstOrderingInput input+3609+fuel) by omega,
    checker_decoded_path_execution input nonempty footer s ready,checkerDecodedLowerTrace]
  simp only [leafQueries,bind_assoc,pure_bind]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  rw [checker_lower_sixteen_input_execution input _ (checker_first_path_ready input nonempty footer s ready a b)]
  simp [Execution.charge,←Nat.add_assoc,
    show 2134+checkerFirstOrderingInput input+4239=checkerFirstOrderingInput input+6373 by omega]

theorem checker_decoded_lower_pc (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s out : MachineState)
    (ready : CheckerDecodedInput input footer s) (reached : out∈support (checkerDecodedLowerTrace input nonempty s)) :
    out.pc=4096+4*2614 := by
  simp only [checkerDecodedLowerTrace,leafQueries,bind_assoc,pure_bind,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨a,_,b,_,last⟩ := reached
  exact checker_lower_sixteen_pc input _ out (checker_first_path_ready input nonempty footer s ready a b) last

end CommitGolfCandidate.Chained.Native.RecordLeaf

/-! The lower path leaves the heap, proof input and fixed record ABI untouched. -/
namespace CommitGolfCandidate.Chained.Native.RecordLeaf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

def checkerLowerFixedSlot (slot : Fin 14) : Fin 31 :=
  ⟨([4,7,8,10,12,17,18,21,24,25,26,2,3,19] : List Nat).getD slot.val 0,by fin_cases slot <;> decide⟩

def checkerLowerFixedReg (slot : Fin 14) : Reg := checkerSnapshotReg (checkerLowerFixedSlot slot)

def CheckerLowerFixed (before after : MachineState) : Prop :=
  ∀ slot : Fin 14, after.getReg (checkerLowerFixedReg slot)=before.getReg (checkerLowerFixedReg slot)

theorem CheckerLowerFixed.trans {before middle after : MachineState}
    (first : CheckerLowerFixed before middle) (last : CheckerLowerFixed middle after) :
    CheckerLowerFixed before after := fun slot => (last slot).trans (first slot)

private theorem frame_reg_mem (s : MachineState) (address value : Word) (reg : Reg) :
    (s.setMem address value).getReg reg=s.getReg reg := by cases reg <;> rfl

private theorem frame_reg_zero (s : MachineState) (value : Word) (reg : Reg) :
    (s.setReg .x0 value).getReg reg=s.getReg reg := by cases reg <;> rfl

private theorem frame_mem_reg (s : MachineState) (reg : Reg) (value : Word) : (s.setReg reg value).mem=s.mem := by
  cases reg <;> rfl

private theorem frame_mem_pc (s : MachineState) (value : Word) : (s.setPC value).mem=s.mem := rfl

theorem checker_lower_finish_fixed (s : MachineState) (n : Nat) (small : n≤10) :
    CheckerLowerFixed s (checkerLowerFinishPrefix s n) := by
  intro slot
  have node : checkerLowerFixedReg slot≠.x6 := by fin_cases slot <;> decide
  have cursor : checkerLowerFixedReg slot≠.x21 := by fin_cases slot <;> decide
  have counter : checkerLowerFixedReg slot≠.x29 := by fin_cases slot <;> decide
  have temp : checkerLowerFixedReg slot≠.x31 := by fin_cases slot <;> decide
  have step (t : MachineState) (i : Fin 10) :
      (execInstrBr t (checkerLowerFinishOps.getD i.val .EBREAK)).getReg (checkerLowerFixedReg slot)=
        t.getReg (checkerLowerFixedReg slot) := by
    fin_cases i
    all_goals simp only [checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
      MachineState.getReg_setPC,frame_reg_mem,frame_reg_zero,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm node),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm cursor),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm counter),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm temp)]
    all_goals split_ifs <;> simp only [MachineState.getReg_setPC]
  induction n with
  | zero => rw [checker_lower_finish_zero]
  | succ n ih => rw [checker_lower_finish_succ,step _ ⟨n,by omega⟩,ih (by omega)]

private theorem fixed_caller (s : MachineState) (slot : Fin 14) :
    (checkerFirstHashCallPrefix (checkerFirstOrderedState s) 3).getReg (checkerLowerFixedReg slot)=s.getReg (checkerLowerFixedReg slot) := by
  apply checker_first_sibling_caller_register
  all_goals fin_cases slot <;> decide

private theorem fixed_later_caller (s : MachineState) (slot : Fin 14) :
    (checkerLaterCaller s).getReg (checkerLowerFixedReg slot)=s.getReg (checkerLowerFixedReg slot) := by
  apply checker_later_caller_register
  all_goals fin_cases slot <;> decide

theorem checker_first_lower_fixed {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstLowerTrace s)) :
    CheckerLowerFixed s out := by
  simp only [checkerFirstLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  intro slot
  rw [checker_lower_finish_fixed _ 10 (by omega) slot]
  exact (checker_first_sibling_return_register input s hashed ready last (checkerLowerFixedSlot slot)).trans
    (fixed_caller s slot)

theorem checker_later_lower_fixed {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterLowerTrace height s)) :
    CheckerLowerFixed s out := by
  simp only [checkerLaterLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  intro slot
  rw [checker_lower_finish_fixed _ 10 (by omega) slot]
  exact (checker_later_return_register height s hashed ready last (checkerLowerFixedSlot slot)).trans
    (fixed_later_caller s slot)

theorem checker_lower_suffix_fixed {base : CheckerRecordBase} (count : Nat) (height : Fin 17) (room : height.val+count≤16)
    (s out : MachineState) (positive : 0<height.val) (ready : CheckerLowerLoopReady height s base)
    (reached : out∈support (checkerLowerSuffixTrace count height room s)) : CheckerLowerFixed s out := by
  induction count generalizing height s with
  | zero =>
    simp only [checkerLowerSuffixTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    intro slot
    rfl
  | succ count ih =>
    have active : height.val<16 := by omega
    have stepReady := checker_lower_loop_later height s positive active ready
    simp only [checkerLowerSuffixTrace,mem_support_bind_iff] at reached
    obtain ⟨middle,first,last⟩ := reached
    exact (checker_later_lower_fixed _ s middle stepReady first).trans
      (ih ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega) middle
        (by change 0<height.val+1; omega) (checker_later_lower_next _ s middle stepReady first) last)

theorem checker_lower_sixteen_fixed {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerLowerSixteenTrace s)) :
    CheckerLowerFixed s out := by
  simp only [checkerLowerSixteenTrace,mem_support_bind_iff] at reached
  obtain ⟨middle,first,last⟩ := reached
  exact (checker_first_lower_fixed input s middle ready first).trans
    (checker_lower_suffix_fixed 15 ⟨1,by decide⟩ (by decide) middle out (by decide)
      (checker_first_lower_next input s middle ready first) last)

theorem checker_hash_packed_memory (site : CheckerHashSite) (s : MachineState) (args : LoopArgs s 256)
    (query : Word) (outside : OutsideScratch query) : (checkerHashPacked site s).getMem query=s.getMem query := by
  rw [checker_hash_packed_eq,first_pack_memory_outside]
  · exact checker_hash_pack_start_memory site s query
  · rw [(args.checkerPackStart site).source]
    exact scratch_address_ne query outside.lower

theorem checker_hash_continued_memory (site : CheckerHashSite) (s : MachineState) (args : LoopArgs s 256)
    (answer : Output) (query : Word) (outside : OutsideScratch query) :
    (checkerHashContinued site s answer).getMem query=s.getMem query := by
  rw [checker_hash_continued_eq]
  change (writeBits (checkerHashPacked site s) 256 answer).getMem query=_
  rw [write_reply_memory _ answer query outside,checker_hash_packed_memory site s args query outside]

theorem checker_hash_trace_memory (site : CheckerHashSite) (remaining : Nat) (s out : MachineState)
    (args : LoopArgs s 256) (reached : out∈support (checkerHashTrace site remaining s))
    (query : Word) (outside : OutsideScratch query) : out.getMem query=s.getMem query := by
  rw [checker_hash_trace_eq] at reached
  simp only [mem_support_bind_iff] at reached
  obtain ⟨answer,_,last⟩ := reached
  exact (continuation_full_memory checkerContinuationBase remaining _ out
    (args.checkerContinued site answer) last query outside).trans
      (checker_hash_continued_memory site s args answer query outside)

structure OutsideLower (query : Word) extends OutsideScratch query : Prop where
  region : query.toNat+32≤12288 ∨ 12800≤query.toNat

theorem OutsideLower.pair (query : Word) (outside : OutsideLower query) (word : Fin 8) :
    query≠(12544 : Word)+BitVec.ofNat 64 (8*word.val) := by
  intro same
  have numeric := congrArg BitVec.toNat same
  have bounds : 12544≤((12544 : Word)+BitVec.ofNat 64 (8*word.val)).toNat ∧
      ((12544 : Word)+BitVec.ofNat 64 (8*word.val)).toNat<12800 := by
    fin_cases word <;> decide
  have := outside.region
  omega

theorem OutsideLower.digest (query : Word) (outside : OutsideLower query) (word : Fin 4) :
    query≠(12288 : Word)+BitVec.ofNat 64 (8*word.val) := by
  intro same
  have numeric := congrArg BitVec.toNat same
  have bounds : 12288≤((12288 : Word)+BitVec.ofNat 64 (8*word.val)).toNat ∧
      ((12288 : Word)+BitVec.ofNat 64 (8*word.val)).toNat<12800 := by
    fin_cases word <;> decide
  have := outside.region
  omega

theorem checker_child_mask_memory (s : MachineState) (n : Nat) (small : n≤9)
    (pair : s.getReg .x24=12544) (query : Word) (outside : OutsideLower query) :
    (checkerChildMaskPrefix .lower s n).getMem query=s.getMem query := by
  have succ (i : Nat) (inside : i<9) : checkerChildMaskPrefix .lower s (i+1)=
      execInstrBr (checkerChildMaskPrefix .lower s i) ((checkerChildMaskOps .lower).getD i .EBREAK) := by
    interval_cases i <;> rw [checkerChildMaskPrefix,checkerChildMaskPrefix] <;> rfl
  have step (t : MachineState) (i : Fin 9) (source : t.getReg .x14=12544) :
      (execInstrBr t ((checkerChildMaskOps .lower).getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i
    all_goals first | rfl | apply word_store_frame
    all_goals rw [source]
    all_goals first | exact OutsideLower.pair query outside ⟨3,by omega⟩ | exact OutsideLower.pair query outside ⟨7,by omega⟩
  induction n with
  | zero => rw [checkerChildMaskPrefix]; rfl
  | succ n ih =>
    by_cases empty : n=0
    · subst n
      rw [checkerChildMaskPrefix]
      rfl
    · rw [succ n (by omega),step _ ⟨n,by omega⟩
        ((checker_child_mask_source .lower s n (by omega) (by omega)).trans pair),ih (by omega)]

theorem checker_lower_prepared_memory (height : Fin 16) (s : MachineState)
    (pair : s.getReg .x24=12544) (query : Word) (outside : OutsideLower query) :
    (checkerLowerHashState height s).getMem query=s.getMem query := by
  rw [checkerLowerHashState,checker_hash_abi_memory,checker_lower_schedule_memory,
    checker_child_mask_memory _ _ (by omega)]
  · apply checker_snapshot_memory_frame _ _ (by omega)
    intro slot
    intro same
    have high := outside.lower
    have low : (checkerSaveWord slot).toNat<248 := by
      simp only [checkerSaveWord,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*slot.val<2^64)]
      omega
    change query=checkerSaveWord slot at same
    rw [same] at high
    omega
  · exact (checker_snapshot_register 31 s (by omega) .x24).trans pair
  · exact outside

private theorem buffer_word_frame (before after : MachineState) (query : Word) (aligned : query.toNat%8=0)
    (same : readBuffer after query.toNat 32=readBuffer before query.toNat 32) : after.getMem query=before.getMem query := by
  have word := congrArg (fun value : Output => value.extractLsb' 0 64) same
  rw [read_digest_word _ _ 0 aligned (by decide),read_digest_word _ _ 0 aligned (by decide)] at word
  simpa only [Nat.mul_zero,Nat.add_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using word

theorem checker_copy_lower_memory (site : CheckerCopySite) (s : MachineState) (source target : Nat)
    (ready : TwoPermutationPrototype.Packed.CopyReady (checkerCopyCode site) s source target 0)
    (ordered : target≤source) (targetLow : 12544≤target) (targetHigh : target+2*site.count≤12800)
    (query : Word) (outside : OutsideLower query) : (checkerCopyState site s).getMem query=s.getMem query := by
  apply buffer_word_frame s _ query outside.aligned
  apply checker_copy_buffer_outside site s source target query.toNat 32 ready ordered outside.room
  rcases outside.region with low | high
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

theorem checker_first_child_lower_memory (order : FirstSiblingOrder) (s : MachineState)
    (digest : s.getReg .x23=12288) (pair : s.getReg .x24=12544) (query : Word) (outside : OutsideLower query) :
    (checkerFirstChildPrefix order s 8).getMem query=s.getMem query := by
  apply checker_first_child_outside order s digest pair query
  intro word
  cases order with
  | even => simpa only [FirstSiblingOrder.childOffset,Nat.zero_add] using OutsideLower.pair query outside ⟨word.val,by omega⟩
  | odd =>
    have same : 8*(word.val+4)=32+8*word.val := by omega
    simpa only [same,FirstSiblingOrder.childOffset] using OutsideLower.pair query outside ⟨word.val+4,by omega⟩

private theorem jump_memory (s : MachineState) (offset : BitVec 21) (query : Word) :
    (execInstrBr s (.JAL .x0 offset)).getMem query=s.getMem query := rfl

theorem checker_first_ordered_memory {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s : MachineState) (ready : CheckerFirstPathReady input s base record)
    (query : Word) (outside : OutsideLower query) : (checkerFirstOrderedState s).getMem query=s.getMem query := by
  have baseAbove := base.above
  have baseRoom := base.room
  have baseEven := base.even
  have digest : (checkerFirstSiblingState s).getReg .x23=12288 :=
    (checker_first_sibling_register s .x23 (by first | decide +kernel | omega) (by first | decide +kernel | omega)).trans ready.digest
  have pair : (checkerFirstSiblingState s).getReg .x24=12544 :=
    (checker_first_sibling_register s .x24 (by first | decide +kernel | omega) (by first | decide +kernel | omega)).trans ready.pair
  have memory : (checkerFirstSiblingState s).getMem query=s.getMem query := by
    simp only [MachineState.getMem,checker_first_sibling_memory]
  rw [checkerFirstOrderedState]
  by_cases even : s.getReg .x6 &&& 1=0
  · simp only [even,ite_true]
    rw [checker_copy_lower_memory .firstEven _ (base.value+16) 12576
      (checker_first_even_copy_ready input s ready even) (by first | decide +kernel | omega) (by omega) (by first | decide +kernel | omega) query outside,
      checker_first_child_lower_memory .even _ digest pair query outside,memory]
  · simp only [even,ite_false,jump_memory]
    have copyDigest : (checkerCopyState .firstOdd (checkerFirstSiblingState s)).getReg .x23=12288 :=
      (checker_copy_register _ _ _ (by first | decide +kernel | omega)).trans digest
    have copyPair : (checkerCopyState .firstOdd (checkerFirstSiblingState s)).getReg .x24=12544 :=
      (checker_copy_register _ _ _ (by first | decide +kernel | omega)).trans pair
    rw [checker_first_child_lower_memory .odd _ copyDigest copyPair query outside,
      checker_copy_lower_memory .firstOdd _ (base.value+16) 12544
        (checker_first_odd_copy_ready input s ready even) (by first | decide +kernel | omega) (by omega) (by first | decide +kernel | omega) query outside,memory]

theorem checker_first_hash_call_memory (s : MachineState) (query : Word) :
    (checkerFirstHashCallPrefix s 3).getMem query=s.getMem query := by
  rw [checkerFirstHashCallPrefix]
  rfl

theorem checker_first_hash_memory (s : MachineState) (pair : s.getReg .x24=12544)
    (query : Word) (outside : OutsideLower query) : (checkerFirstHashState s).getMem query=s.getMem query := by
  have memory := checker_lower_prepared_memory ⟨0,by decide⟩ s pair query outside
  rw [checker_lower_hash_memory] at memory
  exact memory

theorem checker_first_sibling_hash_memory {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstSiblingHashTrace s))
    (query : Word) (outside : OutsideLower query) : out.getMem query=s.getMem query := by
  rw [checker_first_sibling_hash_eq] at reached
  rw [checker_hash_trace_memory .lower 3 _ out (checker_first_sibling_hash_prepared input s ready).args
    reached query outside.toOutsideScratch,checker_first_hash_memory]
  · rw [checker_first_hash_call_memory,checker_first_ordered_memory input s ready query outside]
  · exact (checker_first_sibling_caller_register s .x24 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans ready.pair
  · exact outside

theorem checker_hash_returned_memory (site : CheckerHashSite) (s : MachineState)
    (destination : s.getMem (checkerSaveWord site.resultSlot)=12288) (query : Word) (outside : OutsideLower query) :
    (checkerHashReturned site s).getMem query=s.getMem query := by
  rw [checkerHashReturned]
  change (checkerLoadBackPrefix (checkerResultPrefix site s 9) 31).getMem query=_
  rw [checker_load_back_memory _ _ (by omega)]
  exact checker_result_outside site s 9 (by omega) destination query (OutsideLower.digest query outside)

private theorem bne_memory (s : MachineState) (left right : Reg) (offset : BitVec 13) (query : Word) :
    (execInstrBr s (.BNE left right offset)).getMem query=s.getMem query := by
  change MachineState.mem (if s.getReg left != s.getReg right then s.setPC (s.pc+signExtend13 offset) else s.setPC (s.pc+4)) query=s.mem query
  split <;> rfl

theorem checker_lower_finish_memory (s : MachineState) (n : Nat) (small : n≤10)
    (digest : s.getReg .x23=12288) (query : Word) (outside : OutsideLower query) :
    (checkerLowerFinishPrefix s n).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Fin 10) (source : t.getReg .x23=12288) :
      (execInstrBr t (checkerLowerFinishOps.getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i
    case «4» =>
      apply word_store_frame
      rw [source]
      exact OutsideLower.digest query outside ⟨3,by omega⟩
    case «9» => exact bne_memory t .x29 .x0 7488 query
    all_goals simp only [checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
      MachineState.getMem,frame_mem_reg,frame_mem_pc]
  induction n with
  | zero => rw [checker_lower_finish_zero]
  | succ n ih =>
    rw [checker_lower_finish_succ,step _ ⟨n,by omega⟩
      ((checker_lower_finish_digest s n (by omega)).trans digest),ih (by omega)]

theorem checker_first_lower_memory {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerFirstLowerTrace s))
    (query : Word) (outside : OutsideLower query) : out.getMem query=s.getMem query := by
  simp only [checkerFirstLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  rw [checker_lower_finish_memory _ _ (by omega) (checker_first_sibling_return_digest input s hashed ready last) query outside,
    checker_hash_returned_memory .lower _ (checker_first_sibling_destination input s hashed ready last) query outside,
    checker_first_sibling_hash_memory input s hashed ready last query outside]

theorem checker_later_dispatch_memory (s : MachineState) (query : Word) :
    (checkerLaterDispatchPrefix s 5).getMem query=s.getMem query := by
  have branch (t : MachineState) (left right : Reg) (offset : BitVec 13) :
      (execInstrBr t (.BEQ left right offset)).mem=t.mem := by
    change MachineState.mem (if t.getReg left==t.getReg right then t.setPC (t.pc+signExtend13 offset) else t.setPC (t.pc+4))=t.mem
    split_ifs <;> rfl
  have addi (t : MachineState) (rd rs : Reg) (offset : BitVec 12) :
      (execInstrBr t (.ADDI rd rs offset)).mem=t.mem := frame_mem_reg t rd _
  have andi (t : MachineState) : (execInstrBr t (.ANDI .x7 .x6 1)).mem=t.mem := rfl
  have memory : (checkerLaterDispatchPrefix s 5).mem=s.mem := by
    rw [checkerLaterDispatchPrefix]
    change (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.ADDI .x30 .x0 16))
      (.BEQ .x29 .x30 336)) (.ADDI .x30 .x0 30)) (.ANDI .x7 .x6 1)) (.BEQ .x7 .x0 164)).mem=s.mem
    rw [branch,andi,addi,branch,addi]
  simp only [MachineState.getMem,memory]

theorem checker_later_pad_memory (order : FirstSiblingOrder) (s : MachineState) (pair : s.getReg .x24=12544)
    (query : Word) (outside : OutsideLower query) : (checkerLaterPadState order s).getMem query=s.getMem query := by
  rw [checkerLaterPadState]
  change (s.setHalfword (s.getReg .x24+signExtend12 order.laterPadOffset) 0).getMem query=_
  rw [pair]
  cases order with
  | even =>
    change (if query==(12600 : Word) then _ else _)=_
    have apart : query≠(12600 : Word) := by simpa using OutsideLower.pair query outside ⟨7,by omega⟩
    simp only [beq_iff_eq,ite_eq_right apart,MachineState.getMem]
  | odd =>
    change (if query==(12568 : Word) then _ else _)=_
    have apart : query≠(12568 : Word) := by simpa using OutsideLower.pair query outside ⟨3,by omega⟩
    simp only [beq_iff_eq,ite_eq_right apart,MachineState.getMem]

theorem checker_later_jump_memory (order : FirstSiblingOrder) (s : MachineState) (query : Word) :
    (checkerLaterJumpState order s).getMem query=s.getMem query := by
  rw [checkerLaterJumpState,jump_memory]

theorem checker_later_ordered_memory {base : CheckerRecordBase} (height : Fin 16) (s : MachineState) (ready : CheckerLaterPathReady height s base)
    (query : Word) (outside : OutsideLower query) : (checkerLaterOrderedState s).getMem query=s.getMem query := by
  have digest : (checkerLaterDispatchPrefix s 5).getReg .x23=12288 :=
    (checker_later_dispatch_register s .x23 (by decide) (by decide)).trans ready.digest
  have pair : (checkerLaterDispatchPrefix s 5).getReg .x24=12544 :=
    (checker_later_dispatch_register s .x24 (by decide) (by decide)).trans ready.pair
  have orderedAll : ∀ level : Fin 17, 12576≤checkerLowerCursor level base.value := by
    intro level
    have := base.above
    simp only [checkerLowerCursor]
    omega
  have ordered := orderedAll ⟨height.val,by omega⟩
  rw [checkerLaterOrderedState]
  by_cases even : s.getReg .x6 &&& 1=0
  · simp only [even,ite_true,checker_later_jump_memory]
    have pairChild : (checkerFirstChildPrefix .even (checkerLaterDispatchPrefix s 5) 8).getReg .x24=12544 :=
      (checker_first_child_register _ _ _ (by omega) _ (by decide)).trans pair
    have pairCopied : (checkerCopyState .even (checkerFirstChildPrefix .even (checkerLaterDispatchPrefix s 5) 8)).getReg .x24=12544 :=
      (checker_copy_register _ _ _ (by decide)).trans pairChild
    rw [checker_later_pad_memory .even _ pairCopied query outside,
      checker_copy_lower_memory .even _ (checkerLowerCursor ⟨height.val,by omega⟩ base.value) 12576
        (checker_later_even_copy_ready height s ready even) ordered (by omega) (by decide) query outside,
      checker_first_child_lower_memory .even _ digest pair query outside,checker_later_dispatch_memory]
  · simp only [even,ite_false,checker_later_jump_memory]
    have copyDigest : (checkerCopyState .odd (checkerLaterDispatchPrefix s 5)).getReg .x23=12288 :=
      (checker_copy_register _ _ _ (by decide)).trans digest
    have copyPair : (checkerCopyState .odd (checkerLaterDispatchPrefix s 5)).getReg .x24=12544 :=
      (checker_copy_register _ _ _ (by decide)).trans pair
    have padDigest := (checker_later_pad_register .odd _ .x23).trans copyDigest
    have padPair := (checker_later_pad_register .odd _ .x24).trans copyPair
    rw [checker_first_child_lower_memory .odd _ padDigest padPair query outside,
      checker_later_pad_memory .odd _ copyPair query outside,
      checker_copy_lower_memory .odd _ (checkerLowerCursor ⟨height.val,by omega⟩ base.value) 12544
        (checker_later_odd_copy_ready height s ready even) (by omega) (by omega) (by decide) query outside,
      checker_later_dispatch_memory]

theorem checker_later_hash_memory {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterHashTrace height s))
    (query : Word) (outside : OutsideLower query) : out.getMem query=s.getMem query := by
  rw [checker_hash_trace_memory .lower _ _ out (checker_later_hash_ready height s ready).args
    reached query outside.toOutsideScratch,
    checker_lower_prepared_memory height _ (checker_later_caller_pair height s ready) query outside,
    checkerLaterCaller,checker_first_hash_call_memory,checker_later_ordered_memory height s ready query outside]

theorem checker_later_lower_memory {base : CheckerRecordBase} (height : Fin 16) (s out : MachineState)
    (ready : CheckerLaterPathReady height s base) (reached : out∈support (checkerLaterLowerTrace height s))
    (query : Word) (outside : OutsideLower query) : out.getMem query=s.getMem query := by
  simp only [checkerLaterLowerTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨hashed,last,rfl⟩ := reached
  rw [checker_lower_finish_memory _ _ (by omega) (checker_later_return_digest height s hashed ready last) query outside,
    checker_hash_returned_memory .lower _ (checker_later_hash_destination height s hashed ready last) query outside,
    checker_later_hash_memory height s hashed ready last query outside]

theorem checker_lower_suffix_memory {base : CheckerRecordBase} (count : Nat) (height : Fin 17) (room : height.val+count≤16)
    (s out : MachineState) (positive : 0<height.val) (ready : CheckerLowerLoopReady height s base)
    (reached : out∈support (checkerLowerSuffixTrace count height room s))
    (query : Word) (outside : OutsideLower query) : out.getMem query=s.getMem query := by
  induction count generalizing height s with
  | zero =>
    simp only [checkerLowerSuffixTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    rfl
  | succ count ih =>
    have active : height.val<16 := by omega
    have stepReady := checker_lower_loop_later height s positive active ready
    simp only [checkerLowerSuffixTrace,mem_support_bind_iff] at reached
    obtain ⟨middle,first,last⟩ := reached
    exact (ih ⟨height.val+1,by omega⟩ (by change height.val+1+count≤16; omega) middle
      (by change 0<height.val+1; omega) (checker_later_lower_next _ s middle stepReady first) last).trans
        (checker_later_lower_memory _ s middle stepReady first query outside)

theorem checker_lower_sixteen_memory {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerLowerSixteenTrace s))
    (query : Word) (outside : OutsideLower query) : out.getMem query=s.getMem query := by
  simp only [checkerLowerSixteenTrace,mem_support_bind_iff] at reached
  obtain ⟨middle,first,last⟩ := reached
  exact (checker_lower_suffix_memory 15 ⟨1,by decide⟩ (by decide) middle out (by decide)
    (checker_first_lower_next input s middle ready first) last query outside).trans
      (checker_first_lower_memory input s middle ready first query outside)

theorem lower_memory_byte (before after : MachineState)
    (same : ∀ query, OutsideLower query → after.getMem query=before.getMem query)
    (address : Nat) (lower : 12800≤address) (room : address+32≤2^64) :
    after.getByte (BitVec.ofNat 64 address)=before.getByte (BitVec.ofNat 64 address) := by
  let query : Word := BitVec.ofNat 64 address
  have queryNat : query.toNat=address := by
    simp only [query,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : address<2^64)]
  have upper : (alignToDword query).toNat≤address := by
    rw [alignToDword,BitVec.toNat_and]
    exact Nat.and_le_left.trans (le_of_eq queryNat)
  have above := TwoPermutationPrototype.PackedOpening.aligned_dword_above 12800 address
    (by decide) lower (by omega)
  change 12800≤(alignToDword query).toNat at above
  have aligned : (alignToDword query).toNat%8=0 := by
    have zero := alignToDword_byteOffset_zero query
    change ((alignToDword query) &&& (7 : Word)).toNat=0 at zero
    rw [BitVec.toNat_and] at zero
    change (alignToDword query).toNat &&& (2^3-1)=0 at zero
    rwa [Nat.and_two_pow_sub_one_eq_mod] at zero
  have outside : OutsideLower (alignToDword query) := ⟨⟨aligned,by omega,by omega⟩,Or.inr above⟩
  change extractByte (after.getMem (alignToDword query)) (byteOffset query)=
    extractByte (before.getMem (alignToDword query)) (byteOffset query)
  rw [same _ outside]

theorem lower_memory_buffer (before after : MachineState)
    (same : ∀ query, OutsideLower query → after.getMem query=before.getMem query)
    (address count : Nat) (lower : 12800≤address) (room : address+count+32≤2^64) :
    readBuffer after address count=readBuffer before address count := by
  apply lower_buffer_bytes
  intro i inside
  exact lower_memory_byte before after same (address+i) (by omega) (by omega)

theorem checker_lower_sixteen_buffer {base : CheckerRecordBase} {record : Nat} (input : CheckInput) (s out : MachineState)
    (ready : CheckerFirstPathReady input s base record) (reached : out∈support (checkerLowerSixteenTrace s))
    (address count : Nat) (lower : 12800≤address) (room : address+count+32≤2^64) :
    readBuffer out address count=readBuffer s address count :=
  lower_memory_buffer s out (checker_lower_sixteen_memory input s out ready reached) address count lower room

def checkerRecordLowerTrace (input : CheckInput) (record src : Nat) (s : MachineState) : OracleComp World MachineState := do
  let after ← leafQueries (checkerRecordCoreNonceState s) src (checkerRecordInputIndex input record)
  checkerLowerSixteenTrace (checkerLeafPathState after)

theorem checker_record_lower_execution {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s : MachineState} (ready : CheckerRecordCoreReady input record base src s) (fuel : Nat) :
    execute (Artifact.submission.image .check) (checkerFirstOrderingInput input record+3656+fuel) s false=
      (do let out ← checkerRecordLowerTrace input record src s
          let result ← execute (Artifact.submission.image .check) fuel out false
          return result.charge (checkerFirstOrderingInput input record+4300) 92) := by
  rw [show checkerFirstOrderingInput input record+3656+fuel=
    47+(checkerFirstOrderingInput input record+3609+fuel) by omega,
    checker_record_core_path_execution ready,checkerRecordLowerTrace]
  simp only [leafQueries,bind_assoc,pure_bind]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  rw [checker_lower_sixteen_input_execution input _ (checker_record_core_path_ready ready a b)]
  simp [Execution.charge,←Nat.add_assoc,
    show 61+checkerFirstOrderingInput input record+4239=checkerFirstOrderingInput input record+4300 by omega]

theorem checker_record_lower_ready {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) :
    CheckerLowerLoopReady ⟨16,by decide⟩ out base := by
  simp only [checkerRecordLowerTrace,leafQueries,bind_assoc,pure_bind,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨a,_,b,_,last⟩ := reached
  exact checker_lower_sixteen_ready input _ out (checker_record_core_path_ready ready a b) last

theorem checker_record_lower_pc {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) : out.pc=4096+4*2614 :=
  (checker_record_lower_ready ready reached).pc

theorem checker_record_lower_source {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) :
    out.getReg .x21=BitVec.ofNat 64 (base.value+498) := by
  simpa only [checkerLowerCursor,ite_eq_right (by decide : ¬(16 : Nat)=0),Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub]
    using (checker_record_lower_ready ready reached).source

theorem checker_record_lower_node {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) :
    out.getReg .x6=BitVec.ofNat 64 (LENGTH+(checkerRecordInputIndex input record).val) >>> 16 := by
  simp only [checkerRecordLowerTrace,leafQueries,bind_assoc,pure_bind,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨a,_,b,_,last⟩ := reached
  rw [checker_lower_sixteen_node input _ out (checker_record_core_path_ready ready a b) last,
    (checker_record_core_path_ready ready a b).node]
  rfl

theorem checker_record_lower_costs (input : CheckInput) (record : Nat) :
    checkerFirstOrderingInput input record+3656≤3702 ∧
    checkerFirstOrderingInput input record+4300≤4346 := by
  have := checker_first_ordering_input_costs input record
  omega

theorem checker_record_lower_fixed {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (slot : Fin 14)
    (notSize : checkerLowerFixedReg slot≠.x11) (notPrimitive : checkerLowerFixedReg slot≠.x13) :
    out.getReg (checkerLowerFixedReg slot)=s.getReg (checkerLowerFixedReg slot) := by
  simp only [checkerRecordLowerTrace,leafQueries,bind_assoc,pure_bind,mem_support_bind_iff] at reached
  obtain ⟨a,_,b,_,last⟩ := reached
  have pointer : checkerLowerFixedReg slot≠.x21 := by fin_cases slot <;> decide
  have node : checkerLowerFixedReg slot≠.x6 := by fin_cases slot <;> decide
  have counter : checkerLowerFixedReg slot≠.x29 := by fin_cases slot <;> decide
  have temporary : checkerLowerFixedReg slot≠.x31 := by fin_cases slot <;> decide
  have inputReg : checkerLowerFixedReg slot≠.x10 := by fin_cases slot <;> decide
  have outputReg : checkerLowerFixedReg slot≠.x12 := by fin_cases slot <;> decide
  have tag : checkerLowerFixedReg slot≠.x28 := by fin_cases slot <;> decide
  have head : checkerLowerFixedReg slot∉[.x6,.x28,.x10,.x11,.x13] := by
    simp [node,tag,inputReg,notSize,notPrimitive]
  rw [(checker_lower_sixteen_fixed input _ out (checker_record_core_path_ready ready a b) last) slot,
    checker_leaf_path_eq,
    trunc_lower_register _ _ pointer node notSize notPrimitive counter temporary,
    checker_leaf_preserved_register _ _ _ _ _ inputReg outputReg temporary,
    checkerRecordCoreNonceState,checker_copy_register .nonce _ _ temporary,
    checker_record_head_register 6 s (by decide) _ head]

def checkerRecordGroup (input : CheckInput) (record : Nat) : Nat :=
  256+(checkerRecordInputIndex input record).val/65536

theorem checker_record_group_bounds (input : CheckInput) (record : Nat) :
    256≤checkerRecordGroup input record ∧ checkerRecordGroup input record<512 := by
  have small : (checkerRecordInputIndex input record).val<16777216 :=
    (checkerRecordInputIndex input record).isLt
  dsimp only [checkerRecordGroup]
  omega

theorem checker_record_group_shift (input : CheckInput) (record : Nat) :
    BitVec.ofNat 64 (LENGTH+(checkerRecordInputIndex input record).val) >>> 16=
      BitVec.ofNat 64 (checkerRecordGroup input record) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
  have small : (checkerRecordInputIndex input record).val<16777216 :=
    (checkerRecordInputIndex input record).isLt
  have group := (checker_record_group_bounds input record).2
  change ((16777216+(checkerRecordInputIndex input record).val)%18446744073709551616)/65536=
    (checkerRecordGroup input record)%18446744073709551616
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  dsimp only [checkerRecordGroup]
  omega

theorem checker_record_core_nonce_buffer {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (address count : Nat) (lower : 12800≤address) (room : address+count≤2^64) :
    readBuffer (checkerRecordCoreNonceState s) address count=readBuffer s address count := by
  rw [checkerRecordCoreNonceState,checker_copy_buffer_outside .nonce _ base.value 12272 address count
    (checker_record_core_nonce_ready ready) (by have := base.above;omega) room
    (Or.inl (by change 12272+2*8≤address;omega))]
  apply read_buffer_memory_congr
  funext query
  exact checker_record_head_memory 6 s (by decide) query

theorem checker_record_lower_memory {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (word : Nat)
    (lower : 1600≤word) (room : word<2^33) (outside : word<src ∨ src+26≤word) :
    TwoPermutationPrototype.RV64.memoryView out word=TwoPermutationPrototype.RV64.memoryView s word := by
  simp only [checkerRecordLowerTrace,leafQueries,bind_assoc,pure_bind,mem_support_bind_iff] at reached
  obtain ⟨a,_,b,_,last⟩ := reached
  have args := checker_record_core_leaf_ready ready
  have digest : (secondReplyState (checkerRecordCoreNonceState s) src a b).getReg .x23=12288 :=
    (checker_leaf_preserved_register _ _ _ _ .x23 (by decide) (by decide) (by decide)).trans args.destination
  have frame := checker_lower_sixteen_buffer input _ out (checker_record_core_path_ready ready a b)
    last (8*word) 8 (by omega) (by omega)
  rw [TwoPermutationPrototype.Packed.Checker.read_buffer_word,
    TwoPermutationPrototype.Packed.Checker.read_buffer_word] at frame
  rw [frame,checker_leaf_path_eq,trunc_lower_frame _ digest word (by omega) (by omega),
    checker_leaf_frame args a b word room outside (Or.inr (by omega))]
  have nonce := checker_record_core_nonce_buffer ready (8*word) 8 (by omega) (by omega)
  simpa only [TwoPermutationPrototype.Packed.Checker.read_buffer_word] using nonce

theorem checker_record_lower_mark_memory {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (word : Nat)
    (lower : 512≤word) (upper : word<1024) :
    TwoPermutationPrototype.RV64.memoryView out word=TwoPermutationPrototype.RV64.memoryView s word := by
  have numeric : (TwoPermutationPrototype.RV64.wordAddress word).toNat=8*word := by
    change (8*word)%18446744073709551616=8*word
    exact Nat.mod_eq_of_lt (by omega)
  have outside : OutsideLower (TwoPermutationPrototype.RV64.wordAddress word) := {
    aligned:=by rw [numeric];omega
    lower:=by rw [numeric];omega
    room:=by rw [numeric];omega
    region:=Or.inl (by rw [numeric];omega)}
  have nonce : TwoPermutationPrototype.RV64.memoryView (checkerRecordCoreNonceState s) word=
      TwoPermutationPrototype.RV64.memoryView s word := by
    rw [checkerRecordCoreNonceState]
    have copied := checker_copy_buffer_outside .nonce _ base.value 12272 (8*word) 8
      (checker_record_core_nonce_ready ready) (by have := base.above;omega) (by omega) (Or.inr (by omega))
    rw [TwoPermutationPrototype.Packed.Checker.read_buffer_word,
      TwoPermutationPrototype.Packed.Checker.read_buffer_word] at copied
    exact copied.trans (checker_record_head_memory 6 s (by decide) (TwoPermutationPrototype.RV64.wordAddress word))
  simp only [checkerRecordLowerTrace,leafQueries,bind_assoc,pure_bind,mem_support_bind_iff] at reached
  obtain ⟨a,_,b,_,last⟩ := reached
  have args := checker_record_core_leaf_ready ready
  have digest : (secondReplyState (checkerRecordCoreNonceState s) src a b).getReg .x23=12288 :=
    (checker_leaf_preserved_register _ _ _ _ .x23 (by decide) (by decide) (by decide)).trans args.destination
  have frame := checker_lower_sixteen_memory input _ out (checker_record_core_path_ready ready a b)
    last (TwoPermutationPrototype.RV64.wordAddress word) outside
  change TwoPermutationPrototype.RV64.memoryView out word=
    TwoPermutationPrototype.RV64.memoryView
      (checkerLeafPathState (secondReplyState (checkerRecordCoreNonceState s) src a b)) word at frame
  rw [frame,checker_leaf_path_eq,trunc_lower_frame _ digest word (by omega) (by omega),
    checker_leaf_frame args a b word (by omega) (Or.inl (by have := ready.separated;omega)) (Or.inl (by omega))]
  exact nonce

theorem checker_record_lower_buffer {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s out : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (reached : out∈support (checkerRecordLowerTrace input record src s)) (address count : Nat)
    (lower : 12800≤address) (room : address+count≤2^36)
    (outside : address+count≤8*src ∨ 8*(src+26)≤address) :
    readBuffer out address count=readBuffer s address count := by
  apply lower_buffer_bytes
  intro i small
  apply TwoPermutationPrototype.Packed.Checker.byte_eq_of_word_frame
  apply checker_record_lower_memory ready reached ((address+i)/8) (by omega) (by omega)
  rcases outside with before | after
  · left;omega
  · right;omega

end CommitGolfCandidate.Chained.Native.RecordLeaf
