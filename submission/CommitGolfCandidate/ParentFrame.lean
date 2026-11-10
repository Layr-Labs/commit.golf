import CommitGolfCandidate.CommitParents
/-! Counter framing for parent execution. The byte-write commutation proof is reused
from c7e04b79-4cb1-4fb9-bbc3-9d5a95056ac9, OuterHelpers.lean, lines 12–32. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem parent_frame_write {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) (value : Word) :
    writeBits (state.setReg .x20 value) address answer =
      (writeBits state address answer).setReg .x20 value := by
  have byte_reg (s : MachineState) (a : Word) (b : BitVec 8) :
      (s.setReg .x20 value).setByte a b = (s.setByte a b).setReg .x20 value := by
    cases s; rfl
  have fold (indices : List Nat) (current : MachineState) :
      indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) (current.setReg .x20 value) =
      (indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current).setReg .x20 value := by
    induction indices generalizing current with
    | nil => rfl
    | cons i rest ih =>
      simpa only [List.foldl_cons,byte_reg] using ih
        (current.setByte (address + BitVec.ofNat 64 i)
          (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i))))
  unfold writeBits
  rw [fold]
  rfl


/-- The physical parent counter stays zero while the reference counter descends. -/
def parentFrame (state : MachineState) : MachineState := state.setReg .x20 0

theorem parent_frame_self (state : MachineState) (counter : state.getReg .x20=0) :
    parentFrame state=state := by
  unfold parentFrame
  rw [← counter]
  cases state
  simp only [MachineState.getReg,MachineState.setReg]
  congr 1
  funext reg
  cases reg <;> rfl

theorem parent_frame_input (state : MachineState) : oracleInput (parentFrame state)=oracleInput state := by
  cases state
  rfl

theorem parent_pointer_nonzero (base : Word) (n : Nat) (bound : n<2^24) :
    (base+(BitVec.ofNat 64 n <<< 5)=base) ↔ n=0 := by
  have small : n<2^64 := by omega
  have scaled : n*32<2^64 := by omega
  have value : (BitVec.ofNat 64 n <<< 5).toNat=n*32 := by
    simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.shiftLeft_eq]
    norm_num
    omega
  constructor
  · intro equal
    have h := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_add,value] at h
    have size := BitVec.isLt base
    omega
  · rintro rfl
    simp

/-- The reference counter is not an oracle argument and does not affect input bytes. -/
theorem parent_frame_query (state : MachineState) (pc : state.pc=4444)
    (args : ParentArgsReady state)
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (sourceValid : rangeValid (state.getReg .x9+(state.getReg .x20 <<< 6)) 64=true)
    (destinationValid : rangeValid (state.getReg .x9+(state.getReg .x20 <<< 5)) 32=true)
    (sourceAligned : (state.getReg .x9+(state.getReg .x20 <<< 6)).toNat%8=0)
    (destinationAligned : (state.getReg .x9+(state.getReg .x20 <<< 5)).toNat%8=0)
    (fuel : Nat) :
    execute (submission.image .commit) (1+fuel) (parentFrame state) true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel (parentFrame (commitParentState state answer)) true
          return result.charge 8 1) := by
  have fetched : fetch (submission.image .commit) (parentFrame state)=some (.base .ECALL) := by
    apply commit_fetch _ 87 _ (by decide) pc;rfl
  have kind : (state.getReg .x13).toNat=0 := by rw [constants.2.2];rfl
  have input : oracleInput state=some (commitParentQuery state) := by
    simp [oracleInput,kind,commitParentQuery,constants.2.1,constants.2.2,args.1,args.2,
      COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,sourceValid,destinationValid]
    refine ⟨⟨by simpa using sourceAligned,by simpa using destinationAligned⟩,?_⟩
    have width : ((if (state.getReg .x13).toNat=0 then 512 else PERMUTATION_WIDTH)+7)/8=64 := by
      rw [kind];rfl
    rw [width]
    exact BitVec.setWidth_eq _
  have selector : (parentFrame state).getReg .x5=0 := constants.1
  rw [Nat.add_comm 1 fuel,execute,fetched,if_pos selector,parent_frame_input,input]
  simp only [writeOracleAnswer,oracleCycles,COMPRESSION_CYCLES]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (commitParentQuery state))) : OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have output : (parentFrame state).getReg .x12=state.getReg .x9+(state.getReg .x20 <<< 5) := args.2
  rw [output]
  unfold parentFrame commitParentState
  erw [parent_frame_write]
  simp [Execution.charge]
  rfl

/-- The submitted parent suffix updates two pointers and tests the output pointer. -/
def parentPhysicalNext (state : MachineState) : MachineState :=
  ((state.setReg .x10 (state.getReg .x10-64)).setReg .x12 (state.getReg .x12-32)).setPC
    (if state.getReg .x12-32=state.getReg .x9 then 4460 else 4444)

private def parentPhysicalPrefix (state : MachineState) (count : Nat) : MachineState :=
  ([.ADDI .x10 .x10 4032,.ADDI .x12 .x12 4064].take count).foldl execInstrBr state

/-- Three ordinary instructions, including the final untaken branch. -/
theorem parent_physical_next (state : MachineState) (pc : state.pc=4448) (fuel : Nat) :
    execute (submission.image .commit) (3+fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (parentPhysicalNext state) true
          return result.charge 3 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (2+remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (parentPhysicalPrefix state 2) true
            return result.charge 2 0) := by
    apply execute_unit_steps (states := parentPhysicalPrefix state)
    intro i hi
    refine ⟨.base (([.ADDI .x10 .x10 4032,.ADDI .x12 .x12 4064][i]?).getD .EBREAK),?_,?_,?_⟩
    · apply commit_fetch _ (88+i) _ (by omega)
      · interval_cases i <;> simp [parentPhysicalPrefix,execInstrBr,pc,MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (parentPhysicalPrefix state 2)=some (.base (.BNE .x12 .x9 8180)) := by
    apply commit_fetch _ 90 _ (by decide)
    · simp [parentPhysicalPrefix,execInstrBr,pc,MachineState.setPC]
    · rfl
  have stepped : ordinaryStep (parentPhysicalPrefix state 2) (.base (.BNE .x12 .x9 8180))=
      some (parentPhysicalNext state) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,signExtend12,
      parentPhysicalPrefix,parentPhysicalNext,MachineState.getReg,MachineState.setReg,
      MachineState.setPC,pc,BitVec.sub_eq_add_neg]
    split <;> simp_all
  rw [show 3+fuel=2+(fuel+1) by omega,setup,execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles,Execution.charge,← Nat.add_assoc]

/-- Pointer equality and virtual counter equality give the same branch for valid nodes. -/
theorem parent_physical_frame (state : MachineState) (remaining : Nat)
    (counter : state.getReg .x20=BitVec.ofNat 64 (remaining+1))
    (args : ParentArgsReady state) (bound : remaining<2^24) :
    parentPhysicalNext (parentFrame state)=parentFrame (commitParentNextState state) := by
  have nextCounter : state.getReg .x20-1=BitVec.ofNat 64 remaining := by
    rw [counter]
    change BitVec.ofNat 64 (remaining+1)-BitVec.ofNat 64 1=_
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining+1) 1 (by decide) (by omega)]
    congr 1
  have shift (base node : Word) : base+(node <<< 5)-32=base+((node-1) <<< 5) := by
    simp only [BitVec.shiftLeft_eq_mul_twoPow]
    change base+node*32-32=base+(node-1)*32
    rw [BitVec.mul_comm (x := node-1),BitVec.mul_sub]
    simp only [BitVec.mul_comm]
    rw [show (1 : Word)*32=32 by decide]
    rw [BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have pointerZero : (state.getReg .x12-32=state.getReg .x9) ↔ remaining=0 := by
    erw [args.2,shift,nextCounter]
    exact parent_pointer_nonzero _ _ bound
  have counterZero : (state.getReg .x20-1=0) ↔ remaining=0 := by
    rw [nextCounter]
    constructor
    · intro zero
      have h := congrArg BitVec.toNat zero
      change remaining%18446744073709551616=0 at h
      omega
    · rintro rfl;rfl
  have branch : (state.getReg .x12-32=state.getReg .x9) ↔ (state.getReg .x20-1=0) :=
    pointerZero.trans counterZero.symm
  unfold parentPhysicalNext parentFrame commitParentNextState
  simp only [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20≠.x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20≠.x12),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20≠.x9)]
  simp only [branch]
  cases state
  simp only [MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

/-- The physical step follows the canonical query while erasing only its counter. -/
theorem commit_parent_framed (state : MachineState) (remaining : Nat)
    (pc : state.pc=4444) (counter : state.getReg .x20=BitVec.ofNat 64 (remaining+1))
    (args : ParentArgsReady state) (bound : remaining<2^24)
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (sourceValid : rangeValid (state.getReg .x9+(state.getReg .x20 <<< 6)) 64=true)
    (destinationValid : rangeValid (state.getReg .x9+(state.getReg .x20 <<< 5)) 32=true)
    (sourceAligned : (state.getReg .x9+(state.getReg .x20 <<< 6)).toNat%8=0)
    (destinationAligned : (state.getReg .x9+(state.getReg .x20 <<< 5)).toNat%8=0) (fuel : Nat) :
    execute (submission.image .commit) (4+fuel) (parentFrame state) true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel
            (parentFrame (commitParentNextState (commitParentState state answer))) true
          return result.charge 11 1) := by
  rw [show 4+fuel=1+(3+fuel) by omega,
    parent_frame_query state pc args constants sourceValid destinationValid sourceAligned destinationAligned]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (commitParentQuery state))) : OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have postPC : (parentFrame (commitParentState state answer)).pc=4448 := by
    change (commitParentState state answer).pc=_
    rw [commit_parent_pc,pc];rfl
  have postCounter : (commitParentState state answer).getReg .x20=BitVec.ofNat 64 (remaining+1) :=
    (commit_parent_register state answer .x20 (by simp)).trans counter
  have postArgs : ParentArgsReady (commitParentState state answer) := by
    simpa only [ParentArgsReady,commitParentState,writeBits_register] using args
  rw [parent_physical_next _ postPC,parent_physical_frame _ remaining postCounter postArgs bound]
  simp [Execution.charge,← Nat.add_assoc]

end CommitGolfCandidate
