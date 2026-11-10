import CommitGolfCandidate.Commit
import CommitGolfCandidate.WriteMemory

/-! Bottom-up parent construction and successful commitment return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev commitParentQuery (state : MachineState) : PublicSpec.Domain :=
  .inl (readBuffer state (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat 64)

private theorem parent_read_fixed_width (state : MachineState) (address width : Nat)
    (selected : width = 64) :
    BitVec.setWidth 512 (readBuffer state address width) = readBuffer state address 64 := by
  subst width
  exact BitVec.setWidth_eq _

private def parentInstructions : List Instr :=
  [.SLLI .x6 .x20 6, .ADD .x10 .x9 .x6, .SLLI .x7 .x20 5, .ADD .x12 .x9 .x7]

private def parentPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentInstructions.take count).foldl execInstrBr state

/-- Persistent input and output pointers name the current descending heap node. -/
def ParentArgsReady (state : MachineState) : Prop :=
  state.getReg .x10=state.getReg .x9+(state.getReg .x20 <<< 6) ∧
  state.getReg .x12=state.getReg .x9+(state.getReg .x20 <<< 5)

def commitParentInitState (state : MachineState) : MachineState := parentPrefix state 4

/-- The canonical initialization remains a pure reference operation. -/
theorem commit_parent_init_expansion (state : MachineState) :
    commitParentInitState state=
      ([.SLLI .x6 .x20 6,.ADD .x10 .x9 .x6,.SLLI .x7 .x20 5,.ADD .x12 .x9 .x7] : List Instr).foldl execInstrBr state := rfl

theorem commit_parent_init_register (state : MachineState) (reg : Reg)
    (preserved : reg ∈ [Reg.x9,.x19,.x20,.x21,.x26,.x5,.x11,.x13]) :
    (commitParentInitState state).getReg reg=state.getReg reg := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at preserved
  rcases preserved with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [commitParentInitState,parentPrefix,parentInstructions,execInstrBr,
      MachineState.getReg,MachineState.setReg,MachineState.setPC]

theorem commit_parent_init_ready (state : MachineState) : ParentArgsReady (commitParentInitState state) := by
  simp [ParentArgsReady,commitParentInitState,parentPrefix,parentInstructions,execInstrBr,
    MachineState.getReg,MachineState.setReg,MachineState.setPC]

def commitParentState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits state (state.getReg .x9+(state.getReg .x20 <<< 5)) answer

/-- The parent's setup instructions do not change memory; its only write is the
compression reply at the parent heap slot. -/
theorem commit_parent_written_memory (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).mem =
      (writeBits state (state.getReg .x9+(state.getReg .x20 <<< 5)) answer).mem :=
  rfl

/-- The current pointers are already prepared. Compression costs eight cycles. -/
theorem commit_parent_compression (state : MachineState) (pc : state.pc=4444)
    (args : ParentArgsReady state)
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (sourceValid : rangeValid (state.getReg .x9+(state.getReg .x20 <<< 6)) 64=true)
    (destinationValid : rangeValid (state.getReg .x9+(state.getReg .x20 <<< 5)) 32=true)
    (sourceAligned : (state.getReg .x9+(state.getReg .x20 <<< 6)).toNat%8=0)
    (destinationAligned : (state.getReg .x9+(state.getReg .x20 <<< 5)).toNat%8=0)
    (fuel : Nat) :
    execute (submission.image .commit) (1+fuel) state true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel (commitParentState state answer) true
          return result.charge 8 1) := by
  have fetched : fetch (submission.image .commit) state=some (.base .ECALL) := by
    apply commit_fetch _ 87 _ (by decide) pc; rfl
  have kind : (state.getReg .x13).toNat=0 := by rw [constants.2.2]; rfl
  have input : oracleInput state=some (commitParentQuery state) := by
    simp [oracleInput,kind,commitParentQuery,constants.2.1,constants.2.2,args.1,args.2,
      COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,sourceValid,destinationValid]
    refine ⟨⟨by simpa using sourceAligned,by simpa using destinationAligned⟩,?_⟩
    have width : ((if (state.getReg .x13).toNat=0 then 512 else PERMUTATION_WIDTH)+7)/8=64 := by
      rw [kind]; rfl
    exact parent_read_fixed_width state _ _ width
  rw [Nat.add_comm 1 fuel,execute,fetched,if_pos constants.1,input]
  simp [commitParentQuery,writeOracleAnswer,args.2,commitParentState,oracleCycles,
    COMPRESSION_CYCLES,Execution.charge]
  rfl

theorem commit_parent_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).pc=state.pc+4 := rfl

theorem commit_parent_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∈ [Reg.x9,.x19,.x20,.x21,.x26,.x5,.x11,.x13]) :
    (commitParentState state answer).getReg reg=state.getReg reg := writeBits_register _ _ _ _

def commitParentNextState (state : MachineState) : MachineState :=
  (((state.setReg .x10 (state.getReg .x10-64)).setReg .x12 (state.getReg .x12-32)).setReg .x20
    (state.getReg .x20-1)).setPC (if state.getReg .x20-1=0 then 4460 else 4444)


end CommitGolfCandidate
