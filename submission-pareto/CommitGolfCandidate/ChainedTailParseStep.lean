import CommitGolfCandidate.ChainedTailParseCode

/-! One inverse row: load width, parse a field, store its byte, and branch. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def tailWidthState (s : MachineState) : MachineState := execInstrBr s (.LBU .x26 .x21 1)
def tailParseRead (s : MachineState) : MachineState := tailReadState (tailWidthState s)
def tailParsedStoreOps : List Instr := [.SB .x21 .x24 0,.ADDI .x21 .x21 2]
def tailParsedStoreOp (index : Nat) : Instr := (tailParsedStoreOps[index]?).getD .EBREAK
def tailParsedStorePrefix (s : MachineState) (count : Nat) : MachineState :=
  (tailParsedStoreOps.take count).foldl execInstrBr s
def tailParseStored (s : MachineState) : MachineState := tailParsedStorePrefix (tailParseRead s) 2
def tailParseDecreased (s : MachineState) : MachineState := tailDecrease (tailParseStored s)
def tailParseBack (s : MachineState) : MachineState := execInstrBr s (.BNE .x22 .x0 8128)
def tailParseStepState (s : MachineState) : MachineState := tailParseBack (tailParseDecreased s)
def tailParseStepCycles (s : MachineState) : Nat := 5+tailReadCycles (tailWidthState s)

theorem tail_width_register (s : MachineState) (reg : Reg) (width : reg≠.x26) :
    (tailWidthState s).getReg reg = s.getReg reg := by
  cases reg <;> first | contradiction | rfl

theorem tail_width_pc (s : MachineState) : (tailWidthState s).pc=s.pc+4 := rfl

theorem tail_parse_read_pc (s : MachineState) : (tailParseRead s).pc=s.pc+52 := by
  rw [tailParseRead,tail_read_end_pc,tail_width_pc,BitVec.add_assoc]
  rfl

theorem tail_parsed_store_pc (s : MachineState) (count : Nat) (small : count≤2) :
    (tailParsedStorePrefix s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count
  · simp [tailParsedStorePrefix]
  · rfl
  · change (s.pc+4#64)+4#64=s.pc+8#64
    rw [BitVec.add_assoc]
    rfl

theorem tail_parse_stored_pc (s : MachineState) : (tailParseStored s).pc=s.pc+60 := by
  rw [tailParseStored,tail_parsed_store_pc _ 2 (by decide),tail_parse_read_pc,BitVec.add_assoc]
  rfl

theorem tail_parse_decreased_pc (s : MachineState) : (tailParseDecreased s).pc=s.pc+64 := by
  change (tailParseStored s).pc+4=_
  rw [tail_parse_stored_pc,BitVec.add_assoc]
  rfl

theorem tail_parse_back_pc (s : MachineState) : (tailParseBack s).pc =
    if tailMore s then s.pc+signExtend13 8128 else s.pc+4 := by
  change (if tailMore s then s.setPC (s.pc+signExtend13 8128) else s.setPC (s.pc+4)).pc = _
  split <;> rfl

theorem tail_parse_step_pc (s : MachineState) (base : Word) (pc : s.pc=base+4) :
    (tailParseStepState s).pc = if tailMore (tailParseDecreased s) then base+4 else base+72 := by
  rw [tailParseStepState,tail_parse_back_pc,tail_parse_decreased_pc,pc]
  split <;> rw [BitVec.add_assoc,BitVec.add_assoc] <;> rfl

private theorem store_prefix_succ (s : MachineState) (count : Nat) (inside : count<2) :
    tailParsedStorePrefix s (count+1) = execInstrBr (tailParsedStorePrefix s count) (tailParsedStoreOp count) := by
  interval_cases count <;> rfl

theorem tail_parsed_store_execution (image : Image) (base : Word) (code : TailParseAt image base)
    (s : MachineState) (pc : s.pc=base+56) (valid : accessValid (s.getReg .x21) 1=true)
    (fuel : Nat) (coins : Bool) :
    execute image (2+fuel) s coins =
      (do let result ← execute image fuel (tailParsedStorePrefix s 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := tailParsedStorePrefix s)
  intro i inside
  refine ⟨.base (tailParsedStoreOp i),?_,?_,?_⟩
  · have op : tailParseOp (14+i) = tailParsedStoreOp i := by interval_cases i <;> rfl
    have location : (tailParsedStorePrefix s i).pc=base+BitVec.ofNat 64 (4*(14+i)) := by
      rw [tail_parsed_store_pc s i (by omega),pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
      rfl
    simpa only [op] using code ⟨14+i,by omega⟩ _ location
  · rw [store_prefix_succ s i inside]
    interval_cases i
    · simpa [ordinaryStep,memoryArgumentsValid,memAccess,tailParsedStorePrefix,tailParsedStoreOp,
        tailParsedStoreOps,signExtend12] using valid
    · rfl
  · interval_cases i <;> rfl

theorem tail_parse_step_execution (image : Image) (base : Word) (code : TailParseAt image base)
    (s : MachineState) (pc : s.pc=base+4)
    (width : accessValid (s.getReg .x21+1) 1=true)
    (valid : tailNeedsByte (tailWidthState s) → accessValid ((tailWidthState s).getReg .x20) 1=true)
    (store : accessValid ((tailParseRead s).getReg .x21) 1=true) (fuel : Nat) (coins : Bool) :
    execute image (tailParseStepCycles s+fuel) s coins =
      (do let result ← execute image fuel (tailParseStepState s) coins
          return result.charge (tailParseStepCycles s) 0) := by
  have loadFetch : fetch image s=some (.base (.LBU .x26 .x21 1)) := by
    apply code ⟨1,by decide⟩
    simpa using pc
  have loadStep : ordinaryStep s (.base (.LBU .x26 .x21 1))=some (tailWidthState s) := by
    have access : memoryArgumentsValid s (.LBU .x26 .x21 1)=true := by
      change accessValid (s.getReg .x21+1) 1=true
      exact width
    simp only [ordinaryStep,access,↓reduceIte]
    rfl
  have loadedPc : (tailWidthState s).pc=base+8 := by
    rw [tail_width_pc,pc,BitVec.add_assoc]
    rfl
  have readPc : (tailParseRead s).pc=base+56 := by
    rw [tail_parse_read_pc,pc,BitVec.add_assoc]
    rfl
  have downFetch : fetch image (tailParseStored s)=some (.base (.ADDI .x22 .x22 4095)) := by
    apply code ⟨16,by decide⟩
    rw [tail_parse_stored_pc,pc,BitVec.add_assoc]
    rfl
  have backFetch : fetch image (tailParseDecreased s)=some (.base (.BNE .x22 .x0 8128)) := by
    apply code ⟨17,by decide⟩
    rw [tail_parse_decreased_pc,pc,BitVec.add_assoc]
    rfl
  have downStep : ordinaryStep (tailParseStored s) (.base (.ADDI .x22 .x22 4095))=some (tailParseDecreased s) := rfl
  have backStep : ordinaryStep (tailParseDecreased s) (.base (.BNE .x22 .x0 8128))=some (tailParseStepState s) := rfl
  rw [show tailParseStepCycles s+fuel =
      (tailReadCycles (tailWidthState s)+(2+((fuel+1)+1)))+1 by unfold tailParseStepCycles; omega,
    execute_ordinary_step image _ _ _ _ coins loadFetch loadStep,
    tail_read_execution image (base+8) code.read _ loadedPc valid]
  simp only [bind_assoc,pure_bind]
  change (do let result ← execute image (2+((fuel+1)+1)) (tailParseRead s) coins
             return (result.charge (tailReadCycles (tailWidthState s)) 0).charge 1 0) = _
  rw [tail_parsed_store_execution image base code _ readPc store]
  simp only [bind_assoc,pure_bind]
  change (do let result ← execute image ((fuel+1)+1) (tailParseStored s) coins
             return ((result.charge 2 0).charge (tailReadCycles (tailWidthState s)) 0).charge 1 0) = _
  rw [execute_ordinary_step image _ _ _ (fuel+1) coins downFetch downStep,
    execute_ordinary_step image _ _ _ fuel coins backFetch backStep]
  simp [tailParseStepCycles,Execution.charge,instructionCycles,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  have cycles : 1+(2+(2+tailReadCycles (tailWidthState s)))=5+tailReadCycles (tailWidthState s) := by omega
  simp only [cycles]

theorem tail_parse_step_bound (s : MachineState) : tailParseStepCycles s≤17 := by
  unfold tailParseStepCycles tailReadCycles
  split <;> omega

end CommitGolfCandidate.Chained.Native
