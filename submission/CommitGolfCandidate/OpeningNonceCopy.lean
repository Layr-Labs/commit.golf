import CommitGolfCandidate.NonceSaltMemory
import CommitGolfCandidate.Execution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def openingNonceInstructions : List Instr :=
  [.LD .x6 .x23 0,.SD .x25 .x6 0,.LD .x6 .x23 8,.SD .x25 .x6 8,
   .LD .x6 .x23 16,.SD .x25 .x6 16,.SD .x25 .x0 24]

def openingNoncePrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingNonceInstructions.take count).foldl execInstrBr state

def openingNonceCopyState (state : MachineState) : MachineState := openingNoncePrefix state 7

private theorem opening_nonce_getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg=state.getReg reg := by cases reg <;> rfl

private theorem opening_nonce_getMem_setMem (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query=(if query=address then value else state.getMem query) := by
  simp [MachineState.getMem,MachineState.setMem]

theorem opening_nonce_prefix_register (state : MachineState) (count : Nat) (bounded : count≤7)
    (reg : Reg) (notTemporary : reg≠.x6) :
    (openingNoncePrefix state count).getReg reg=state.getReg reg := by
  interval_cases count <;>
    simp only [openingNoncePrefix,openingNonceInstructions,List.take,List.foldl,execInstrBr,
      MachineState.getReg_setPC,opening_nonce_getReg_setMem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

def OpeningNonceFetched (image : Image) : Prop :=
  ∀ (state : MachineState) (i : Nat),i<7 → state.pc=BitVec.ofNat 64 (4196+4*i) →
    fetch image state=some (.base ((openingNonceInstructions[i]?).getD .EBREAK))

theorem opening_nonce_execute (image : Image) (fetched : OpeningNonceFetched image)
    (state : MachineState) (pc : state.pc = 4196)
    (sourceValid : ∀ word : Fin 3,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (7 + fuel) state allowCoins =
      (do let result ← execute image fuel (openingNonceCopyState state) allowCoins
          return result.charge 7 0) := by
  change execute image (7 + fuel) state allowCoins =
    (do let result ← execute image fuel (openingNoncePrefix state 7) allowCoins
        return result.charge 7 0)
  apply execute_unit_steps (states := openingNoncePrefix state)
  intro i hi
  refine ⟨.base ((openingNonceInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetched _ i hi
    interval_cases i <;>
      simp [openingNoncePrefix, openingNonceInstructions, execInstrBr, pc,
        MachineState.setPC]
  · have source := opening_nonce_prefix_register state i (by omega) .x23 (by decide)
    have destination := opening_nonce_prefix_register state i (by omega) .x25 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (openingNoncePrefix state i)
        ((openingNonceInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [openingNonceInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid,
          memAccess, source, destination, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [openingNonceInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem opening_nonce_copy_register (state : MachineState) (reg : Reg) (notTemporary : reg≠.x6) :
    (openingNonceCopyState state).getReg reg=state.getReg reg :=
  opening_nonce_prefix_register state 7 (by decide) reg notTemporary

theorem opening_nonce_copy_pc (state : MachineState) :
    (openingNonceCopyState state).pc=state.pc+28 := by
  simp [openingNonceCopyState,openingNoncePrefix,openingNonceInstructions,execInstrBr,
    MachineState.setPC,BitVec.add_assoc]

theorem opening_nonce_copy_memory (state : MachineState) :
    (openingNonceCopyState state).mem=
      (nonceSaltState ((state.setReg .x18 (state.getReg .x23)).setReg .x10 (state.getReg .x25))).mem := by
  simp [openingNonceCopyState,openingNoncePrefix,openingNonceInstructions,nonceSaltState,
    nonceSaltPrefix,nonceSaltInstructions,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.setPC,MachineState.setMem,MachineState.getMem]

theorem opening_nonce_copy_digest (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x23=BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25=BitVec.ofNat 64 destination)
    (sourceAligned : source%8=0) (destinationAligned : destination%8=0)
    (sourceBound : source+32≤2^64) (destinationBound : destination+32≤2^64)
    (separate : source+32≤destination ∨ destination+32≤source) :
    readBuffer (openingNonceCopyState state) destination 32=readNonce state source := by
  rw [nonce_read_buffer_memory_congr _ _ (opening_nonce_copy_memory state)]
  exact nonce_salt_digest ((state.setReg .x18 (state.getReg .x23)).setReg .x10 (state.getReg .x25))
    source destination
    (by simpa [MachineState.getReg,MachineState.setReg] using sourcePointer)
    (by simpa [MachineState.getReg,MachineState.setReg] using destinationPointer)
    sourceAligned destinationAligned sourceBound destinationBound separate

theorem opening_nonce_copy_preserves_digest (state : MachineState) (destination address : Nat)
    (destinationPointer : state.getReg .x25=BitVec.ofNat 64 destination)
    (aligned : address%8=0) (destinationBound : destination+32≤2^64) (readBound : address+32≤2^64)
    (separate : address+32≤destination ∨ destination+32≤address) :
    readBuffer (openingNonceCopyState state) address 32=readBuffer state address 32 := by
  rw [nonce_read_buffer_memory_congr _ _ (opening_nonce_copy_memory state)]
  exact nonce_salt_preserves_digest ((state.setReg .x18 (state.getReg .x23)).setReg .x10 (state.getReg .x25))
    destination address (by simpa [MachineState.getReg,MachineState.setReg] using destinationPointer)
    aligned destinationBound readBound separate

theorem opening_nonce_copy_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 4,address≠state.getReg .x25+BitVec.ofNat 64 (8*word.val)) :
    (openingNonceCopyState state).getMem address=state.getMem address := by
  change (openingNonceCopyState state).mem address=state.mem address
  rw [opening_nonce_copy_memory]
  apply nonce_salt_memory_outside
  intro word
  simpa [MachineState.getReg,MachineState.setReg] using outside word

end CommitGolfCandidate
