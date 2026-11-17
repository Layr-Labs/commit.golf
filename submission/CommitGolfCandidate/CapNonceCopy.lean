import CommitGolfCandidate.NonceSaltMemory
import CommitGolfCandidate.Execution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def capNonceInstructions : List Instr :=
  [.LD .x6 .x23 0,.SD .x25 .x6 0,.LD .x6 .x23 8,.SD .x25 .x6 8,
   .LD .x6 .x23 16,.SD .x25 .x6 16,.SD .x25 .x0 24]

def capNoncePrefix (state : MachineState) (count : Nat) : MachineState :=
  (capNonceInstructions.take count).foldl execInstrBr state

def capNonceCopyState (state : MachineState) : MachineState := capNoncePrefix state 7

private theorem cap_nonce_getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg=state.getReg reg := by cases reg <;> rfl

private theorem cap_nonce_getMem_setMem (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query=(if query=address then value else state.getMem query) := by
  simp [MachineState.getMem,MachineState.setMem]

theorem cap_nonce_prefix_register (state : MachineState) (count : Nat) (bounded : count≤7)
    (reg : Reg) (notTemporary : reg≠.x6) :
    (capNoncePrefix state count).getReg reg=state.getReg reg := by
  interval_cases count <;>
    simp only [capNoncePrefix,capNonceInstructions,List.take,List.foldl,execInstrBr,
      MachineState.getReg_setPC,cap_nonce_getReg_setMem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

def CapNonceFetched (image : Image) : Prop :=
  ∀ (state : MachineState) (i : Nat),i<7 → state.pc=BitVec.ofNat 64 (4224+4*i) →
    fetch image state=some (.base ((capNonceInstructions[i]?).getD .EBREAK))

theorem cap_nonce_execute (image : Image) (fetched : CapNonceFetched image)
    (state : MachineState) (pc : state.pc = 4224)
    (sourceValid : ∀ word : Fin 3,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (7 + fuel) state allowCoins =
      (do let result ← execute image fuel (capNonceCopyState state) allowCoins
          return result.charge 7 0) := by
  change execute image (7 + fuel) state allowCoins =
    (do let result ← execute image fuel (capNoncePrefix state 7) allowCoins
        return result.charge 7 0)
  apply execute_unit_steps (states := capNoncePrefix state)
  intro i hi
  refine ⟨.base ((capNonceInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetched _ i hi
    interval_cases i <;>
      simp [capNoncePrefix, capNonceInstructions, execInstrBr, pc,
        MachineState.setPC]
  · have source := cap_nonce_prefix_register state i (by omega) .x23 (by decide)
    have destination := cap_nonce_prefix_register state i (by omega) .x25 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (capNoncePrefix state i)
        ((capNonceInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [capNonceInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid,
          memAccess, source, destination, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [capNonceInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem cap_nonce_copy_register (state : MachineState) (reg : Reg) (notTemporary : reg≠.x6) :
    (capNonceCopyState state).getReg reg=state.getReg reg :=
  cap_nonce_prefix_register state 7 (by decide) reg notTemporary

theorem cap_nonce_copy_pc (state : MachineState) :
    (capNonceCopyState state).pc=state.pc+28 := by
  simp [capNonceCopyState,capNoncePrefix,capNonceInstructions,execInstrBr,
    MachineState.setPC,BitVec.add_assoc]

theorem cap_nonce_copy_memory (state : MachineState) :
    (capNonceCopyState state).mem=
      (nonceSaltState ((state.setReg .x18 (state.getReg .x23)).setReg .x10 (state.getReg .x25))).mem := by
  simp [capNonceCopyState,capNoncePrefix,capNonceInstructions,nonceSaltState,
    nonceSaltPrefix,nonceSaltInstructions,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.setPC,MachineState.setMem,MachineState.getMem]

theorem cap_nonce_copy_digest (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x23=BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25=BitVec.ofNat 64 destination)
    (sourceAligned : source%8=0) (destinationAligned : destination%8=0)
    (sourceBound : source+32≤2^64) (destinationBound : destination+32≤2^64)
    (separate : source+32≤destination ∨ destination+32≤source) :
    readBuffer (capNonceCopyState state) destination 32=readNonce state source := by
  rw [nonce_read_buffer_memory_congr _ _ (cap_nonce_copy_memory state)]
  exact nonce_salt_digest ((state.setReg .x18 (state.getReg .x23)).setReg .x10 (state.getReg .x25))
    source destination
    (by simpa [MachineState.getReg,MachineState.setReg] using sourcePointer)
    (by simpa [MachineState.getReg,MachineState.setReg] using destinationPointer)
    sourceAligned destinationAligned sourceBound destinationBound separate

theorem cap_nonce_copy_preserves_digest (state : MachineState) (destination address : Nat)
    (destinationPointer : state.getReg .x25=BitVec.ofNat 64 destination)
    (aligned : address%8=0) (destinationBound : destination+32≤2^64) (readBound : address+32≤2^64)
    (separate : address+32≤destination ∨ destination+32≤address) :
    readBuffer (capNonceCopyState state) address 32=readBuffer state address 32 := by
  rw [nonce_read_buffer_memory_congr _ _ (cap_nonce_copy_memory state)]
  exact nonce_salt_preserves_digest ((state.setReg .x18 (state.getReg .x23)).setReg .x10 (state.getReg .x25))
    destination address (by simpa [MachineState.getReg,MachineState.setReg] using destinationPointer)
    aligned destinationBound readBound separate

theorem cap_nonce_copy_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 4,address≠state.getReg .x25+BitVec.ofNat 64 (8*word.val)) :
    (capNonceCopyState state).getMem address=state.getMem address := by
  change (capNonceCopyState state).mem address=state.mem address
  rw [cap_nonce_copy_memory]
  apply nonce_salt_memory_outside
  intro word
  simpa [MachineState.getReg,MachineState.setReg] using outside word

def capNonceEightState (state : MachineState) : MachineState :=
  (capNonceCopyState state).setPC ((capNonceCopyState state).pc + 4)

theorem cap_nonce_eight_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6) :
    (capNonceEightState state).getReg reg = state.getReg reg := by
  rw [capNonceEightState, MachineState.getReg_setPC]
  exact cap_nonce_copy_register state reg outside

theorem cap_nonce_eight_memory (state : MachineState) :
    (capNonceEightState state).mem = (capNonceCopyState state).mem := by rfl

theorem cap_nonce_eight_pc (state : MachineState) :
    (capNonceEightState state).pc = state.pc + 32 := by
  change (capNonceCopyState state).pc + 4 = state.pc + 32
  rw [cap_nonce_copy_pc]
  simp only [BitVec.add_assoc]
  rfl

theorem cap_nonce_eight_execute (image : Image) (fetched : CapNonceFetched image)
    (nopFetched : ∀ state : MachineState, state.pc = 4252 →
      fetch image state = some (.base (.ADDI .x0 .x0 0)))
    (state : MachineState) (pc : state.pc = 4224)
    (sourceValid : ∀ word : Fin 3,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8*word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8*word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (8+fuel) state allowCoins =
      (do let result ← execute image fuel (capNonceEightState state) allowCoins
          return result.charge 8 0) := by
  have nextPC : (capNonceCopyState state).pc = 4252 := by
    rw [cap_nonce_copy_pc, pc]
    rfl
  rw [show 8+fuel=7+(fuel+1) by omega,
    cap_nonce_execute image fetched state pc sourceValid destinationValid,
    execute_ordinary_step image (.base (.ADDI .x0 .x0 0))
      (capNonceCopyState state) (capNonceEightState state) fuel allowCoins
      (nopFetched _ nextPC) (by
        simp only [ordinaryStep, memoryArgumentsValid, memAccess, ↓reduceIte,
          execInstrBr, MachineState.setReg, capNonceEightState])]
  simp only [instructionCycles, bind_assoc, pure_bind]
  apply bind_congr
  intro result
  congr 1
  simp only [Execution.charge, Nat.zero_add, ← Nat.add_assoc, Nat.reduceAdd]

theorem cap_nonce_eight_digest (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x23 = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (sourceAligned : source%8=0) (destinationAligned : destination%8=0)
    (sourceBound : source+32≤2^64) (destinationBound : destination+32≤2^64)
    (separate : source+32≤destination ∨ destination+32≤source) :
    readBuffer (capNonceEightState state) destination 32 = readNonce state source := by
  rw [nonce_read_buffer_memory_congr _ _ (cap_nonce_eight_memory state)]
  exact cap_nonce_copy_digest state source destination sourcePointer destinationPointer
    sourceAligned destinationAligned sourceBound destinationBound separate

theorem cap_nonce_eight_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 4, address ≠ state.getReg .x25 + BitVec.ofNat 64 (8*word.val)) :
    (capNonceEightState state).getMem address = state.getMem address := by
  change (capNonceEightState state).mem address = state.mem address
  rw [cap_nonce_eight_memory]
  exact cap_nonce_copy_memory_outside state address outside

end CommitGolfCandidate
