import CommitGolfCandidate.NonceEncoding
import CommitGolfCandidate.Execution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def nonceSaltInstructions : List Instr :=
  [.LD .x6 .x18 0,.SD .x10 .x6 0,.LD .x6 .x18 8,.SD .x10 .x6 8,
   .LD .x6 .x18 16,.SD .x10 .x6 16,.SD .x10 .x0 24]

def nonceSaltPrefix (state : MachineState) (count : Nat) : MachineState :=
  (nonceSaltInstructions.take count).foldl execInstrBr state

def nonceSaltState (state : MachineState) : MachineState := nonceSaltPrefix state 7

def nonceVirtualSaltState (state : MachineState) : MachineState :=
  ([.LD .x6 .x18 0,.SD .x10 .x6 0,.LD .x6 .x18 8,.SD .x10 .x6 8,
    .LD .x6 .x18 16,.SD .x10 .x6 16,.ADDI .x6 .x6 0,.SD .x10 .x0 24] : List Instr).foldl execInstrBr state

theorem nonce_salt_virtual (state : MachineState) :
    nonceSaltState state=(nonceVirtualSaltState state).setPC (state.pc+28) := by
  cases state
  dsimp [nonceSaltState,nonceSaltPrefix,nonceSaltInstructions,nonceVirtualSaltState,
    execInstrBr,signExtend12,MachineState.setPC,MachineState.setReg,MachineState.getReg,
    MachineState.getMem,MachineState.setMem]
  simp only [BitVec.add_assoc,BitVec.add_zero]
  congr 1
  funext reg
  cases reg <;> rfl

private theorem nonce_getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg=state.getReg reg := by cases reg <;> rfl

private theorem nonce_getMem_setMem (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query=(if query=address then value else state.getMem query) := by
  simp [MachineState.getMem,MachineState.setMem]

theorem nonce_salt_prefix_register (state : MachineState) (count : Nat) (bounded : count≤7)
    (reg : Reg) (notTemporary : reg≠.x6) :
    (nonceSaltPrefix state count).getReg reg=state.getReg reg := by
  interval_cases count <;>
    simp only [nonceSaltPrefix,nonceSaltInstructions,List.take,List.foldl,execInstrBr,
      MachineState.getReg_setPC,nonce_getReg_setMem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

def NonceSaltFetched (image : Image) : Prop :=
  ∀ (state : MachineState) (i : Nat),i<7 → state.pc=BitVec.ofNat 64 (4456+4*i) →
    fetch image state=some (.base ((nonceSaltInstructions[i]?).getD .EBREAK))

theorem nonce_salt_execute (image : Image) (fetched : NonceSaltFetched image)
    (state : MachineState) (pc : state.pc = 4456)
    (sourceValid : ∀ word : Fin 3,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x10 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute image (7 + fuel) state true =
      (do let result ← execute image fuel (nonceSaltState state) true
          return result.charge 7 0) := by
  change execute image (7 + fuel) state true =
    (do let result ← execute image fuel (nonceSaltPrefix state 7) true
        return result.charge 7 0)
  apply execute_unit_steps (states := nonceSaltPrefix state)
  intro i hi
  refine ⟨.base ((nonceSaltInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetched _ i hi
    interval_cases i <;>
      simp [nonceSaltPrefix, nonceSaltInstructions, execInstrBr, pc,
        MachineState.setPC]
  · have source := nonce_salt_prefix_register state i (by omega) .x18 (by decide)
    have destination := nonce_salt_prefix_register state i (by omega) .x10 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (nonceSaltPrefix state i)
        ((nonceSaltInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [nonceSaltInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid,
          memAccess, source, destination, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [nonceSaltInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate
