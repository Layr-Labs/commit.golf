import CommitGolfCandidate.PhaseLayout
import CommitGolfCandidate.PhaseMemory
import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProjectedHalfword
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

private theorem small_sign (n : Nat) (h : n<128) : signExtend12 (BitVec.ofNat 12 n)=addr n := by
  exact (show ∀ k : Fin 128, signExtend12 (BitVec.ofNat 12 k.val)=addr k.val by decide) ⟨n,h⟩

def moveRead (s : MachineState) (w : Nat) (sa : Word) : Word :=
  if w=8 then s.getMem sa else if w=4 then (s.getWord32 sa).zeroExtend 64
  else (s.getHalfword sa).zeroExtend 64

def moveWrite (s : MachineState) (w : Nat) (da data : Word) : MachineState :=
  if w=8 then s.setMem da data else if w=4 then s.setWord32 da (data.truncate 32)
  else s.setHalfword da (data.truncate 16)

def moveState (s : MachineState) (w src dst : Nat) : MachineState :=
  let rd := moveRead s w (addr src)
  (moveWrite (s.setReg .x31 rd) w (addr dst) rd).setPC (s.pc+8)

/-- End-to-end equality of all memory cells, including any cells outside ordinary aligned-word
 observation. This justifies reusing the old halfword serializer's byte and memory frames. -/
theorem move_memory (s : MachineState) (w src dst : Nat) (width : w=2 ∨ w=4 ∨ w=8)
    (fromAligned : src%w=0) (toAligned : dst%w=0) (apart : src+w≤dst) (fits : dst+w≤2^64) :
    (moveState s w src dst).mem=(copyLoopMemory false (w/2) s (addr src) (addr dst)).mem := by
  rcases width with rfl|rfl|rfl
  · simp [moveState,moveRead,moveWrite,copyLoopMemory,MachineState.setReg, MachineState.setPC,
      MachineState.getHalfword,MachineState.setHalfword,MachineState.setMem,MachineState.getMem]
  · rw [show 4/2=2 by decide,word_halfwords s _ _ fromAligned toAligned apart fits]
    simp [moveState,moveRead,moveWrite,MachineState.setReg,MachineState.setPC,
      MachineState.setWord32, MachineState.setMem, MachineState.getMem]
  · rw [show 8/2=4 by decide,dword_halfwords s _ _ fromAligned toAligned apart fits]
    rfl

theorem move_register (s : MachineState) (w src dst : Nat) (r : Reg) (kept : r ≠ .x31) :
    (moveState s w src dst).getReg r=s.getReg r := by
  simp only [moveState,moveWrite,MachineState.getReg_setPC]
  split <;> try split
  all_goals simp [MachineState.setWord32,MachineState.setHalfword,Opening.getReg_setMem,
    Opening.getReg_setReg,Ne.symm kept]

theorem move_pc (s : MachineState) (w src dst : Nat) : (moveState s w src dst).pc=s.pc+8 := rfl

def PairRun (im : Image) (s u : MachineState) (n : Nat) : Prop := ∀ fuel coins,
  execute im (n+fuel) s coins = do
    let z ← execute im fuel u coins
    return z.charge n 0

private theorem access (n w : Nat) (bound : n+w≤MEMORY_BYTES) (aligned : n%w=0) :
    accessValid (addr n) w=true := by
  have room : MEMORY_BYTES<2^64 := by decide
  simp only [accessValid,rangeValid,addr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : n<2^64),
    Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨bound,aligned⟩

theorem move_run (im : Image) (s : MachineState) (f : Fin 18) (w offset toOffset src dst : Nat)
    (width : w=2 ∨ w=4 ∨ w=8) (sourceAddr : s.getReg (srcReg f)+addr offset=addr src)
    (destAddr : s.getReg .x21+addr toOffset=addr dst) (offS : offset<128) (offD : toOffset<128)
    (sv : src+w≤MEMORY_BYTES) (dv : dst+w≤MEMORY_BYTES) (sa : src%w=0) (da : dst%w=0)
    (fetchL : fetch im s=some (.base (loadWidth w f offset)))
    (fetchS : ∀ t : MachineState, t.pc=s.pc+4 → fetch im t=some (.base (saveWidth w toOffset))) :
    PairRun im s (moveState s w src dst) 2 := by
  let rd := moveRead s w (addr src)
  let l := (s.setReg .x31 rd).setPC (s.pc+4)
  have ds : l.getReg .x21+addr toOffset=addr dst := by
    simpa [l, Opening.getReg_setReg,MachineState.getReg_setPC] using destAddr
  have datum : l.getReg .x31=rd := by simp [l,Opening.getReg_setReg,MachineState.getReg_setPC]
  have read := access src w sv sa
  have write := access dst w dv da
  have hls : ordinaryStep s (.base (loadWidth w f offset))=some l := by
    rcases width with h|h|h <;> subst w <;>
    simp [loadWidth,ordinaryStep,memoryArgumentsValid,memAccess,small_sign offset offS,sourceAddr,
      read,execInstrBr,moveRead,l,rd]
  have store : ordinaryStep l (.base (saveWidth w toOffset))=some (moveState s w src dst) := by
    have off : l.getReg .x21+signExtend12 (BitVec.ofNat 12 toOffset)=addr dst := by
      rw [small_sign toOffset offD]; exact ds
    rcases width with h|h|h
    · subst w
      change ordinaryStep l (.base (.SH .x21 .x31 (BitVec.ofNat 12 toOffset)))=_
      simp only [ordinaryStep,memoryArgumentsValid,memAccess,off,write,↓reduceIte,execInstrBr,datum]
      simp [l,rd,moveRead,moveWrite,moveState,MachineState.setPC,MachineState.setHalfword,
        MachineState.setMem,MachineState.getMem,BitVec.add_assoc]
    · subst w
      change ordinaryStep l (.base (.SW .x21 .x31 (BitVec.ofNat 12 toOffset)))=_
      simp only [ordinaryStep,memoryArgumentsValid,memAccess,off,write,↓reduceIte,execInstrBr,datum]
      simp [l,rd,moveRead,moveWrite,moveState,MachineState.setPC,MachineState.setWord32,
        MachineState.setMem,MachineState.getMem,BitVec.add_assoc]
    · subst w
      change ordinaryStep l (.base (.SD .x21 .x31 (BitVec.ofNat 12 toOffset)))=_
      simp only [ordinaryStep,memoryArgumentsValid,memAccess,off,write,↓reduceIte,execInstrBr,datum]
      simp [l,rd,moveRead,moveWrite,moveState,MachineState.setPC,MachineState.setMem,BitVec.add_assoc]
  have lCost : instructionCycles (.base (loadWidth w f offset)) = 1 := by
    rcases width with rfl|rfl|rfl <;> rfl
  have sCost : instructionCycles (.base (saveWidth w toOffset)) = 1 := by
    rcases width with rfl|rfl|rfl <;> rfl
  intro fuel coins
  have first:=CommitGolfCandidate.execute_ordinary_step im _ s l (fuel+1) coins fetchL hls
  have second:=CommitGolfCandidate.execute_ordinary_step im _ l (moveState s w src dst) fuel coins (fetchS l rfl) store
  rw [show 2+fuel=(fuel+1)+1 by omega,first,second,lCost,sCost]
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc]

#print axioms move_run
#print axioms move_memory
end TwoPermutationPrototype.PhaseOpening
