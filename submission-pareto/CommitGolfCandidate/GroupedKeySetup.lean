import CommitGolfCandidate.GroupedInvariant
import CommitGolfCandidate.TwoPermutationCommitSetup

/-! P4 commit prologue (words 0-20): registers, the 24-byte key drawn by RANDOM into the key block K+8
(K = trapdoor + 80·LENGTH, word `keyWord`), the centered heap pointer and the sentinel. The state after
word 20 is the grouped leaf scan's `Live` state at leaf 0. Modelled on c28dd9ca's `NonceChainSetup`. -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 60000
set_option maxHeartbeats 1000000

abbrev Key := BitVec 192

def keyOps : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 0,.LUI .x19 131072,
   .ADD .x20 .x9 .x19,.ADD .x21 .x20 .x19,.LUI .x24 327680,.ADD .x24 .x9 .x24,
   .ADDI .x24 .x24 0,.ADDI .x5 .x0 2,.ADDI .x10 .x24 8,.ADDI .x11 .x0 24]
def readyOps : List Instr :=
  [.ADDI .x5 .x0 0,.ADDI .x11 .x0 200,.ADDI .x13 .x0 1,.SLLI .x7 .x13 11,
   .ADD .x20 .x20 .x7,.ADD .x28 .x21 .x7,.SLLI .x7 .x7 1,.ADDI .x10 .x18 0]

def keySetup (s : MachineState) := keyOps.foldl execInstrBr s
def keyWritten (s : MachineState) (k : BitVec 192) := writeBits (keySetup s) (wordAddress (keyWord+1)) k
def keyReady (s : MachineState) (k : BitVec 192) := readyOps.foldl execInstrBr (keyWritten s k)

theorem key_run (s : MachineState) (pc : s.pc=4096) (fuel : Nat) :
    execute image (12+fuel) s true =
      (do let result ← execute image fuel (keySetup s) true
          return result.charge 12 0) := by
  unfold keySetup
  apply execute_unit_steps (states := fun i => (keyOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((keyOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply fetch_decoded _ i (by omega)
    · interval_cases i <;>
        simp only [keyOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    · interval_cases i <;> decide +kernel
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem ready_run (s : MachineState) (pc : s.pc=4148) (fuel : Nat) :
    execute image (8+fuel) s true =
      (do let result ← execute image fuel (readyOps.foldl execInstrBr s) true
          return result.charge 8 0) := by
  apply execute_unit_steps (states := fun i => (readyOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((readyOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply fetch_decoded _ (13+i) (by omega)
    · interval_cases i <;>
        simp only [readyOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    · interval_cases i <;> decide +kernel
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

structure KeyRegisters (s : MachineState) : Prop where
  out : s.getReg .x8 = 4294971392
  heap : s.getReg .x9 = 4294971424
  source : s.getReg .x18 = 4096
  stride : s.getReg .x19 = 536870912
  leaves : s.getReg .x20 = wordAddress (leafDest 0)
  stop : s.getReg .x21 = wordAddress (leafDest (2^24))
  key : s.getReg .x24 = wordAddress keyWord
  target : s.getReg .x10 = wordAddress (keyWord+1)
  size : s.getReg .x11 = 24
  selector : s.getReg .x5 = 2

theorem key_registers (s : MachineState) (entry : CommitEntry s) : KeyRegisters (keySetup s) := by
  constructor <;>
    dsimp [keySetup,keyOps,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [show s.regs .x10=4096 from entry.message,
    show s.regs .x11=4294971392 from entry.commitment,show s.regs .x12=4294971424 from entry.heap]
  all_goals rfl

theorem key_pc (s : MachineState) (pc : s.pc=4096) : (keySetup s).pc=4144 := by
  change s.pc+4+4+4+4+4+4+4+4+4+4+4+4=_
  rw [pc];rfl

theorem key_draw (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (1+fuel) (keySetup s) true =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let result ← execute image fuel (keyWritten s k) true
          return result.charge 4 0) := by
  have r := key_registers s e
  have pc' : (keySetup s).pc=BitVec.ofNat 64 (4096+4*12) := key_pc s e.pc
  have fetched := fetch_decoded (keySetup s) 12 (by decide) pc' .ECALL (by decide +kernel)
  have valid : randomArgumentsValid (keySetup s) = true := by
    rw [randomArgumentsValid,r.target,r.size];decide
  have raw :
      execute image (1+fuel) (keySetup s) true =
        (do let k ← liftM ($ᵗ BitVec (8*((keySetup s).getReg .x11).toNat) :
              ProbComp (BitVec (8*((keySetup s).getReg .x11).toNat)))
            let result ← execute image fuel
              (writeBits (keySetup s) ((keySetup s).getReg .x10) k) true
            return result.charge (1+(((keySetup s).getReg .x11).toNat+7)/8) 0) := by
    rw [Nat.add_comm 1 fuel,execute,fetched]
    simp only [r.selector,valid]
    rfl
  rw [r.size,r.target] at raw
  exact raw

theorem prologue_run (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (21+fuel) s true =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let result ← execute image fuel (keyReady s k) true
          return result.charge 24 0) := by
  rw [show 21+fuel=12+(1+(8+fuel)) by omega,key_run s e.pc,key_draw s e]
  simp only [bind_assoc]
  apply bind_congr;intro k
  have wpc : (keyWritten s k).pc=4148 := by
    rw [keyWritten,written_pc,key_pc s e.pc];rfl
  rw [ready_run _ wpc]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro r
  cases r;simp [Execution.charge];omega

end TwoPermutationPrototype.Grouped
