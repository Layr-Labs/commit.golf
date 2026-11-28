import CommitGolfCandidate.PentaGroupedInvariant
import CommitGolfCandidate.TwoPermutationCommitSetup

/-! Penta counter-mode commit prologue (words 0 .. 16): registers, 24-byte key drawn by RANDOM
into `keyWord + 1..3`, centered 45-leaf destination pointer `x20`, sentinel `x28`, and permutation
constants. Ends in `Live (keyReady s k) 0` at word 17 in 17 steps and 20 cycles. -/
namespace TwoPermutationPrototype.PentaGrouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Quad.Commit
set_option maxRecDepth 60000
set_option maxHeartbeats 1000000

abbrev Key := BitVec 192

def keyOps : List Instr :=
  [.ADDI .x8 .x11 0, .ADDI .x9 .x12 0, .ADDI .x18 .x10 0,
   .LUI .x20 1, .ADDI .x20 .x20 1536, .ADD .x20 .x9 .x20,
   .LUI .x24 442369, .ADD .x24 .x9 .x24, .ADDI .x28 .x8 (-256),
   .ADDI .x5 .x0 2, .ADDI .x10 .x24 8, .ADDI .x11 .x0 24]

def readyOps : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x11 .x0 200, .ADDI .x13 .x0 1, .ADDI .x10 .x18 0]

def keySetup (s : MachineState) := keyOps.foldl execInstrBr s
def keyWritten (s : MachineState) (k : BitVec 192) := writeBits (keySetup s) (wordAddress (keyWord + 1)) k
def keyReady (s : MachineState) (k : BitVec 192) := readyOps.foldl execInstrBr (keyWritten s k)

theorem key_run (s : MachineState) (pc : s.pc = 4096) (fuel : Nat) :
    execute image (12 + fuel) s true =
      (do let result ← execute image fuel (keySetup s) true
          return result.charge 12 0) := by
  unfold keySetup
  apply execute_unit_steps (states := fun i => (keyOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((keyOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_decoded _ i (by omega)
    · interval_cases i <;>
        simp only [keyOps, List.take, List.foldl, execInstrBr, MachineState.setPC, pc] <;> rfl
    · interval_cases i <;> decide +kernel
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem ready_run (s : MachineState) (pc : s.pc = 4148) (fuel : Nat) :
    execute image (4 + fuel) s true =
      (do let result ← execute image fuel (readyOps.foldl execInstrBr s) true
          return result.charge 4 0) := by
  apply execute_unit_steps (states := fun i => (readyOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((readyOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_decoded _ (13 + i) (by omega)
    · interval_cases i <;>
        simp only [readyOps, List.take, List.foldl, execInstrBr, MachineState.setPC, pc] <;> rfl
    · interval_cases i <;> decide +kernel
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

structure KeyRegisters (s : MachineState) : Prop where
  out : s.getReg .x8 = 4294971392
  heap : s.getReg .x9 = 4294971424
  source : s.getReg .x18 = 4096
  leaves : s.getReg .x20 = wordAddress (cursor 0)
  key : s.getReg .x24 = wordAddress keyWord
  stop : s.getReg .x28 = wordAddress (msgWord N_loop)
  target : s.getReg .x10 = wordAddress (keyWord + 1)
  size : s.getReg .x11 = 24
  selector : s.getReg .x5 = 2

theorem key_registers (s : MachineState) (entry : CommitEntry s) : KeyRegisters (keySetup s) := by
  constructor <;>
    dsimp [keySetup, keyOps, execInstrBr, MachineState.setPC, MachineState.setReg, MachineState.getReg]
  all_goals try simp only [show s.regs .x10 = 4096 from entry.message,
    show s.regs .x11 = 4294971392 from entry.commitment, show s.regs .x12 = 4294971424 from entry.heap]
  all_goals rfl

theorem key_pc (s : MachineState) (pc : s.pc = 4096) : (keySetup s).pc = 4144 := by
  change s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = _
  rw [pc]; rfl

theorem key_draw (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (1 + fuel) (keySetup s) true =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let result ← execute image fuel (keyWritten s k) true
          return result.charge 4 0) := by
  have r := key_registers s e
  have pc' : (keySetup s).pc = BitVec.ofNat 64 (4096 + 4 * 12) := key_pc s e.pc
  have fetched := fetch_decoded (keySetup s) 12 (by decide) pc' .ECALL (by decide +kernel)
  have valid : randomArgumentsValid (keySetup s) = true := by
    rw [randomArgumentsValid, r.target, r.size]; decide
  have raw :
      execute image (1 + fuel) (keySetup s) true =
        (do let k ← liftM ($ᵗ BitVec (8 * ((keySetup s).getReg .x11).toNat) :
              ProbComp (BitVec (8 * ((keySetup s).getReg .x11).toNat)))
            let result ← execute image fuel
              (writeBits (keySetup s) ((keySetup s).getReg .x10) k) true
            return result.charge (1 + (((keySetup s).getReg .x11).toNat + 7) / 8) 0) := by
    rw [Nat.add_comm 1 fuel, execute, fetched]
    simp only [r.selector, valid]
    rfl
  rw [r.size, r.target] at raw
  exact raw

theorem prologue_run (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (17 + fuel) s true =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let result ← execute image fuel (keyReady s k) true
          return result.charge 20 0) := by
  rw [show 17 + fuel = 12 + (1 + (4 + fuel)) by omega, key_run s e.pc, key_draw s e]
  simp only [bind_assoc]
  apply bind_congr; intro k
  have wpc : (keyWritten s k).pc = 4148 := by
    rw [keyWritten, written_pc, key_pc s e.pc]; rfl
  rw [ready_run _ wpc]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro r
  cases r; simp [Execution.charge]; omega

private theorem ready_reg (t : MachineState) :
    (readyOps.foldl execInstrBr t).getReg .x10 = t.getReg .x18 ∧
    (readyOps.foldl execInstrBr t).getReg .x5 = 0 ∧
    (readyOps.foldl execInstrBr t).getReg .x11 = 200 ∧
    (readyOps.foldl execInstrBr t).getReg .x13 = 1 ∧
    (readyOps.foldl execInstrBr t).pc = t.pc + 16 ∧
    ∀ reg ∈ [Reg.x8, .x9, .x20, .x24, .x28], (readyOps.foldl execInstrBr t).getReg reg = t.getReg reg := by
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_⟩
  · change t.getReg .x18 + 0 = _; simp
  · change t.pc + 4 + 4 + 4 + 4 = _; bv_omega
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem ready_live (s : MachineState) (e : CommitEntry s) (k : BitVec 192) : Live (keyReady s k) 0 := by
  have r := key_registers s e
  have w (reg : Reg) : (keyWritten s k).getReg reg = (keySetup s).getReg reg := writeBits_register ..
  have wpc : (keyWritten s k).pc = 4148 := by rw [keyWritten, written_pc, key_pc s e.pc]; rfl
  obtain ⟨x10, x5, x11, x13, pc, keep⟩ := ready_reg (keyWritten s k)
  change (readyOps.foldl execInstrBr (keyWritten s k)).getReg _ = _ at x10
  refine ⟨⟨?_, ?_, ?_, x5, x11, x13⟩, ?_, ?_, ?_, ?_⟩
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl, x10, w, r.source]; rfl
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl, keep .x20 (by simp), w, r.leaves]
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl, keep .x24 (by simp), w, r.key]
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl, pc, wpc]; rfl
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl, keep .x28 (by simp), w, r.stop]
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl, keep .x8 (by simp), w, r.out]
  · rw [show keyReady s k = readyOps.foldl execInstrBr (keyWritten s k) from rfl, keep .x9 (by simp), w, r.heap]

end TwoPermutationPrototype.PentaGrouped
