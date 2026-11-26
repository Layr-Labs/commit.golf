import CommitGolfCandidate.S5Code
import CommitGolfCandidate.Counting

namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev AtWord := Site .commit

def prepareCall (s : MachineState) (src dst : Reg) (fromOff toOff : BitVec 12) :=
  let t := execInstrBr s (.ADDI .x10 src fromOff)
  execInstrBr t (.ADDI .x12 dst toOff)

def callState (s : MachineState) (src dst : Reg) (fromOff toOff : BitVec 12) (w : Digest) :=
  let ready := prepareCall s src dst fromOff toOff
  writeBits ready (ready.getReg .x12) w



/-- Common three-instruction address setup and compression used by the leaf and parent loops. -/
theorem execute_compression (s : MachineState) (n fuel : Nat) (src dst : Reg)
    (fromOff toOff : BitVec 12)
    (op₁ : AtWord n (.ADDI .x10 src fromOff))
    (op₂ : AtWord (n+1) (.ADDI .x12 dst toOff))
    (op₃ : AtWord (n+2) .ECALL) (pc : s.pc = pcAt n)
    (selector : s.getReg .x5 = 0) (len : s.getReg .x11 = 96) (kind : s.getReg .x13 = 0)
    (valid : let r := prepareCall s src dst fromOff toOff
             rangeValid (r.getReg .x10) 96 = true ∧ (r.getReg .x10).toNat%8 = 0 ∧
             rangeValid (r.getReg .x12) 32 = true ∧ (r.getReg .x12).toNat%8 = 0) :
    let ready := prepareCall s src dst fromOff toOff
    execute commitImage (fuel+3) s true =
      (do let w ← hash (readBuffer s (ready.getReg .x10).toNat 96)
          let r ← execute commitImage fuel (callState s src dst fromOff toOff w) true
          return r.charge 10 1) := by
  let t := execInstrBr s (.ADDI .x10 src fromOff)
  let r := prepareCall s src dst fromOff toOff
  have pc₁ : t.pc = pcAt (n+1) := by change s.pc+4 = _; rw [pc,←pc_succ]
  have pc₂ : r.pc = pcAt (n+2) := by change t.pc+4 = _; rw [pc₁, ←pc_succ (n+1)]
  have r5 : r.getReg .x5 = 0 := selector
  have r11 : r.getReg .x11 = 96 := len
  have r13 : r.getReg .x13 = 0 := kind
  have mem : r.mem = s.mem := rfl
  obtain ⟨sv, sa, dv, da⟩ := valid
  have query : oracleInput r = some (.inl (readBuffer s (r.getReg .x10).toNat 96)) := by
    change rangeValid (r.getReg .x10) 96 = true at sv
    change rangeValid (r.getReg .x12) 32 = true at dv
    change (r.getReg .x10).toNat%8 = 0 at sa
    change (r.getReg .x12).toNat%8 = 0 at da
    simp [oracleInput, r11, r13, COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, sv, dv,
      sa, da]
    try rw [r13]
    try simp
    rfl
  dsimp only
  rw [execute_ordinary_step _ _ _ t _ _ (op₁ _ pc) rfl,
    execute_ordinary_step _ _ _ r _ _ (op₂ _ pc₁) rfl]
  rw [execute, op₃ _ pc₂, if_pos r5, query]
  simp only [Late.hash, writeOracleAnswer, bind_assoc, pure_bind]
  apply bind_congr
  intro w
  simp [callState, r, oracleCycles, COMPRESSION_CYCLES, instructionCycles, Execution.charge,
    ← Nat.add_assoc]
  rfl

end CommitGolfCandidate.S5Machine
