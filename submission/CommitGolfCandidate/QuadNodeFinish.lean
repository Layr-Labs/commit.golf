import CommitGolfCandidate.QuadCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationCheckerReplay

/-! The actual quad permutation call and its five-instruction return to the
fourteen-level binary path. Input bytes are the actual 200-byte scratch window. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute
attribute [local simp] Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem finish_zero (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem finish_pc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl

def quadCallPrepared (s : MachineState) : MachineState := execInstrBr s (.ADDI .x12 .x23 0)

def quadReturnCode : List Instr :=
  [.SRLI .x6 .x6 2,.ADDI .x11 .x0 64,.JAL .x0 2095672,
   .ADDI .x13 .x0 0,.ADDI .x29 .x0 14]

def quadReturn (s : MachineState) (n : Nat) : MachineState :=
  (quadReturnCode.take n).foldl execInstrBr s

private def returnWord (i : Nat) : Nat := if i<3 then 429+i else 58+i

theorem quad_call_prepare_hop (s : MachineState) (pc : s.pc=5804) :
    GroupHop s (quadCallPrepared s) 1 := by
  intro fuel
  have fetched := fetch_at s 427 (.ADDI .x12 .x23 0) (by decide) pc rfl
  have step : ordinaryStep s (.base (.ADDI .x12 .x23 0))=some (quadCallPrepared s) := rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched step]
  rfl

theorem quad_return_hop (s : MachineState) (pc : s.pc=5812) : GroupHop s (quadReturn s 5) 5 := by
  intro fuel
  apply execute_unit_steps (states := quadReturn s)
  intro i bound
  refine ⟨.base (quadReturnCode[i]?.getD .EBREAK),?_,?_,?_⟩
  · apply fetch_at _ (returnWord i) _ (by unfold returnWord; split <;> omega)
    · interval_cases i <;> simp [quadReturn,quadReturnCode,returnWord,execInstrBr,signExtend21,pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem quad_return_post (s : MachineState) (pc : s.pc=5812) :
    let t := quadReturn s 5
    t.pc=4348 ∧ t.getReg .x6=s.getReg .x6 >>> 2 ∧ t.getReg .x11=64 ∧
      t.getReg .x13=0 ∧ t.getReg .x29=14 ∧ t.mem=s.mem := by
  simp [quadReturn,quadReturnCode,execInstrBr,signExtend12,signExtend21,pc] <;> rfl

theorem quad_return_register (s : MachineState) (reg : Reg)
    (a : reg≠.x6) (b : reg≠.x11) (c : reg≠.x13) (d : reg≠.x29) :
    (quadReturn s 5).getReg reg=s.getReg reg := by
  simp [quadReturn,quadReturnCode,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d]

/-- One actual permutation query, returning to the unchanged binary dispatcher. -/
def quadFinish (s : MachineState) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) 1600)))))
  return quadReturn (writeBits (quadCallPrepared s) (wordAddress 1536) answer) 5

attribute [local irreducible] writeBits readBuffer

theorem execute_quad_finish (s : MachineState) (pc : s.pc=5804)
    (input : s.getReg .x10=12800) (dest : s.getReg .x23=12288)
    (selector : s.getReg .x5=0) (size : s.getReg .x11=200) (primitive : s.getReg .x13=1)
    (fuel : Nat) :
    execute packedImage (7+fuel) s false = do
      let finished ← quadFinish s
      let result ← execute packedImage fuel finished false
      return result.charge 14 1 := by
  let p := quadCallPrepared s
  have pcP : p.pc=5808 := by simp [p,quadCallPrepared,execInstrBr,pc]
  have keep (reg : Reg) (kept : reg≠.x12) : p.getReg reg=s.getReg reg := by
    simp [p,quadCallPrepared,execInstrBr,Ne.symm kept]
  have output : p.getReg .x12=wordAddress 1536 := by
    simp [p,quadCallPrepared,execInstrBr,signExtend12,dest,wordAddress]
  have fetched := fetch_at p 428 .ECALL (by decide) pcP rfl
  have call := execute_permutation_call packedImage (5+fuel) p false 1600 1536 (by decide) (by decide)
    ((keep .x10 (by decide)).trans input) output ((keep .x5 (by decide)).trans selector)
    ((keep .x11 (by decide)).trans size) ((keep .x13 (by decide)).trans primitive) fetched
  have mem : p.mem=s.mem := rfl
  have windowSame : window (count := 25) (memoryView p) 1600=window (memoryView s) 1600 := by
    rfl
  rw [windowSame] at call
  rw [show 7+fuel=1+(5+fuel+1) by omega,quad_call_prepare_hop s pc,call]
  simp only [quadFinish,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  have returnedPC : (writeBits p (wordAddress 1536) answer).pc=5812 := by
    unfold writeBits
    change p.pc+4=_
    rw [pcP]
    rfl
  rw [quad_return_hop _ returnedPC]
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc]
  rfl

theorem quad_return_memory (s : MachineState) : (quadReturn s 5).mem=s.mem := rfl

theorem quad_finish_rows (oracle : Oracle) (s : MachineState) :
    let input := packBuffer (window (memoryView s) 1600)
    let answer := oracle.permutation input
    checkEvaluation oracle (recordRows (quadFinish s)) =
      ((quadReturn (writeBits (quadCallPrepared s) (wordAddress 1536) answer) 5,
        [.permutation input answer]),1) := by
  simp only [quadFinish,record_rows_query,check_evaluation_public_bind,check_evaluation_map,
    record_rows_pure,check_evaluation_pure]
  rfl

theorem quad_finish_digest (s : MachineState) (reply : Block) :
    readBuffer (quadReturn (writeBits (quadCallPrepared s) (wordAddress 1536) reply) 5) 12288 32 =
      outputDigest reply := by
  rw [read_buffer_memory_congr _ _ (quad_return_memory _) _ _]
  simpa only [wordAddress,Nat.add_zero,Nat.mul_zero,outputDigest] using
    write_bits_digest (quadCallPrepared s) 12288 0 reply (by decide) (by decide)

end TwoPermutationPrototype.Quad.Checker
