import CommitGolfCandidate.QuadCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationCheckerReplay

/-! The actual quad permutation call, its three-instruction loop test, and the
four-instruction exit to the twelve-level binary path. Input bytes are the
actual 200-byte scratch window. -/
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
  [.SRLI .x6 .x6 2,.SRLI .x29 .x6 21,.BNE .x29 .x0 7936]

def quadReturn (s : MachineState) (n : Nat) : MachineState :=
  (quadReturnCode.take n).foldl execInstrBr s

theorem quad_call_prepare_hop (s : MachineState) (pc : s.pc=5804) :
    GroupHop s (quadCallPrepared s) 1 := by
  intro fuel
  have fetched := fetch_at s 427 (.ADDI .x12 .x23 0) (by decide) pc rfl
  have step : ordinaryStep s (.base (.ADDI .x12 .x23 0))=some (quadCallPrepared s) := rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched step]
  rfl

theorem quad_return_hop (s : MachineState) (pc : s.pc=5812) : GroupHop s (quadReturn s 3) 3 := by
  intro fuel
  apply execute_unit_steps (states := quadReturn s)
  intro i bound
  refine ⟨.base (quadReturnCode[i]?.getD .EBREAK),?_,?_,?_⟩
  · apply fetch_at _ (429+i) _ (by omega)
    · interval_cases i <;> simp [quadReturn,quadReturnCode,execInstrBr,pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem shift_nat (n k : Nat) (bound : n<2^64) :
    BitVec.ofNat 64 n >>> k=BitVec.ofNat 64 (n/2^k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound,Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) bound),Nat.shiftRight_eq_div_pow]

theorem quad_return_memory (s : MachineState) : (quadReturn s 3).mem=s.mem := by
  change (execInstrBr (quadReturn s 2) (.BNE .x29 .x0 7936)).mem=s.mem
  simp only [execInstrBr]
  split <;> rfl

theorem quad_return_register (s : MachineState) (reg : Reg)
    (a : reg≠.x6) (d : reg≠.x29) :
    (quadReturn s 3).getReg reg=s.getReg reg := by
  change (execInstrBr (quadReturn s 2) (.BNE .x29 .x0 7936)).getReg reg=s.getReg reg
  have two : (quadReturn s 2).getReg reg=s.getReg reg := by
    simp [quadReturn,quadReturnCode,execInstrBr,Ne.symm a,Ne.symm d]
  simp only [execInstrBr]
  split <;> simpa only [MachineState.getReg_setPC] using two

/-- Both shifts of the node index, then the loop test: the block repeats while
the shifted index is at least 2^21 and otherwise continues at word 432. -/
theorem quad_return_post (s : MachineState) (pc : s.pc=5812) (n : Nat)
    (node : s.getReg .x6=BitVec.ofNat 64 n) (bound : n<2^64) :
    let t := quadReturn s 3
    t.pc=(if n/4/2^21=0 then 5824 else 5564) ∧ t.getReg .x6=BitVec.ofNat 64 (n/4) ∧
      t.getReg .x29=BitVec.ofNat 64 (n/4/2^21) ∧ t.mem=s.mem := by
  have quarter : s.getReg .x6 >>> 2=BitVec.ofNat 64 (n/4) := by
    rw [node]; exact shift_nat n 2 bound
  have small : n/4<2^64 := lt_of_le_of_lt (Nat.div_le_self _ _) bound
  have high : BitVec.ofNat 64 (n/4) >>> 21=BitVec.ofNat 64 (n/4/2^21) := shift_nat _ 21 small
  have tiny : n/4/2^21<2^64 := lt_of_le_of_lt (Nat.div_le_self _ _) small
  let u := quadReturn s 2
  have uPc : u.pc=5820 := by simp [u,quadReturn,quadReturnCode,execInstrBr,pc]
  have u6 : u.getReg .x6=BitVec.ofNat 64 (n/4) := by simp [u,quadReturn,quadReturnCode,execInstrBr,quarter]
  have u29 : u.getReg .x29=BitVec.ofNat 64 (n/4/2^21) := by
    simp [u,quadReturn,quadReturnCode,execInstrBr,quarter,high]
  have u0 : u.getReg .x0=0#64 := rfl
  have unfolded : quadReturn s 3=execInstrBr u (.BNE .x29 .x0 7936) := rfl
  rw [unfolded]
  refine ⟨?_,?_,?_,quad_return_memory s⟩
  · simp only [execInstrBr,u29,u0]
    by_cases zero : n/4/2^21=0
    · rw [if_pos zero,zero]
      simp only [show (BitVec.ofNat 64 0 != 0#64)=false by decide,Bool.false_eq_true,ite_false,
        MachineState.getReg_setPC,uPc]
      rfl
    · have ne : BitVec.ofNat 64 (n/4/2^21)≠0#64 := by
        intro eq
        have := congrArg BitVec.toNat eq
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt tiny] at this
        exact zero this
      rw [if_neg zero]
      simp only [bne_iff_ne,ne_eq,ne,not_false_eq_true,ite_true,uPc]
      rfl
  · simp only [execInstrBr]
    split <;> simpa only [MachineState.getReg_setPC] using u6
  · simp only [execInstrBr]
    split <;> simpa only [MachineState.getReg_setPC] using u29

/-- Exit to the binary path after the second pass: syscall width, primitive and
level counter for the twelve projected steps. -/
def quadExitCode : List Instr :=
  [.ADDI .x11 .x0 64,.JAL .x0 2095664,.ADDI .x13 .x0 0,.ADDI .x29 .x0 12]

def quadExit (s : MachineState) (n : Nat) : MachineState :=
  (quadExitCode.take n).foldl execInstrBr s

private def exitWord (i : Nat) : Nat := if i<2 then 432+i else 59+i

theorem quad_exit_hop (s : MachineState) (pc : s.pc=5824) : GroupHop s (quadExit s 4) 4 := by
  intro fuel
  apply execute_unit_steps (states := quadExit s)
  intro i bound
  refine ⟨.base (quadExitCode[i]?.getD .EBREAK),?_,?_,?_⟩
  · apply fetch_at _ (exitWord i) _ (by unfold exitWord; split <;> omega)
    · interval_cases i <;> simp [quadExit,quadExitCode,exitWord,execInstrBr,signExtend21,pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem quad_exit_post (s : MachineState) (pc : s.pc=5824) :
    let t := quadExit s 4
    t.pc=4348 ∧ t.getReg .x11=64 ∧ t.getReg .x13=0 ∧ t.getReg .x29=12 ∧ t.mem=s.mem := by
  simp [quadExit,quadExitCode,execInstrBr,signExtend12,signExtend21,pc] <;> rfl

theorem quad_exit_register (s : MachineState) (reg : Reg)
    (b : reg≠.x11) (c : reg≠.x13) (d : reg≠.x29) :
    (quadExit s 4).getReg reg=s.getReg reg := by
  simp [quadExit,quadExitCode,execInstrBr,Ne.symm b,Ne.symm c,Ne.symm d]

theorem quad_exit_memory (s : MachineState) : (quadExit s 4).mem=s.mem := rfl

/-- One actual permutation query, returning to the unchanged binary dispatcher. -/
def quadFinish (s : MachineState) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) 1600)))))
  return quadReturn (writeBits (quadCallPrepared s) (wordAddress 1536) answer) 3

attribute [local irreducible] writeBits readBuffer

theorem execute_quad_finish (s : MachineState) (pc : s.pc=5804)
    (input : s.getReg .x10=12800) (dest : s.getReg .x23=12288)
    (selector : s.getReg .x5=0) (size : s.getReg .x11=200) (primitive : s.getReg .x13=1)
    (fuel : Nat) :
    execute packedImage (5+fuel) s false = do
      let finished ← quadFinish s
      let result ← execute packedImage fuel finished false
      return result.charge 34 1 := by
  let p := quadCallPrepared s
  have pcP : p.pc=5808 := by simp [p,quadCallPrepared,execInstrBr,pc]
  have keep (reg : Reg) (kept : reg≠.x12) : p.getReg reg=s.getReg reg := by
    simp [p,quadCallPrepared,execInstrBr,Ne.symm kept]
  have output : p.getReg .x12=wordAddress 1536 := by
    simp [p,quadCallPrepared,execInstrBr,signExtend12,dest,wordAddress]
  have fetched := fetch_at p 428 .ECALL (by decide) pcP rfl
  have call := execute_permutation_call packedImage (3+fuel) p false 1600 1536 (by decide) (by decide)
    ((keep .x10 (by decide)).trans input) output ((keep .x5 (by decide)).trans selector)
    ((keep .x11 (by decide)).trans size) ((keep .x13 (by decide)).trans primitive) fetched
  have mem : p.mem=s.mem := rfl
  have windowSame : window (count := 25) (memoryView p) 1600=window (memoryView s) 1600 := by
    rfl
  rw [windowSame] at call
  rw [show 5+fuel=1+(3+fuel+1) by omega,quad_call_prepare_hop s pc,call]
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

theorem quad_finish_rows (oracle : Oracle) (s : MachineState) :
    let input := packBuffer (window (memoryView s) 1600)
    let answer := oracle.permutation input
    checkEvaluation oracle (recordRows (quadFinish s)) =
      ((quadReturn (writeBits (quadCallPrepared s) (wordAddress 1536) answer) 3,
        [.permutation input answer]),1) := by
  simp only [quadFinish,record_rows_query,check_evaluation_public_bind,check_evaluation_map,
    record_rows_pure,check_evaluation_pure]
  rfl

theorem quad_finish_digest (s : MachineState) (reply : Block) :
    readBuffer (quadReturn (writeBits (quadCallPrepared s) (wordAddress 1536) reply) 3) 12288 32 =
      outputDigest reply := by
  rw [read_buffer_memory_congr _ _ (quad_return_memory _) _ _]
  simpa only [wordAddress,Nat.add_zero,Nat.mul_zero,outputDigest] using
    write_bits_digest (quadCallPrepared s) 12288 0 reply (by decide) (by decide)

end TwoPermutationPrototype.Quad.Checker
