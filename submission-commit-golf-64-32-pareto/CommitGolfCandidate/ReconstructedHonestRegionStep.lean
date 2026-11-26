import CommitGolfCandidate.ReconstructedHonestMemoryRanges
import CommitGolfCandidate.ReconstructedHonestAbstract

namespace CommitGolfCandidate.Reconstruction.HonestRegionStep
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRanges HonestMemoryRanges HonestAbstract

structure Abstract where
  regs : Registers
  ram : Heap

def Models (s : MachineState) (a : Abstract) := Meaning s a.regs ∧ HeapMeaning s a.ram

/-- The largest public answer is one 1,600-bit permutation. Only qwords
possibly touched by those 200 bytes lose their known ranges. -/
def afterQuery (a : Abstract) : Abstract := ⟨a.regs,fun q =>
  if away (wrap (a.regs .x12).lo ((a.regs .x12).hi+199)) q then a.ram q else any⟩

private theorem reply_model {bits : Nat} (s : MachineState) (a : Abstract) (meaning : Models s a)
    (answer : BitVec bits) (size : (bits+7)/8≤200) :
    Models (writeBits s (s.getReg .x12) answer) (afterQuery a) := by
  refine ⟨fun r => ?_,fun q => ?_⟩
  · rw [writeBits_register]; exact meaning.1 _
  · simp only [afterQuery]; split
    · rename_i ok
      rw [writeBits_memory_outside _ _ q answer (by
        intro i hi
        have reg := meaning.1 .x12
        have small : i<2^64 := by omega
        have contained : Contains (wrap (a.regs .x12).lo ((a.regs .x12).hi+199))
            (s.getReg .x12+BitVec.ofNat 64 i) := by
          apply wrap_ok _ _ ((s.getReg .x12).toNat+i) (by have := reg.1; omega) (by have := reg.2; omega)
          simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,limit]
        exact (away_ok _ _ _ contained ok).2)]
      exact meaning.2 _
    · exact arbitrary _

/-- After any supported public syscall, register ranges survive and every
disjoint heap word keeps its previous range. A syscall fault has no successor. -/
theorem query (im : Image) (s : MachineState) (coins : Bool) (a : Abstract)
    (meaning : Models s a) (read : fetch im s=some (.base .ECALL)) (pub : s.getReg .x5=0)
    (out : Execution) (run : out ∈ support (execute im 1 s coins)) (cont : out.exit=.unfinished) :
    out.state.pc=s.pc+4 ∧ Models out.state (afterQuery a) := by
  rw [execute,read] at run
  simp only [pub,ite_true] at run
  cases q : oracleInput s with
  | none =>
    simp only [q,support_pure,Set.mem_singleton_iff] at run
    subst out; cases cont
  | some q' =>
    simp only [q,mem_support_bind_iff] at run
    obtain ⟨answer,_,run⟩ := run
    simp only [execute,support_pure,Set.mem_singleton_iff] at run
    obtain ⟨_,rfl,rfl⟩ := run
    rcases q' with x|(y|z) <;> exact ⟨rfl,reply_model _ _ meaning _ (by decide)⟩

def isQuery : Instruction → Bool
  | .base .ECALL => true
  | _ => false

@[simp] theorem isQuery_iff (op : Instruction) : isQuery op=true ↔ op=.base .ECALL := by
  cases op with
  | base op => cases op <;> simp [isQuery]
  | word _ _ _ _ | sraiw _ _ _ => simp [isQuery]

def advance (a : Abstract) (op : Instruction) : Abstract :=
  if isQuery op then afterQuery a else ⟨registersAfter a.regs a.ram op,heapAfter a.regs a.ram op⟩

/-- Concrete positive steps of the pinned interpreter are overapproximated by
their decoded interval and RAM actions, including the public permutation call. -/
theorem one (im : Image) (s : MachineState) (coins : Bool) (a : Abstract) (op : Instruction)
    (meaning : Models s a) (read : fetch im s=some op) (plain : HonestFlow.direct op=true)
    (pub : op=.base .ECALL → s.getReg .x5=0)
    (out : Execution) (run : out ∈ support (execute im 1 s coins)) (cont : out.exit=.unfinished) :
    out.state.pc ∈ destinations s.pc (exactFile a.regs) op ∧ Models out.state (advance a op) := by
  by_cases sys : op=.base .ECALL
  · subst op
    obtain ⟨pc,after⟩ := query _ _ _ _ meaning read (pub rfl) out run cont
    refine ⟨?_,after⟩
    rw [pc]; exact List.mem_cons_self
  · have step := continued_step im s op coins read sys out run cont
    have cfg := ((HonestAbstract.one im s op _ coins read sys plain (exactFile_ok meaning.1) out run).2 cont).1
    refine ⟨cfg,?_⟩
    have noQuery : ¬isQuery op = true := fun yes => sys ((isQuery_iff _).mp yes)
    unfold advance
    rw [ite_eq_right noQuery]
    exact ⟨registersAfter_ok _ _ _ meaning.1 meaning.2 step,heapAfter_ok _ _ _ meaning.1 meaning.2 step⟩

end CommitGolfCandidate.Reconstruction.HonestRegionStep
