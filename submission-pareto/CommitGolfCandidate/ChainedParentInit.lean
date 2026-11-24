import CommitGolfCandidate.ChainedCommitPrefix
import CommitGolfCandidate.ChainedHeapTransition

/-! Initialize the delivered heap levels from the unchanged leaf/masking prefix. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
attribute [local irreducible] execute

def parentInitPrefix (s : MachineState) (count : Nat) : MachineState :=
  (parentInitOps.take count).foldl execInstrBr s

theorem parent_init_prefix_pc (s : MachineState) (count : Nat) (small : count ≤ 5) :
    (parentInitPrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp [parentInitPrefix,parentInitOps,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem parent_init_execution (s : MachineState) (pc : s.pc = 184628) (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (5+fuel) s coins =
      (do let result ← execute chainedCommitImage fuel (parentInitPrefix s 5) coins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := parentInitPrefix s)
  intro i inside
  refine ⟨.base ((parentInitOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have opEq : chainedParentOp i = (parentInitOps[i]?).getD .EBREAK := by
      interval_cases i <;> rfl
    have here : (parentInitPrefix s i).pc = (184628 : Word)+BitVec.ofNat 64 (4*i) := by
      rw [parent_init_prefix_pc s i (by omega),pc]
    simpa only [opEq] using chained_parent_at ⟨i,by omega⟩ (parentInitPrefix s i) here
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem parent_init_register (s : MachineState) (reg : Reg)
    (kept : reg ∉ ([.x4,.x6,.x7,.x10,.x12] : List Reg)) :
    (parentInitPrefix s 5).getReg reg = s.getReg reg := by
  cases reg <;> first | exact (kept (by decide)).elim | rfl

theorem parent_init_memory (s : MachineState) (query : Word) :
    (parentInitPrefix s 5).getMem query = s.getMem query := by rfl

theorem initial_heap_ready (s : MachineState) (regs : ParentRegs s (2^24-1))
    (pc : s.pc = 184628) (stride : s.getReg .x19 = 536870912) :
    HeapLevelReady (parentInitPrefix s 5) (0 : Height) (heightCount 0) := by
  have args : LoopArgs (parentInitPrefix s 5) 256 :=
    ⟨rfl,rfl,regs.selector,regs.size,regs.primitive,by decide,by decide,by decide,by decide⟩
  refine ⟨args,?_,?_,?_,?_,?_,by decide,by decide⟩
  · rw [parent_init_prefix_pc s 5 (by decide),pc]
    rfl
  · change s.getReg .x10+signExtend12 0 = _
    exact (BitVec.add_zero _).trans regs.source
  · change s.getReg .x12+signExtend12 0 = _
    exact (BitVec.add_zero _).trans regs.target
  · exact regs.heap
  · change s.getReg .x19 >>> 1 = _
    rw [stride]
    rfl

/-- The specialized initializer needs the parent's two cursors and the unshifted stride. -/
structure FastEntry (s : MachineState) : Prop where
  regs : ParentRegs s (2^24-1)
  stride : s.getReg .x19=536870912

theorem leaf_prefix_heap_ready (ready : MachineState) (regs : Chain.BodyRegs ready) (out : MachineState)
    (reached : out ∈ support (leafPrefixTrace ready)) : FastEntry out := by
  simp only [leafPrefixTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨leaves,last,rfl⟩ := reached
  have fin := PackedLeaves.executableLeaves.finished ready regs leaves last
  have setup := skip_entry_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop
  exact ⟨setup.1,setup.2.2.2.1.trans fin.stride⟩

end CommitGolfCandidate.Chained.Native
