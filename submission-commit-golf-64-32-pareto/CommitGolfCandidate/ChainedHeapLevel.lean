import CommitGolfCandidate.ChainedHeapAddress

/-! Initialize and execute a complete level from the concrete heap geometry. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

theorem level_header_register (s : MachineState) (h : Height) (reg : Reg)
    (kept : reg ∉ ([.x15,.x16,.x17] : List Reg)) :
    (parentLevelPrefix s h 5).getReg reg = s.getReg reg := by
  cases reg <;> first | exact (kept (by decide)).elim | rfl

theorem level_header_memory (s : MachineState) (h : Height) (query : Word) :
    (parentLevelPrefix s h 5).getMem query = s.getMem query := by rfl

structure HeapLevelReady (s : MachineState) (h : Height) (count : Nat) : Prop where
  args : LoopArgs s 256
  pc : s.pc = levelPC h
  source : s.getReg .x6 = heapAddress (4*count-2)
  target : s.getReg .x7 = heapAddress (2*count-1)
  base : s.getReg .x9 = BitVec.ofNat 64 heapBase
  stride : s.getReg .x4 = BitVec.ofNat 64 (32*count)
  positive : 0 < count
  small : count ≤ 2^23

theorem HeapLevelReady.header {s : MachineState} {h : Height} {count : Nat}
    (ready : HeapLevelReady s h count) : LevelReady (parentLevelPrefix s h 5) h count := by
  have args : LoopArgs (parentLevelPrefix s h 5) 256 :=
    ⟨ready.args.source,ready.args.target,ready.args.selector,ready.args.size,ready.args.kind,
      ready.args.aligned,ready.args.inputValid,ready.args.outputValid,ready.args.access⟩
  refine ⟨args,?_,ready.small,?_,?_,?_⟩
  · simpa only [ite_eq_right (by have := ready.positive; omega : count ≠ 0)] using
      level_header_pc s h ready.pc
  · rw [level_header_register s h .x7 (by decide),level_boundary,ready.target,ready.base,ready.stride]
    exact (heap_boundary_offset count ready.positive).symm
  · intro i inside k
    have lower : 2*i ≤ 4*count-2 := by have := ready.positive; omega
    rw [level_header_register s h .x6 (by decide),ready.source,heap_cursor64 _ _ lower]
    exact heap_word_valid _ k.val (by have := ready.small; omega) k.isLt
  · intro i inside k
    have lower : i ≤ 2*count-1 := by have := ready.positive; omega
    rw [level_header_register s h .x7 (by decide),ready.target,heap_cursor32 _ _ lower]
    exact heap_word_valid _ k.val (by have := ready.small; omega) (by have := k.isLt; omega)

def heapLevelTrace (h : Height) (count : Nat) (s : MachineState) : OracleComp World MachineState :=
  levelTrace h count (parentLevelPrefix s h 5)

theorem heap_level_execution (s : MachineState) (h : Height) (count : Nat)
    (ready : HeapLevelReady s h count) (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (5+parentNodeSteps h*count+fuel) s coins =
      (do let out ← heapLevelTrace h count s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (5+parentNodeCycles h*count) (calls h*count)) := by
  rw [show 5+parentNodeSteps h*count+fuel = 5+(parentNodeSteps h*count+fuel) by omega,
    level_header_execution s h ready.pc,level_execution count _ h ready.header]
  simp [heapLevelTrace,Execution.charge,←Nat.add_assoc]

theorem heap_level_pc (s out : MachineState) (h : Height) (count : Nat)
    (ready : HeapLevelReady s h count) (reached : out ∈ support (heapLevelTrace h count s)) :
    out.pc = shiftPC h := by
  have finished := level_trace_ready count _ out h ready.header reached
  simpa only [ite_true] using finished.pc

end CommitGolfCandidate.Chained.Native
