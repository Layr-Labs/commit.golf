import CommitGolfCandidate.ChainedLevelShift

/-! Consecutive-height geometry across all 24 delivered parent levels. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def heightCount (h : Height) : Nat := 2^(23-h.val)
def lowerHeight (i : Fin 23) : Height := ⟨i.val,by have := i.isLt; omega⟩
def nextHeight (i : Fin 23) : Height := ⟨i.val+1,by have := i.isLt; omega⟩

theorem height_count_bounds (h : Height) : 0 < heightCount h ∧ heightCount h ≤ 2^23 := by
  fin_cases h <;> decide

theorem height_count_next (i : Fin 23) : heightCount (lowerHeight i) = 2*heightCount (nextHeight i) := by
  fin_cases i <;> rfl

theorem height_stride_next (i : Fin 23) :
    BitVec.ofNat 64 (32*heightCount (lowerHeight i)) >>> 1 =
      BitVec.ofNat 64 (32*heightCount (nextHeight i)) := by
  fin_cases i <;> rfl

theorem height_pc_next (i : Fin 23) : shiftPC (lowerHeight i)+4 = levelPC (nextHeight i) := by
  fin_cases i <;> rfl

theorem heap_level_next (i : Fin 23) (s out : MachineState)
    (ready : HeapLevelReady s (lowerHeight i) (heightCount (lowerHeight i)))
    (reached : out ∈ support (heapLevelTrace (lowerHeight i) (heightCount (lowerHeight i)) s)) :
    HeapLevelReady (shiftState out) (nextHeight i) (heightCount (nextHeight i)) := by
  have finished := level_trace_ready _ _ out _ ready.header reached
  have args : LoopArgs (shiftState out) 256 :=
    ⟨finished.args.source,finished.args.target,finished.args.selector,finished.args.size,finished.args.kind,
      finished.args.aligned,finished.args.inputValid,finished.args.outputValid,finished.args.access⟩
  refine ⟨args,?_,?_,?_,?_,?_,(height_count_bounds _).1,(height_count_bounds _).2⟩
  · rw [shift_pc,heap_level_pc s out _ _ ready reached,height_pc_next]
  · rw [shift_register out .x6 (by decide),heap_level_source s out _ _ ready reached,height_count_next]
    congr 1
    omega
  · rw [shift_register out .x7 (by decide),heap_level_target s out _ _ ready reached,height_count_next]
  · rw [shift_register out .x9 (by decide),heap_level_register s out _ _ reached .x9 (by decide)]
    exact ready.base
  · rw [shift_stride,heap_level_register s out _ _ reached .x4 (by decide),ready.stride,height_stride_next]

end CommitGolfCandidate.Chained.Native
