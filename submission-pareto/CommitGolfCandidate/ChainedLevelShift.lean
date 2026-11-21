import CommitGolfCandidate.ChainedHeapLevel

/-! The delivered level-ending shift and exact whole-level cursor positions. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
attribute [local irreducible] execute

def shiftState (s : MachineState) : MachineState := execInstrBr s (.SRLI .x4 .x4 1)

theorem shift_execution (s : MachineState) (h : Height) (pc : s.pc = shiftPC h)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (fuel+1) s coins =
      (do let result ← execute chainedCommitImage fuel (shiftState s) coins
          return result.charge 1 0) := by
  refine execute_ordinary_step chainedCommitImage (.base (.SRLI .x4 .x4 1)) s (shiftState s) fuel coins ?_ rfl
  · have opEq : chainedParentOp (24+20*h.val) = .SRLI .x4 .x4 1 := by fin_cases h <;> rfl
    simpa only [opEq] using chained_parent_at ⟨24+20*h.val,by have := h.isLt; omega⟩ s pc

theorem shift_pc (s : MachineState) : (shiftState s).pc = s.pc+4 := by rfl

theorem shift_stride (s : MachineState) : (shiftState s).getReg .x4 = s.getReg .x4 >>> 1 := by rfl

theorem shift_register (s : MachineState) (reg : Reg) (kept : reg ≠ .x4) :
    (shiftState s).getReg reg = s.getReg reg := by
  cases reg <;> first | exact (kept rfl).elim | rfl

theorem shift_memory (s : MachineState) (query : Word) : (shiftState s).getMem query = s.getMem query := by rfl

theorem heap_level_source (s out : MachineState) (h : Height) (count : Nat)
    (ready : HeapLevelReady s h count) (reached : out ∈ support (heapLevelTrace h count s)) :
    out.getReg .x6 = heapAddress (2*count-2) := by
  rw [level_trace_source count _ out h reached,level_header_register s h .x6 (by decide),ready.source,
    heap_cursor64 _ _ (by have := ready.positive; omega)]
  congr 1
  have := ready.positive
  omega

theorem heap_level_target (s out : MachineState) (h : Height) (count : Nat)
    (ready : HeapLevelReady s h count) (reached : out ∈ support (heapLevelTrace h count s)) :
    out.getReg .x7 = heapAddress (count-1) := by
  rw [level_trace_target count _ out h reached,level_header_register s h .x7 (by decide),ready.target,
    heap_cursor32 _ _ (by have := ready.positive; omega)]
  congr 1
  have := ready.positive
  omega

theorem heap_level_register (s out : MachineState) (h : Height) (count : Nat)
    (reached : out ∈ support (heapLevelTrace h count s)) (reg : Reg)
    (kept : reg ∉ ([.x1,.x6,.x7,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30] : List Reg)) :
    out.getReg reg = s.getReg reg :=
  (level_trace_register count _ out h reached reg (by simp_all)).trans
    (level_header_register s h reg (by simp_all))

end CommitGolfCandidate.Chained.Native
