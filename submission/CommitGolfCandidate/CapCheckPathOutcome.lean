import CommitGolfCandidate.CapCheckPathLoop
import CommitGolfCandidate.CapMemoryFrame

/-! Universal query and supported register outcomes for the lower path.
These bounds cover every reply continuation; natural node progress is
derived only from a nonwrapping initial node representation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_path_loop_query_bound (state : MachineState) (count : Nat) :
    IsTotalQueryBound (capCheckPathLoop state count) count := by
  induction count generalizing state with
  | zero => trivial
  | succ count ih =>
    unfold capCheckPathLoop capCheckScratchQuery
    erw [isTotalQueryBound_query_bind_iff]
    exact ⟨by omega, fun answer => by simpa using ih (capCheckPathBlockState state answer)⟩

theorem cap_check_path_loop_register_frame (state : MachineState) (count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (capCheckPathLoop state count))
    (reg : Reg) (outside : reg ∉ [.x6,.x7,.x5,.x10,.x11,.x12,.x13,.x25,.x20,.x29]) :
    finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [capCheckPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    rfl
  | succ count ih =>
    simp only [capCheckPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, tail⟩ := reachable
    exact (ih _ tail).trans (cap_check_path_block_register state answer reg outside)

theorem cap_check_path_loop_cursor (state : MachineState) (count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (capCheckPathLoop state count)) :
    finished.getReg .x25 = state.getReg .x25 + BitVec.ofNat 64 (32*count) := by
  induction count generalizing state with
  | zero =>
    simp only [capCheckPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [capCheckPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, tail⟩ := reachable
    rw [ih _ tail, (cap_check_path_block_projection state answer).1,
      show 32*(count+1)=32+32*count by omega, BitVec.ofNat_add, BitVec.add_assoc]
    rfl

theorem cap_check_path_loop_node (state : MachineState) (count node : Nat)
    (small : node < 2^64) (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (finished : MachineState) (reachable : finished ∈ support (capCheckPathLoop state count)) :
    finished.getReg .x20 = BitVec.ofNat 64 (node/2^count) := by
  induction count generalizing state node with
  | zero =>
    simp only [capCheckPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simpa using index
  | succ count ih =>
    simp only [capCheckPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, tail⟩ := reachable
    have nextIndex := cap_check_path_block_node state answer node small index
    have result := ih _ (node/2) (by omega) nextIndex tail
    simpa only [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm] using result

theorem cap_check_path_loop_finished (state : MachineState) (count : Nat)
    (bounded : count ≤ 17) (counter : state.getReg .x29 = BitVec.ofNat 64 count)
    (finished : MachineState) (reachable : finished ∈ support (capCheckPathLoop state count)) :
    finished.getReg .x29 = 0 ∧ (0 < count → finished.pc = 4420) := by
  induction count generalizing state with
  | zero =>
    simp only [capCheckPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨counter, by omega⟩
  | succ count ih =>
    simp only [capCheckPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, tail⟩ := reachable
    have nextCounter : (capCheckPathBlockState state answer).getReg .x29 =
        BitVec.ofNat 64 count := by
      simpa only [Nat.add_sub_cancel] using
        cap_check_path_block_counter state answer (count+1) (by omega) counter
    have result := ih _ (by omega) nextCounter tail
    refine ⟨result.1, ?_⟩
    intro _
    by_cases empty : count = 0
    · subst count
      simp only [capCheckPathLoop, support_pure, Set.mem_singleton_iff] at tail
      subst finished
      rw [cap_check_path_block_exit state answer 1 (by decide) (by decide) counter]
      rfl
    · exact result.2 (by omega)

end CommitGolfCandidate
