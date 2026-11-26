import CommitGolfCandidate.ChainedCommitContent

/-! Native parent-phase frames above the complete heap, including nonce storage. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open TwoPermutationPrototype TwoPermutationPrototype.Sampling
attribute [local irreducible] checkEvaluation parentLevels readBuffer

theorem stage_memory_above_heap (s out : MachineState) (h : Height)
    (ready : HeapLevelReady s h (heightCount h)) (reached : out ∈ support (stageTrace h s))
    (query : Word) (outside : OutsideScratch query) (above : heapBase+32*2^25 ≤ query.toNat) :
    out.getMem query = s.getMem query := by
  simp only [stageTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨body,last,rfl⟩ := reached
  rw [shift_memory]
  trans (parentLevelPrefix s h 5).getMem query
  · apply level_trace_memory _ _ body h ready.header.args last query outside
    intro i inside j
    rw [level_header_register s h .x7 (by decide),ready.target,heap_cursor32 _ _ (by have := ready.positive; omega)]
    intro equal
    have numeric := congrArg BitVec.toNat equal
    rw [heap_word_numeric _ j.val (by have := ready.small; omega) (by have := j.isLt; omega)] at numeric
    have short := j.isLt
    have countBound := ready.small
    have countPositive := ready.positive
    omega
  · exact level_header_memory s h query

theorem parent_levels_memory_above_heap (remaining : Nat) (small : remaining ≤ 24) (s out : MachineState)
    (ready : 0 < remaining → HeapLevelReady s (heightAt remaining) (heightCount (heightAt remaining)))
    (reached : out ∈ support (parentLevels remaining s))
    (query : Word) (outside : OutsideScratch query) (above : heapBase+32*2^25 ≤ query.toNat) :
    out.getMem query = s.getMem query := by
  induction remaining generalizing s with
  | zero =>
    simp only [parentLevels,support_pure,Set.mem_singleton_iff] at reached
    subst out
    rfl
  | succ remaining ih =>
    simp only [parentLevels,mem_support_bind_iff] at reached
    obtain ⟨middle,first,last⟩ := reached
    have entry := ready (by omega)
    have next : 0 < remaining → HeapLevelReady middle (heightAt remaining) (heightCount (heightAt remaining)) :=
      fun positive => stage_next remaining positive (by omega) s middle entry first
    exact (ih (by omega) middle next last).trans (stage_memory_above_heap s middle _ entry first query outside above)

theorem root_memory_above_heap (s : MachineState) (output : s.getReg .x8 = 4294971392)
    (query : Word) (above : heapBase+32*2^25 ≤ query.toNat) :
    (chainedRootPrefix s 10).getMem query = s.getMem query := by
  rw [root_tail_memory]
  apply root_memory_outside s query _ 4 (by decide)
  intro j same
  have numeric := congrArg BitVec.toNat same
  rw [output] at numeric
  change query.toNat = (BitVec.ofNat 64 4294971392+BitVec.ofNat 64 (8*j.val)).toNat at numeric
  have short := j.isLt
  rw [←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4294971392+8*j.val < 2^64 by omega)] at numeric
  unfold heapBase at above
  omega

theorem complete_parent_memory_above_heap (oracle : Oracle) (s : MachineState)
    (pc : s.pc = 186848) (entry : FastEntry s)
    (output : s.getReg .x8 = 4294971392) (query : Word) (outside : OutsideScratch query)
    (above : heapBase+32*2^25 ≤ query.toNat) :
    (checkEvaluation oracle (completeParentTrace s)).1.getMem query = s.getMem query := by
  rw [show completeParentTrace s = Fast.fastParentTrace s from rfl,Fast.fast_parent_eval]
  have ready := Fast.fast_part_ready oracle s pc entry output
  let b := Fast.ctl (checkEvaluation oracle (Fast.fast 8 (Fast.ctl s Fast.setup))).1 Fast.handoff
  let c := (checkEvaluation oracle (parentLevels 16 b)).1
  have reached := check_evaluation_support oracle (parentLevels 16 b)
  have frame := parent_levels_memory_above_heap 16 (by decide) b c (fun _ => ready.1) reached query outside above
  have target : c.getReg .x8 = 4294971392 :=
    (parent_levels_register 16 _ c reached .x8 (by simp [ParentSaved])).trans ready.2
  have fast := Fast.fast_part_memory oracle s query.toNat ⟨above,outside.aligned,outside.room⟩
  have e : Fast.W query.toNat = query := by simp [Fast.W]
  rw [e] at fast
  exact (root_memory_above_heap c target query above).trans (frame.trans fast)

theorem complete_parent_nonce (oracle : Oracle) (s : MachineState)
    (pc : s.pc = 186848) (ready : FastEntry s)
    (output : s.getReg .x8 = 4294971392) (i : Index) :
    readBuffer (checkEvaluation oracle (completeParentTrace s)).1 (8*leafSalt i.val) 16 =
      readBuffer s (8*leafSalt i.val) 16 := by
  apply aligned_buffer_eq _ _ _ (by decide)
  intro k bound
  have idx : i.val < 2^24 := i.isLt
  have room : 8*(leafSalt i.val+k) < 2^64 := by unfold leafSalt; omega
  have numeric : (wordAddress (leafSalt i.val+k)).toNat = 8*(leafSalt i.val+k) := by
    rw [wordAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt room]
  have outside : OutsideScratch (wordAddress (leafSalt i.val+k)) := by
    constructor <;> rw [numeric] <;> unfold leafSalt <;> omega
  have above : heapBase+32*2^25 ≤ (wordAddress (leafSalt i.val+k)).toNat := by
    rw [numeric]; unfold heapBase leafSalt; omega
  have frame := complete_parent_memory_above_heap oracle s pc ready output _ outside above
  change memoryView (checkEvaluation oracle (completeParentTrace s)).1 (leafSalt i.val+k) = _
  rw [show memoryView (checkEvaluation oracle (completeParentTrace s)).1 (leafSalt i.val+k) =
    (checkEvaluation oracle (completeParentTrace s)).1.getMem (wordAddress (leafSalt i.val+k)) from rfl,frame]
  have slice := read_buffer_slice s (8*leafSalt i.val) 16 (8*k) 8 (by omega)
  rw [show 8*leafSalt i.val+8*k = 8*(leafSalt i.val+k) by omega,read_word] at slice
  simpa only [←Nat.mul_assoc,Nat.reduceMul,memoryView] using slice.symm

theorem chained_commit_body_nonce (oracle : Oracle) (ready : MachineState) (regs : Chain.BodyRegs ready)
    (salts : Index → BitVec 128)
    (original : ∀ i : Index, (window (memoryView ready) (leafSalt i.val) : Words 2) = saltWords (salts i))
    (i : Index) : readBuffer (checkEvaluation oracle (chainedCommitBody ready)).1 (8*leafSalt i.val) 16 = salts i := by
  let middle := (checkEvaluation oracle (leafPrefixTrace ready)).1
  have reached := check_evaluation_support oracle (leafPrefixTrace ready)
  have content := (leaf_prefix_content oracle ready regs salts original).2 i
  have entry := leaf_prefix_heap_ready ready regs middle reached
  have output := leaf_prefix_output ready regs middle reached
  rw [chainedCommitBody,evaluation_read_bind]
  exact (complete_parent_nonce oracle middle (leaf_prefix_parent_pc ready regs middle reached) entry output i).trans content

end CommitGolfCandidate.Chained.Native
