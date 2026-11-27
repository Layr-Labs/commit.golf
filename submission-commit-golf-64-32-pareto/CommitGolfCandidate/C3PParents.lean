import CommitGolfCandidate.TwoPermutationHybridLower
import CommitGolfCandidate.TwoPermutationCounted

/-! # The paired commit's first parent level (loop 1) reads from the reply area

Leaf `i`'s 200-byte reply is at `R + 200 i` (`R = TD + 2^29 + 168`), so the two child digests of
parent `n = 2^23 + k` (the last 32 bytes of reply `2k`, the first 32 bytes of reply `2k+1`) are the 64
bytes at `R + 400 k + 168`, word `pairWord n`. Loop 1 is the leader's `ecall ; addi a0,a0,-64 ;
addi a2,a2,-32` with the source step `-400`. After its last step `a0` is the heap word of node
`2^24 - 2` (`pairWord hybridCut = treeWord (2 * hybridCut)`), where the leader's upper levels start. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option autoImplicit false
attribute [local irreducible] execute

/-- The word of parent `n`'s two child digests (`2^23 - 1 ≤ n < 2^24`). -/
def pairWord (n : Nat) : Nat := 516 + 32 * 2 ^ 24 + 2 ^ 26 - 8 + 50 * (n + 1 - 2 ^ 23)

theorem pair_word_cut : pairWord hybridCut = treeWord (2 * hybridCut) := by
  unfold pairWord treeWord hybridCut; norm_num

theorem pair_word_step (n : Nat) (h : 2 ^ 23 ≤ n + 1) : pairWord (n + 1) = pairWord n + 50 := by
  unfold pairWord; omega

theorem pair_word_bound (n : Nat) (h : n < 2 ^ 24) : pairWord n + 8 < 2 ^ 33 := by
  unfold pairWord; omega

structure ParentRegsP (s : MachineState) (n : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (pairWord n)
  target : s.getReg .x12 = wordAddress (treeWord n)
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0
  heap : s.getReg .x9 = wordAddress (treeWord 0)

theorem regs_of_cut (s : MachineState) (r : ParentRegsP s hybridCut) : ParentRegs s hybridCut :=
  ⟨by rw [r.source, pair_word_cut], r.target, r.selector, r.size, r.primitive, r.heap⟩

def parentInputP (s : MachineState) (n : Nat) := readBuffer s (8 * pairWord n) 64

def parentAfterP (s : MachineState) (n : Nat) (reply : BitVec 256) :=
  execInstrBr (execInstrBr (parentWritten s n reply) (.ADDI .x10 .x10 3696)) (.ADDI .x12 .x12 4064)

structure ParentWordsAtP (image : Image) (pc : Word) : Prop where
  call : ∀ s : MachineState, s.pc = pc → fetch image s = some (.base .ECALL)
  source : ∀ s : MachineState, s.pc = pc + 4 → fetch image s = some (.base (.ADDI .x10 .x10 3696))
  target : ∀ s : MachineState, s.pc = pc + 8 → fetch image s = some (.base (.ADDI .x12 .x12 4064))

theorem parent_call_atP (image : Image) (s : MachineState) (n fuel : Nat)
    (bound : n < 2 ^ 24) (regs : ParentRegsP s n)
    (fetched : fetch image s = some (.base .ECALL)) :
    execute image (fuel + 1) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInputP s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (parentWritten s n answer) true
          return result.charge 8 1) := by
  have pb := pair_word_bound n bound
  have source := word_address_value (word := pairWord n) (by omega)
  have target := word_address_value (word := treeWord n) (by unfold treeWord; omega)
  have inputRange : 8 * pairWord n + 64 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have outputRange : 8 * treeWord n + 32 ≤ MEMORY_BYTES := by unfold treeWord MEMORY_BYTES; omega
  have query : oracleInput s = some (.inl (parentInputP s n)) := by
    have kind : (s.getReg .x13).toNat = 0 := by rw [regs.primitive]; rfl
    unfold oracleInput
    dsimp only
    rw [kind]
    simp [regs.source, regs.target, regs.size, COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH,
      rangeValid, source, target, inputRange, outputRange, parentInputP]
  simp [execute, fetched, regs.selector, query, writeOracleAnswer, regs.target, parentWritten,
    oracleCycles, COMPRESSION_CYCLES]
  rfl

theorem parent_triple_atP (image : Image) (s : MachineState) (n fuel : Nat) (pc : Word)
    (here : s.pc = pc) (bound : n < 2 ^ 24) (regs : ParentRegsP s n)
    (fetched : ParentWordsAtP image pc) :
    execute image (3 + fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInputP s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (parentAfterP s n answer) true
          return result.charge 10 1) := by
  rw [show 3 + fuel = (fuel + 2) + 1 by omega, parent_call_atP image s n _ bound regs (fetched.call s here)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let first := parentWritten s n answer
  let second := execInstrBr first (.ADDI .x10 .x10 3696)
  have firstPC : first.pc = pc + 4 := by simp only [first, parentWritten, written_pc, here]
  have secondPC : second.pc = pc + 8 := by
    change first.pc + 4 = _
    rw [firstPC, BitVec.add_assoc]
    rfl
  have advance : ordinaryStep second (.base (.ADDI .x12 .x12 4064)) = some (parentAfterP s n answer) := by
    unfold parentAfterP
    rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.source first firstPC)
    (show ordinaryStep first _ = some second from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.target second secondPC) advance]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem parent_pcP (s : MachineState) (n : Nat) (reply : BitVec 256) :
    (parentAfterP s n reply).pc = s.pc + 12 := by
  change (parentWritten s n reply).pc + 4 + 4 = s.pc + 12
  rw [parentWritten, written_pc]
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem next_parent_regsP (s : MachineState) (n : Nat) (reply : BitVec 256) (cut : 2 ^ 23 ≤ n + 1)
    (r : ParentRegsP s (n + 1)) : ParentRegsP (parentAfterP s (n + 1) reply) n := by
  have holds (reg : Reg) : (parentWritten s (n + 1) reply).getReg reg = s.getReg reg :=
    CommitGolfCandidate.writeBits_register ..
  constructor
  · change (parentWritten s (n + 1) reply).getReg .x10 + signExtend12 3696 = _
    rw [holds, r.source, pair_word_step n cut]
    rw [show signExtend12 (3696 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 50) by decide,
      wordAddress, wordAddress, ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [show 8 * (pairWord n + 50) + (2 ^ 64 - 8 * 50) = 8 * pairWord n + 2 ^ 64 by omega, Nat.add_mod_right]
  · change (parentWritten s (n + 1) reply).getReg .x12 + signExtend12 4064 = _
    rw [holds, r.target]
    have advance : treeWord (n + 1) = treeWord n + 4 := by unfold treeWord; omega
    rw [advance, wordAddress_add, BitVec.add_assoc]; simp [wordAddress, signExtend12]
  · exact (holds .x5).trans r.selector
  · exact (holds .x11).trans r.size
  · exact (holds .x13).trans r.primitive
  · exact (holds .x9).trans r.heap

def parentsTraceP (remaining : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0, s => pure s
  | k + 1, s => do
    let answer ← (liftM (World.query (.inr (.inl (parentInputP s (remaining + (k + 1)))))) :
      OracleComp World (BitVec 256))
    parentsTraceP remaining k (parentAfterP s (remaining + (k + 1)) answer)

theorem wide_parent_pc_succP (base : Word) (slot : Nat) :
    wideParentPC base slot + 12 = wideParentPC base (slot + 1) := by
  change base + BitVec.ofNat 64 (12 * slot) + BitVec.ofNat 64 12 = base + BitVec.ofNat 64 (12 * (slot + 1))
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [show 12 * slot + 12 = 12 * (slot + 1) by omega]

theorem wide_parent_segmentP (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, ParentWordsAtP image (wideParentPC base i))
    (remaining count slot fuel : Nat) (s : MachineState)
    (bound : remaining + count < 2 ^ 24) (cut : hybridCut ≤ remaining) (inside : slot + count ≤ span)
    (regs : ParentRegsP s (remaining + count)) (pc : s.pc = wideParentPC base slot) :
    execute image (3 * count + fuel) s true =
      (do let mid ← parentsTraceP remaining count s
          let result ← execute image fuel mid true
          return result.charge (10 * count) count) := by
  induction count generalizing slot s with
  | zero => simp [parentsTraceP, Execution.charge]
  | succ count ih =>
    rw [show 3 * (count + 1) + fuel = 3 + (3 * count + fuel) by omega,
      parent_triple_atP image s _ _ _ pc bound regs (fetches slot (by omega))]
    simp only [parentsTraceP, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    have next := next_parent_regsP s (remaining + count) answer (by unfold hybridCut at cut; omega)
      (by simpa only [Nat.add_assoc] using regs)
    have atNext := (parent_pcP s (remaining + (count + 1)) answer).trans
      ((congrArg (· + 12) pc).trans (wide_parent_pc_succP base slot))
    rw [ih (slot + 1) _ (by omega) (by omega) (by simpa only [Nat.add_assoc] using next) atNext]
    simp [Execution.charge, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem wide_parent_segment_postP (base : Word) (remaining count slot : Nat) (cut : hybridCut ≤ remaining)
    (s : MachineState) (regs : ParentRegsP s (remaining + count)) (pc : s.pc = wideParentPC base slot)
    {out : MachineState} (reached : out ∈ support (parentsTraceP remaining count s)) :
    ParentRegsP out remaining ∧ out.pc = wideParentPC base (slot + count) := by
  induction count generalizing slot s with
  | zero =>
    simp only [parentsTraceP, support_pure, Set.mem_singleton_iff] at reached
    subst out
    exact ⟨regs, pc⟩
  | succ count ih =>
    simp only [parentsTraceP, mem_support_bind_iff] at reached
    obtain ⟨answer, _, tail⟩ := reached
    have next := next_parent_regsP s (remaining + count) answer (by unfold hybridCut at cut; omega)
      (by simpa only [Nat.add_assoc] using regs)
    have atNext := (parent_pcP s (remaining + (count + 1)) answer).trans
      ((congrArg (· + 12) pc).trans (wide_parent_pc_succP base slot))
    rw [show slot + (count + 1) = slot + 1 + count by omega]
    exact ih (slot + 1) _ (by simpa only [Nat.add_assoc] using next) atNext tail

theorem full_trace_frameP (remaining count : Nat) (s : MachineState) (reg : Reg)
    (src : Reg.x10 ≠ reg) (dst : Reg.x12 ≠ reg) {out : MachineState}
    (hit : out ∈ support (parentsTraceP remaining count s)) : out.getReg reg = s.getReg reg := by
  induction count generalizing s with
  | zero => simp only [parentsTraceP, support_pure, Set.mem_singleton_iff] at hit; rw [hit]
  | succ count ih =>
    simp only [parentsTraceP, mem_support_bind_iff] at hit
    obtain ⟨answer, _, tail⟩ := hit
    rw [ih _ tail]
    simp only [parentAfterP, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ src, MachineState.getReg_setReg_ne _ _ _ _ dst,
      parentWritten, CommitGolfCandidate.writeBits_register]

structure HybridLowerCodeP (image : Image) where
  words : ∀ i < fullSpan, ParentWordsAtP image (wideParentPC 217580 i)
  branch : ∀ s : MachineState, s.pc = 610796 → fetch image s = some (.base (.BEQ .x12 .x18 8))
  back : ∀ s : MachineState, s.pc = 610800 → fetch image s = some (.base (.JAL .x0 1703932))

theorem lower_latchP (image : Image) (code : HybridLowerCodeP image) (left fuel : Nat) (s : MachineState)
    (bound : hybridCut + left < 2 ^ 24) (regs : ParentRegsP s (hybridCut + left))
    (cut : s.getReg .x18 = wordAddress (treeWord hybridCut)) (pc : s.pc = 610796) :
    execute image (longParentLatchCost left + fuel) s true =
      (do let y ← execute image fuel (s.setPC (lowerNext left)) true
          return y.charge (longParentLatchCost left) 0) := by
  have equal : s.getReg .x12 = s.getReg .x18 ↔ left = 0 := by
    rw [regs.target, cut]
    constructor
    · intro same
      have index := wordAddress_injective_of_bound (by unfold treeWord; omega)
        (by decide : treeWord hybridCut < 2 ^ 61) same
      unfold treeWord at index
      omega
    · rintro rfl; rfl
  by_cases last : left = 0
  · have step : ordinaryStep s (.base (.BEQ .x12 .x18 8)) = some (s.setPC 610804) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, equal.mpr last, signExtend13]
    rw [longParentLatchCost, if_pos last, lowerNext, if_pos last, Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (code.branch s pc) step]
    rfl
  · let mid := s.setPC 610800
    have diff : s.getReg .x12 ≠ s.getReg .x18 := fun h => last (equal.mp h)
    have step : ordinaryStep s (.base (.BEQ .x12 .x18 8)) = some mid := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, diff, mid]
    have jump : ordinaryStep mid (.base (.JAL .x0 1703932)) = some (s.setPC 217580) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, mid, MachineState.setReg, MachineState.setPC]
      rfl
    rw [longParentLatchCost, if_neg last, lowerNext, if_neg last, show 2 + fuel = (fuel + 1) + 1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (code.branch s pc) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (code.back mid rfl) jump]
    simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

def hybridLowerForP (span : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0, s => pure s
  | n + 1, s => do
    let mid ← parentsTraceP (hybridCut + span * n) span s
    hybridLowerForP span n (mid.setPC (lowerNext (span * n)))

abbrev hybridLowerP := hybridLowerForP fullSpan

theorem lower_runP (image : Image) (code : HybridLowerCodeP image)
    (n fuel : Nat) (s : MachineState) (bound : hybridCut + fullSpan * n < 2 ^ 24)
    (regs : ParentRegsP s (hybridCut + fullSpan * n)) (pc : 0 < n → s.pc = 217580)
    (cut : s.getReg .x18 = wordAddress (treeWord hybridCut)) :
    execute image (lowerCost 3 n + fuel) s true =
      (do let out ← hybridLowerP n s
          let res ← execute image fuel out true
          return res.charge (lowerCost 10 n) (fullSpan * n)) := by
  induction n generalizing s with
  | zero => simp [hybridLowerP, hybridLowerForP, lowerCost, Execution.charge]
  | succ n ih =>
    have amount : hybridCut + fullSpan * (n + 1) = hybridCut + fullSpan * n + fullSpan := by
      rw [Nat.mul_succ, Nat.add_assoc]
    rw [amount] at regs bound
    have enter : s.pc = wideParentPC 217580 0 := pc (by omega)
    have stepCost : lowerCost 3 (n + 1) = 3 * fullSpan + longParentLatchCost (fullSpan * n) + lowerCost 3 n := by
      cases n with
      | zero => simp [lowerCost, longParentLatchCost]
      | succ n =>
        have nz : fullSpan * (n + 1) ≠ 0 := by unfold fullSpan; omega
        simp only [lowerCost, longParentLatchCost, nz, ite_false]
        rw [Nat.mul_succ (3 * fullSpan) (n + 1)]; omega
    rw [stepCost,
      show 3 * fullSpan + longParentLatchCost (fullSpan * n) + lowerCost 3 n + fuel =
        3 * fullSpan + (longParentLatchCost (fullSpan * n) + (lowerCost 3 n + fuel)) by omega,
      wide_parent_segmentP image 217580 fullSpan code.words (hybridCut + fullSpan * n) fullSpan 0 _ s bound
        (by omega) (by decide) regs enter]
    simp only [hybridLowerP, hybridLowerForP, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro mid hit
    have post := wide_parent_segment_postP 217580 (hybridCut + fullSpan * n) fullSpan 0 (by omega) s regs enter hit
    have saved := (full_trace_frameP _ _ s .x18 (by decide) (by decide) hit).trans cut
    rw [lower_latchP image code (fullSpan * n) _ mid (by omega) post.1 saved post.2]
    let next := mid.setPC (lowerNext (fullSpan * n))
    have nr : ParentRegsP next (hybridCut + fullSpan * n) :=
      ⟨post.1.source, post.1.target, post.1.selector, post.1.size, post.1.primitive, post.1.heap⟩
    have begin (h : 0 < n) : next.pc = 217580 := by
      change lowerNext (fullSpan * n) = _; rw [lowerNext, if_neg (by unfold fullSpan; omega)]
    have stepTen : lowerCost 10 (n + 1) = 10 * fullSpan + longParentLatchCost (fullSpan * n) + lowerCost 10 n := by
      cases n with
      | zero => simp [lowerCost, longParentLatchCost]
      | succ n =>
        have nz : fullSpan * (n + 1) ≠ 0 := by unfold fullSpan; omega
        simp only [lowerCost, longParentLatchCost, nz, ite_false]
        rw [Nat.mul_succ (10 * fullSpan) (n + 1)]; omega
    rw [ih next (by omega) nr begin saved, stepTen]
    rw [Nat.mul_succ fullSpan n]
    simp [next, Execution.charge, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem lower_postP (n : Nat) (s : MachineState) (entry : 0 < n → s.pc = 217580)
    (regs : ParentRegsP s (hybridCut + fullSpan * n)) {out : MachineState}
    (hit : out ∈ support (hybridLowerP n s)) :
    ParentRegsP out hybridCut ∧ (0 < n → out.pc = 610804) ∧ out.getReg .x8 = s.getReg .x8 := by
  induction n generalizing s with
  | zero =>
    simp only [hybridLowerP, hybridLowerForP, support_pure, Set.mem_singleton_iff] at hit; subst out; exact ⟨regs, by omega, rfl⟩
  | succ n ih =>
    simp only [hybridLowerP, hybridLowerForP, mem_support_bind_iff] at hit
    obtain ⟨mid, path, tail⟩ := hit
    have enter : s.pc = wideParentPC 217580 0 := entry (by omega)
    have r : ParentRegsP s (hybridCut + fullSpan * n + fullSpan) := by
      rw [show hybridCut + fullSpan * n + fullSpan = hybridCut + fullSpan * (n + 1) by rw [Nat.mul_succ, Nat.add_assoc]]
      exact regs
    have post := wide_parent_segment_postP 217580 (hybridCut + fullSpan * n) fullSpan 0 (by omega) s r enter path
    let next := mid.setPC (lowerNext (fullSpan * n))
    have nr : ParentRegsP next (hybridCut + fullSpan * n) :=
      ⟨post.1.source, post.1.target, post.1.selector, post.1.size, post.1.primitive, post.1.heap⟩
    have begin (h : 0 < n) : next.pc = 217580 := by
      change lowerNext (fullSpan * n) = _; rw [lowerNext, if_neg (by unfold fullSpan; omega)]
    have after := ih next begin nr tail
    refine ⟨after.1, ?_, after.2.2.trans (full_trace_frameP _ _ s .x8 (by decide) (by decide) (out := mid) path)⟩
    intro _
    cases n with
    | zero => simp only [hybridLowerP, hybridLowerForP, support_pure, Set.mem_singleton_iff] at tail; rw [tail]; rfl
    | succ n => exact after.2.1 (by omega)

theorem counted_parentsP (oracle : Oracle) (s : MachineState) (rem cnt : Nat) :
    RunPublic oracle (parentsTraceP rem cnt s) cnt := by
  induction cnt generalizing s with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [parentsTraceP]
    simpa only [Nat.add_comm 1 k] using
      (run_bind_public oracle (liftM (World.query (.inr (.inl (parentInputP s (rem + (k + 1)))))) :
        OracleComp World (BitVec 256))
        (fun answer => parentsTraceP rem k (parentAfterP s (rem + (k + 1)) answer)) 1 k (run_query_public ..)
        (fun _ => ih _))

theorem counted_lowerP (oracle : Oracle) (s : MachineState) (n : Nat) :
    RunPublic oracle (hybridLowerP n s) (fullSpan * n) := by
  induction n generalizing s with
  | zero => simpa only [hybridLowerP, hybridLowerForP, Nat.mul_zero] using run_pure_public oracle s
  | succ n ih =>
    rw [hybridLowerP, hybridLowerForP, show fullSpan * (n + 1) = fullSpan + fullSpan * n by rw [Nat.mul_succ, Nat.add_comm]]
    exact run_bind_public oracle _ _ fullSpan (fullSpan * n) (counted_parentsP ..) (fun out => ih _)

end TwoPermutationPrototype.RV64
