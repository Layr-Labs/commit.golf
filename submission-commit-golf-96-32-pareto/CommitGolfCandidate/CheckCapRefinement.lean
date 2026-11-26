import CommitGolfCandidate.CheckCap
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.BufferRefinement
import CommitGolfCandidate.CopyRefinement

/-! Functional refinement of the level-7 cap-table verification phase (`k = 128`).
Copies the 128 cap digests from `[proof + 71680, proof + 75776)` into flat heap slots
128..255 at `[4608, 8704)`, computes parents 127 down to 1 into `[544, 4608)`, and
compares slot 1 (`[544, 576)`) against `input.commitment`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The 128 level-7 cap digests read directly from the loaded proof buffer. -/
def capTableOf (initial : MachineState) (slot : Nat) : Digest :=
  readBuffer initial (submission.layout.proof + 71680 + 32 * slot) 32

set_option maxHeartbeats 2000000 in
private theorem cap_copy_digest_memory (state : MachineState)
    (disjoint : ∀ i j : Fin 4,
      state.getReg .x23 + BitVec.ofNat 64 (8 * i.val) ≠
        state.getReg .x12 + BitVec.ofNat 64 (8 * j.val))
    (word : Fin 4) :
    (checkCapCopyDigestState state).getMem (state.getReg .x12 + BitVec.ofNat 64 (8 * word.val)) =
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) := by
  have regMem (s : MachineState) (a v : Word) (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
    cases r <;> rfl
  have dstNe (i j : Fin 4) (h : i ≠ j) :
      state.getReg .x12 + BitVec.ofNat 64 (8 * i.val) ≠
        state.getReg .x12 + BitVec.ofNat 64 (8 * j.val) := by
    intro eq
    have c := congrArg (fun v : Word => v - state.getReg .x12) eq
    simp only [BitVec.add_comm (state.getReg .x12), BitVec.add_sub_cancel] at c
    have n := congrArg BitVec.toNat c
    have hi := i.isLt; have hj := j.isLt
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * i.val < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 8 * j.val < 2 ^ 64)] at n
    exact h (Fin.ext (by omega))
  have d01 : state.getReg .x12 ≠ state.getReg .x12 + 8#64 := by
    simpa using dstNe ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  have d02 : state.getReg .x12 ≠ state.getReg .x12 + 16#64 := by
    simpa using dstNe ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
  have d03 : state.getReg .x12 ≠ state.getReg .x12 + 24#64 := by
    simpa using dstNe ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide)
  have d12 : state.getReg .x12 + 8#64 ≠ state.getReg .x12 + 16#64 :=
    dstNe ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
  have d13 : state.getReg .x12 + 8#64 ≠ state.getReg .x12 + 24#64 :=
    dstNe ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide)
  have d23 : state.getReg .x12 + 16#64 ≠ state.getReg .x12 + 24#64 :=
    dstNe ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
  have s0 : signExtend12 0 = 0#64 := rfl
  have s8 : signExtend12 8 = 8#64 := rfl
  have s16 : signExtend12 16 = 16#64 := rfl
  have s24 : signExtend12 24 = 24#64 := rfl
  have x10 : state.getReg .x23 + 8#64 ≠ state.getReg .x12 := by
    simpa using disjoint ⟨1, by decide⟩ ⟨0, by decide⟩
  have x20 : state.getReg .x23 + 16#64 ≠ state.getReg .x12 := by
    simpa using disjoint ⟨2, by decide⟩ ⟨0, by decide⟩
  have x21 : state.getReg .x23 + 16#64 ≠ state.getReg .x12 + 8#64 :=
    disjoint ⟨2, by decide⟩ ⟨1, by decide⟩
  have x30 : state.getReg .x23 + 24#64 ≠ state.getReg .x12 := by
    simpa using disjoint ⟨3, by decide⟩ ⟨0, by decide⟩
  have x31 : state.getReg .x23 + 24#64 ≠ state.getReg .x12 + 8#64 :=
    disjoint ⟨3, by decide⟩ ⟨1, by decide⟩
  have x32 : state.getReg .x23 + 24#64 ≠ state.getReg .x12 + 16#64 :=
    disjoint ⟨3, by decide⟩ ⟨2, by decide⟩
  rcases word with ⟨w, hw⟩
  rw [cap_copy_digest_expansion]
  interval_cases w <;>
    simp only [Nat.reduceMul, List.foldl, execInstrBr,
      s0, s8, s16, s24, BitVec.add_zero, regMem,
      MachineState.getMem_setPC, MachineState.getMem_setReg, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x12),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x23),
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
      MachineState.getMem_setMem_eq,
      MachineState.getMem_setMem_ne d03, MachineState.getMem_setMem_ne d02,
      MachineState.getMem_setMem_ne d01, MachineState.getMem_setMem_ne d13,
      MachineState.getMem_setMem_ne d12, MachineState.getMem_setMem_ne d23,
      MachineState.getMem_setMem_ne x10, MachineState.getMem_setMem_ne x20,
      MachineState.getMem_setMem_ne x21, MachineState.getMem_setMem_ne x30,
      MachineState.getMem_setMem_ne x31, MachineState.getMem_setMem_ne x32]

private theorem cap_copy_digest_eq (state : MachineState) (src dst : Nat)
    (srcReg : state.getReg .x23 = BitVec.ofNat 64 src)
    (dstReg : state.getReg .x12 = BitVec.ofNat 64 dst)
    (srcAligned : src % 8 = 0) (dstAligned : dst % 8 = 0)
    (srcBound : src + 32 ≤ 2 ^ 64) (dstBound : dst + 32 ≤ 2 ^ 64)
    (separate : src + 32 ≤ dst ∨ dst + 32 ≤ src) :
    readBuffer (checkCapCopyDigestState state) dst 32 = readBuffer state src 32 := by
  apply (read_digest_eq_iff _ _ _ _ dstAligned srcAligned).mpr
  intro word hw
  have copied := cap_copy_digest_memory state (by
    intro i j
    rw [srcReg, dstReg, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact separate_digest_words src dst i.val j.val srcBound dstBound i.isLt j.isLt separate)
    ⟨word, hw⟩
  simpa only [srcReg, dstReg, ← BitVec.ofNat_add] using copied

/-- `cap-copy` copies `count` consecutive 32-byte digests from `src` to `dst`. -/
theorem cap_copy_loop_records (state : MachineState) (cap : Nat → Digest)
    (src dst count : Nat) (bounded : count ≤ 128)
    (srcReg : state.getReg .x23 = BitVec.ofNat 64 src)
    (dstReg : state.getReg .x12 = BitVec.ofNat 64 dst)
    (srcAligned : src % 8 = 0) (dstAligned : dst % 8 = 0)
    (srcBound : src + 32 * count ≤ MEMORY_BYTES)
    (dstBound : dst + 32 * count ≤ MEMORY_BYTES)
    (below : dst + 32 * count ≤ src)
    (data : ∀ slot < count, readBuffer state (src + 32 * slot) 32 = cap slot) :
    ∀ slot < count, readBuffer (checkCapCopyStepState^[count] state) (dst + 32 * slot) 32 = cap slot := by
  induction count generalizing state cap src dst with
  | zero => intro slot hs; omega
  | succ count ih =>
    have srcSmall : src + 32 * (count + 1) < 2 ^ 64 := by dsimp [MEMORY_BYTES] at srcBound; omega
    have dstSmall : dst + 32 * (count + 1) < 2 ^ 64 := by dsimp [MEMORY_BYTES] at dstBound; omega
    let next := checkCapCopyStepState state
    have nextSrc : next.getReg .x23 = BitVec.ofNat 64 (src + 32) := by
      rw [(cap_copy_step_registers state).1, srcReg]
      change BitVec.ofNat 64 src + BitVec.ofNat 64 32 = _
      rw [← BitVec.ofNat_add]
    have nextDst : next.getReg .x12 = BitVec.ofNat 64 (dst + 32) := by
      rw [(cap_copy_step_registers state).2.1, dstReg]
      change BitVec.ofNat 64 dst + BitVec.ofNat 64 32 = _
      rw [← BitVec.ofNat_add]
    have stepFirst : readBuffer next dst 32 = cap 0 := by
      have d := cap_copy_digest_eq state src dst srcReg dstReg srcAligned dstAligned
        (by omega) (by omega) (Or.inr (by omega))
      exact d.trans (by simpa only [Nat.mul_zero, Nat.add_zero] using data 0 (by omega))
    have nextData (slot : Nat) (hs : slot < count) :
        readBuffer next (src + 32 + 32 * slot) 32 = cap (slot + 1) := by
      have unchanged : readBuffer next (src + 32 + 32 * slot) 32 =
          readBuffer state (src + 32 + 32 * slot) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro w hw
        change (checkCapCopyDigestState state).getMem _ = _
        apply cap_copy_digest_outside
        intro j
        rw [dstReg, ← BitVec.ofNat_add]
        exact separate_digest_words (src + 32 + 32 * slot) dst w j.val (by omega) (by omega)
          hw j.isLt (Or.inr (by omega))
      rw [unchanged, show src + 32 + 32 * slot = src + 32 * (slot + 1) by omega]
      exact data (slot + 1) (by omega)
    have rest := ih next (fun s => cap (s + 1)) (src + 32) (dst + 32) (by omega)
      nextSrc nextDst (by omega) (by omega) (by omega) (by omega) (by omega) nextData
    intro slot hs
    rw [Function.iterate_succ_apply]
    cases slot with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      have kept : readBuffer (checkCapCopyStepState^[count] next) dst 32 = readBuffer next dst 32 := by
        apply read_digest_congr _ _ _ dstAligned
        intro w hw
        apply cap_copy_loop_outside count next _
        · rw [nextDst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        · rw [nextDst, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          exact Or.inl (by omega)
      exact kept.trans stepFirst
    | succ slot =>
      rw [show dst + 32 * (slot + 1) = dst + 32 + 32 * slot by omega]
      exact rest slot (by omega)

private theorem cap_parent_step_mem (state : MachineState) (answer : BitVec 256) :
    (checkCapParentStepState state answer).mem = (paddedCompressionState state answer).mem := rfl

private theorem check_cap_length_pc (state : MachineState) :
    (checkCapLengthState state).pc = if state.getReg .x17 = 75776 then 4468 else 4432 := rfl

private theorem check_cap_root_setup_mem (state : MachineState) :
    (checkCapRootSetupState state).mem = state.mem := rfl

attribute [local irreducible] checkCapParentLoop checkCapParentStepState checkCapHash checkEvaluation

/-- The 127-step bottom-up parent loop computes `referenceHeap oracle.compression 128 cap`
at every internal and leaf slot `1..255` in `[544, 8704)`. -/
theorem cap_parent_loop_heap (oracle : Oracle) (state : MachineState)
    (cap : Nat → Digest) (count : Nat) (bounded : count ≤ 127)
    (r10 : state.getReg .x10 = BitVec.ofNat 64 (512 + 64 * count))
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (above : ∀ slot, count < slot → slot < 256 →
      readBuffer state (512 + 32 * slot) 32 = referenceHeap oracle.compression 128 cap slot) :
    ∀ slot, 0 < slot → slot < 256 →
      readBuffer (checkEvaluation oracle (checkCapParentLoop state count)).1 (512 + 32 * slot) 32 =
        referenceHeap oracle.compression 128 cap slot := by
  induction count generalizing state with
  | zero =>
    intro slot pos hi
    rw [checkCapParentLoop, check_evaluation_pure]
    exact above slot pos hi
  | succ count ih =>
    have r10Nat : (state.getReg .x10).toNat = 512 + 64 * (count + 1) := by
      rw [r10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h64 : readBuffer state (state.getReg .x10).toNat 64 =
        referenceHeap oracle.compression 128 cap (2 * (count + 1) + 1) ++
          referenceHeap oracle.compression 128 cap (2 * (count + 1)) := by
      rw [r10Nat, read_compression_halves state _ (by omega)]
      have leftAddr : 512 + 64 * (count + 1) = 512 + 32 * (2 * (count + 1)) := by omega
      have rightAddr : 512 + 64 * (count + 1) + 32 = 512 + 32 * (2 * (count + 1) + 1) := by omega
      rw [rightAddr, leftAddr,
        above (2 * (count + 1) + 1) (by omega) (by omega),
        above (2 * (count + 1)) (by omega) (by omega)]
    let answer : BitVec 256 := oracle.compression (padInput (readBuffer state (state.getReg .x10).toNat 64))
    have answerEq : answer = referenceHeap oracle.compression 128 cap (count + 1) := by
      dsimp only [answer]
      rw [h64]
      exact (reference_heap_parent oracle.compression 128 cap (count + 1) (by omega) (by omega)).symm
    let next := checkCapParentStepState state answer
    have next10 : next.getReg .x10 = BitVec.ofNat 64 (512 + 64 * count) := by
      rw [(cap_parent_step_registers state answer).1, r10]
      change BitVec.ofNat 64 (512 + 64 * (count + 1)) - BitVec.ofNat 64 64 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have next12 : next.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have nextMem : next.mem = (writeBits state (BitVec.ofNat 64 (512 + 32 * (count + 1))) answer).mem := by
      dsimp only [next]
      rw [cap_parent_step_mem, padded_compression_memory state answer, r12]
    have nextAbove (slot : Nat) (lo : count < slot) (hi : slot < 256) :
        readBuffer next (512 + 32 * slot) 32 = referenceHeap oracle.compression 128 cap slot := by
      rw [read_buffer_memory_congr _ _ nextMem]
      by_cases eq : slot = count + 1
      · subst slot
        have w := write_bits_digest (bits := 256) state (512 + 32 * (count + 1)) 0 answer (by decide) (by decide)
        rw [← answerEq]
        exact w.trans (by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          rw [BitVec.getLsbD_extractLsb']
          simp [hi])
      · have preserved := write_bits_read_outside (bits := 256) state answer (512 + 32 * (count + 1))
          (512 + 32 * slot) 32 (by omega) (by omega) (Or.inr (by omega))
        exact preserved.trans (above slot (by omega) hi)
    intro slot pos hi
    rw [checkCapParentLoop, check_evaluation_public_bind]
    exact ih next (by omega) next10 next12 nextAbove slot pos hi

attribute [local irreducible] checkCapCopyStepState checkCapCopySetupState checkCapLengthState
  checkCapParentSetupState checkCapRootSetupState Nat.iterate

/-- `checkCapHash` computes the exact root of the 128-leaf cap table at scratch `[544, 576)`. -/
theorem check_cap_hash_root (oracle : Oracle) (input : CheckInput)
    (lenOk : input.proof.length = 75776) :
    let initial := submission.initialState .check input
    readBuffer (checkEvaluation oracle (checkCapHash initial)).1 544 32 =
      referenceHeap oracle.compression 128 (capTableOf initial) 1 := by
  dsimp only
  let initial := submission.initialState .check input
  let lenState := checkCapLengthState initial
  have isLen : initial.getReg .x17 = 75776 := by
    change BitVec.ofNat 64 input.proof.length = 75776; rw [lenOk]; rfl
  have lenPC : lenState.pc = 4468 := by rw [check_cap_length_pc, if_pos isLen]
  let copySetup := checkCapCopySetupState lenState
  have csRegs := check_cap_copy_setup_registers lenState lenPC
  have csSrc : copySetup.getReg .x23 = BitVec.ofNat 64 (submission.layout.proof + 71680) := by
    rw [csRegs.2.2.1, (check_cap_length_registers initial).2.2.2.1]; rfl
  have csMem : copySetup.mem = initial.mem :=
    csRegs.2.2.2.2.2.2.trans (check_cap_length_registers initial).2.2.2.2.2
  let afterCopy := checkCapCopyStepState^[128] copySetup
  have copyData : ∀ slot < 128, readBuffer afterCopy (4608 + 32 * slot) 32 = capTableOf initial slot := by
    apply cap_copy_loop_records copySetup (capTableOf initial)
      (submission.layout.proof + 71680) 4608 128 (by decide) csSrc csRegs.2.2.2.2.1
      (by decide) (by decide) (by decide) (by decide) (by decide)
    intro slot hs
    rw [read_buffer_memory_congr _ _ csMem]
    rfl
  have copyEndPC : afterCopy.pc = 4572 :=
    cap_copy_loop_finished 128 (by decide) (by decide) copySetup csRegs.2.2.2.2.2.1
  let parSetup := checkCapParentSetupState afterCopy
  have psRegs := check_cap_parent_setup_registers afterCopy copyEndPC
  have parAbove (slot : Nat) (lo : 127 < slot) (hi : slot < 256) :
      readBuffer parSetup (512 + 32 * slot) 32 =
        referenceHeap oracle.compression 128 (capTableOf initial) slot := by
    rw [read_buffer_memory_congr _ _ psRegs.2.2.2.2.2.2]
    have addrEq : 512 + 32 * slot = 4608 + 32 * (slot - 128) := by omega
    rw [addrEq, copyData (slot - 128) (by omega)]
    have leafEq := reference_heap_leaf oracle.compression 128 (capTableOf initial) (slot - 128) (by omega)
    rw [show 128 + (slot - 128) = slot by omega] at leafEq
    exact leafEq.symm
  have heapEq := cap_parent_loop_heap oracle parSetup (capTableOf initial) 127 (by decide)
    (by rw [psRegs.2.2.2.2.1]; rfl) (by rw [psRegs.2.2.2.2.2.1]; rfl) parAbove 1 (by decide) (by decide)
  rw [checkCapHash, check_evaluation_bind]
  rcases hPar : checkEvaluation oracle (checkCapParentLoop parSetup 127) with ⟨parOut, cPar⟩
  simp only [check_evaluation_pure]
  rw [read_buffer_memory_congr _ _ (check_cap_root_setup_mem parOut)]
  simpa [hPar] using heapEq

/-- The cap-root four-word comparison passes iff the 128 cap digests hash to `input.commitment`. -/
theorem check_cap_comparison (oracle : Oracle) (input : CheckInput)
    (batch : input.positions.card = BATCH) (lenOk : input.proof.length = 75776) :
    let initial := submission.initialState .check input
    let hashed := (checkEvaluation oracle (checkCapHash initial)).1
    (∀ word < 4, hashed.getMem (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
      hashed.getMem (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word))) ↔
    referenceHeap oracle.compression 128 (capTableOf initial) 1 = input.commitment := by
  dsimp only
  let initial := submission.initialState .check input
  let hashed := (checkEvaluation oracle (checkCapHash initial)).1
  have is128 : initial.getReg .x16 = 128 := by
    change BitVec.ofNat 64 input.positions.card = 128; rw [batch]; rfl
  have isLen : initial.getReg .x17 = 75776 := by
    change BitVec.ofNat 64 input.proof.length = 75776; rw [lenOk]; rfl
  have hRegs := check_cap_hash_registers initial hashed is128 isLen (check_evaluation_support oracle _)
  have commEq : readBuffer hashed submission.layout.commitment 32 = input.commitment := by
    have same : readBuffer hashed submission.layout.commitment 32 =
        readBuffer initial submission.layout.commitment 32 := by
      apply read_digest_congr _ _ _ (by decide)
      intro w hw
      apply check_cap_hash_support_outside initial hashed isLen (check_evaluation_support oracle _)
      exact Or.inr (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by change 4294971392 + 8 * w < 2 ^ 64; omega)]
        change 8704 ≤ 4294971392 + 8 * w; omega)
    exact same.trans (check_input_commitment input)
  have rootEq := check_cap_hash_root oracle input lenOk
  rw [← rootEq, ← commEq, read_digest_eq_iff _ _ _ _ (by decide) (by decide)]
  constructor <;> intro words word hw
  · have agree := words word hw
    rw [hRegs.2.1, hRegs.2.2.1] at agree
    change hashed.getMem (BitVec.ofNat 64 544 + BitVec.ofNat 64 (8 * word)) =
      hashed.getMem (BitVec.ofNat 64 submission.layout.commitment + BitVec.ofNat 64 (8 * word)) at agree
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add] at agree
    exact agree
  · have agree := words word hw
    rw [hRegs.2.1, hRegs.2.2.1]
    change hashed.getMem (BitVec.ofNat 64 544 + BitVec.ofNat 64 (8 * word)) =
      hashed.getMem (BitVec.ofNat 64 submission.layout.commitment + BitVec.ofNat 64 (8 * word))
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact agree

end CommitGolfCandidate
