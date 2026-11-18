import CommitGolfCandidate.GroupOpenCapMoves
import CommitGolfCandidate.GroupOpenWideCopy
import CommitGolfCandidate.TwoPermutationPackedOpeningBytes
import CommitGolfCandidate.GroupOpenCopyKernel
import CommitGolfCandidate.TwoPermutationPackedMemory
import RiscvZkvm.Rv64.Logic.ByteOps

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.QuartetCopy
open Packed (forward_disjoint_memory)
open PackedOpening (ByteCopy)

/-- The halfword kernel of a site. A wide site (`CopySite.wide`) runs through its stub instead, so its kernel
is empty. -/
def fieldCode (site : CopySite) : CopyCode where
  image := openingImage
  start := site.start
  count := if site.wide then 0 else site.halfwords
  source := site.source
  dest := .x21
  destOffset := site.destOffset
  sourceTemp := by cases site <;> simp [CopySite.source]
  destTemp := by decide
  offsetBound := by
    cases site <;> simp [CopySite.halfwords, CopySite.destOffset, CopySite.wide] <;> (try split) <;> omega
  load := fun offset inside state pc => by
    have plain : site.wide = false := by cases h : site.wide <;> simp_all
    have small : offset < site.halfwords := by simp only [plain, Bool.false_eq_true, ite_false] at inside; exact inside
    exact fetch_copy_load site ⟨offset, small⟩ state (Or.inl plain) pc
  store := fun offset inside state pc => by
    have plain : site.wide = false := by cases h : site.wide <;> simp_all
    have small : offset < site.halfwords := by simp only [plain, Bool.false_eq_true, ite_false] at inside; exact inside
    exact fetch_copy_store site ⟨offset, small⟩ state (Or.inl plain) pc

/-- A site's copy: the halfword kernel, or for a wide site its stub path. -/
def copyState (site : CopySite) (state : MachineState) : MachineState :=
  if site.wide then wideState site state else copyField (fieldCode site) state

/-- Cycles of a site's copy into `target`. -/
def copyCost (site : CopySite) (target : Nat) : Nat :=
  if site.wide then wideCost target else 2*site.halfwords

theorem wide_halfwords (site : CopySite) (wide : site.wide = true) : site.halfwords = 16 := by
  cases site <;> simp_all [CopySite.wide, CopySite.halfwords]

theorem plain_count (site : CopySite) (plain : site.wide = false) : (fieldCode site).count = site.halfwords := by
  simp [fieldCode, plain]

structure FieldInputs (site : CopySite) (state : MachineState) (source target : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*site.start)
  sourceReg : state.getReg site.source = BitVec.ofNat 64 source
  targetReg : state.getReg .x21 + BitVec.ofNat 64 site.destOffset = BitVec.ofNat 64 target
  disjoint : source+2*site.halfwords ≤ target
  targetFit : target+2*site.halfwords ≤ MEMORY_BYTES
  sourceEven : source % 2 = 0
  targetEven : target % 2 = 0
  sourceWide : site.wide = true → source % 8 = 0

private theorem FieldInputs.ready {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) (plain : site.wide = false) :
    CopyReady (fieldCode site) state source target 0 := by
  have cnt := plain_count site plain
  refine ⟨?_, input.sourceReg, ?_, ?_, ?_, input.sourceEven, input.targetEven⟩
  · simpa [fieldCode] using input.pc
  · simpa [fieldCode] using input.targetReg
  · rw [cnt]; exact input.disjoint.trans (Nat.le_trans (Nat.le_add_right _ _) input.targetFit)
  · rw [cnt]; exact input.targetFit

theorem FieldInputs.wide {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) (wide : site.wide = true) :
    WideInputs site state source target := by
  have h := wide_halfwords site wide
  exact ⟨wide, input.pc, input.sourceReg, input.targetReg, input.sourceWide wide, input.targetEven,
    by have := input.disjoint; omega, by have := input.targetFit; omega⟩

theorem FieldInputs.run {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) :
    RunsOpeningBlock state (copyState site state) (copyCost site target) := by
  cases w : site.wide
  · have run : RunsOpeningBlock state (copyField (fieldCode site) state) (2*(fieldCode site).count) :=
      copy_field_execute (fieldCode site) state source target (input.ready w)
    rw [plain_count site w] at run
    simp only [copyState, copyCost, w, Bool.false_eq_true, ite_false]
    exact run
  · simpa only [copyState, copyCost, w, ite_true] using (wide_copy site state source target (input.wide w)).run

theorem FieldInputs.final_pc {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) :
    (copyState site state).pc = BitVec.ofNat 64 (4096+4*(site.start+2*site.halfwords)) := by
  cases w : site.wide
  · have pc := copy_field_pc (fieldCode site) state source target (input.ready w)
    rw [plain_count site w] at pc
    simpa only [copyState, w, Bool.false_eq_true, ite_false, fieldCode] using pc
  · rw [wide_halfwords site w]
    simpa only [copyState, w, ite_true] using (wide_copy site state source target (input.wide w)).pc

theorem copy_register (site : CopySite) (state : MachineState) (reg : Reg) (kept : reg ≠ .x31)
    (free : site.wide = false ∨ reg ≠ .x29) :
    (copyState site state).getReg reg = state.getReg reg := by
  cases w : site.wide
  · simpa only [copyState, w, Bool.false_eq_true, ite_false] using copy_field_register (fieldCode site) state reg kept
  · have other : reg ≠ .x29 := by
      rcases free with h | h
      · simp [w] at h
      · exact h
    simp only [copyState, w, ite_true]
    exact wide_regs site state reg kept other

theorem FieldInputs.bytes {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) :
    ByteCopy state (copyState site state) source target (2*site.halfwords) := by
  cases w : site.wide
  · have mem : (copyState site state).mem =
        (ProjectedHalfword.copyLoopMemory false site.halfwords state (BitVec.ofNat 64 source)
          (BitVec.ofNat 64 target)).mem := by
      have m := copy_field_memory (fieldCode site) state source target (input.ready w)
      rw [plain_count site w] at m
      simpa only [copyState, w, Bool.false_eq_true, ite_false] using m
    have targetBound : target+2*site.halfwords ≤ 2^64 :=
      input.targetFit.trans (by decide)
    obtain ⟨copied, frame⟩ := forward_disjoint_memory site.halfwords state source target
      input.disjoint (input.disjoint.trans (Nat.le_trans (Nat.le_add_right _ _) targetBound)) targetBound
      input.sourceEven input.targetEven
    exact ⟨fun index inside => by
      simpa only [MachineState.getByte, MachineState.getMem, mem] using copied index inside,
      fun address outside => by
        simpa only [MachineState.getByte, MachineState.getMem, mem] using frame address outside⟩
  · rw [wide_halfwords site w]
    simpa only [copyState, w, ite_true] using (wide_copy site state source target (input.wide w)).bytes

theorem aligned_dword_above (base target : Nat) (baseAligned : base % 8 = 0)
    (above : base ≤ target) (fit : target+8 ≤ 2^64) :
    base ≤ (alignToDword (BitVec.ofNat 64 target)).toNat := by
  let word : Word := BitVec.ofNat 64 target
  let aligned := alignToDword word
  have wordAsNat : word.toNat = target := by
    simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : target < 2^64)]
  have alignedAtMost : aligned.toNat ≤ target := by
    rw [show aligned.toNat = word.toNat &&& (~~~7#64).toNat by exact BitVec.toNat_and _ _]
    exact Nat.and_le_left.trans (le_of_eq wordAsNat)
  have offset : byteOffset word < 8 := byteOffset_lt_8
  have whole := congrArg BitVec.toNat (alignToDword_add_byteOffset word)
  change (aligned+BitVec.ofNat 64 (byteOffset word)).toNat = word.toNat at whole
  rw [BitVec.toNat_add, wordAsNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : byteOffset word < 2^64),
    Nat.mod_eq_of_lt (by omega)] at whole
  have even := alignToDword_byteOffset_zero word
  change (aligned &&& 7#64).toNat = 0 at even
  rw [BitVec.toNat_and] at even
  change aligned.toNat &&& (2^3-1) = 0 at even
  rw [Nat.and_two_pow_sub_one_eq_mod] at even
  change base ≤ aligned.toNat
  omega

private theorem copyLoop_words_before (count : Nat) (state : MachineState) (source target base address : Nat)
    (below : address < base) (upper : base ≤ target) (baseAligned : base % 8 = 0)
    (fit : target+2*count ≤ MEMORY_BYTES) :
    (ProjectedHalfword.copyLoopMemory false count state (BitVec.ofNat 64 source)
      (BitVec.ofNat 64 target)).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  induction count generalizing state source target with
  | zero => rfl
  | succ count ih =>
    have shift (x : Nat) : ProjectedHalfword.advance false (BitVec.ofNat 64 x) =
        BitVec.ofNat 64 (x+2) := by
      rw [BitVec.ofNat_add]
      rfl
    simp only [ProjectedHalfword.copyLoopMemory, shift]
    rw [ih _ (source+2) (target+2) (by omega) (by omega)]
    unfold MachineState.setHalfword
    apply MachineState.getMem_setMem_ne
    intro equal
    have limit : MEMORY_BYTES+8 ≤ 2^64 := by decide
    have align := aligned_dword_above base target baseAligned upper (by omega)
    rw [← equal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address < 2^64)] at align
    omega

theorem FieldInputs.words_before {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) (base address : Nat)
    (below : address < base) (upper : base ≤ target) (aligned : base % 8 = 0) :
    (copyState site state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  cases w : site.wide
  · have mem : (copyState site state).mem =
        (ProjectedHalfword.copyLoopMemory false site.halfwords state (BitVec.ofNat 64 source)
          (BitVec.ofNat 64 target)).mem := by
      have m := copy_field_memory (fieldCode site) state source target (input.ready w)
      rw [plain_count site w] at m
      simpa only [copyState, w, Bool.false_eq_true, ite_false] using m
    simpa only [MachineState.getMem, mem] using
      copyLoop_words_before site.halfwords state source target base address below upper aligned
        input.targetFit
  · have done := wide_copy site state source target (input.wide w)
    have fit : address < 2^64 := by have := input.targetFit; unfold MEMORY_BYTES at this; omega
    have stable := done.below (BitVec.ofNat 64 address) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]; omega)
    simpa only [copyState, w, ite_true] using stable

end TwoPermutationPrototype.GroupedOpening
