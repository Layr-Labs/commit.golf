import CommitGolfCandidate.ChainedRootWords

/-! Root readback from projected stores, and complete parent-phase content. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
attribute [local irreducible] parentLevels checkEvaluation readBuffer

theorem root_buffers_separate (s : MachineState) (heap : s.getReg .x9 = 4294971424)
    (output : s.getReg .x8 = 4294971392) :
    ∀ a b : Fin 4, s.getReg .x9+BitVec.ofNat 64 (32+8*a.val) ≠
      s.getReg .x8+BitVec.ofNat 64 (8*b.val) := by
  intro a b same
  rw [heap,output] at same
  have numeric := congrArg BitVec.toNat same
  change (BitVec.ofNat 64 4294971424+BitVec.ofNat 64 (32+8*a.val)).toNat =
    (BitVec.ofNat 64 4294971392+BitVec.ofNat 64 (8*b.val)).toNat at numeric
  have ha := a.isLt
  have hb := b.isLt
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 4294971424+(32+8*a.val) < 2^64 by omega),
    Nat.mod_eq_of_lt (show 4294971392+8*b.val < 2^64 by omega)] at numeric
  omega

theorem chained_root_copy_output (s : MachineState) (heap : s.getReg .x9 = 4294971424)
    (output : s.getReg .x8 = 4294971392) :
    readBuffer (chainedRootPrefix s 10) 4294971392 32 = heapDigest s 1 := by
  unfold heapDigest
  apply output_ext_words
  intro i
  rw [read_digest_word _ _ i.val (by decide) i.isLt,
    read_digest_word s (heapBase+32*1) i.val (by decide) i.isLt,root_tail_memory]
  have copied := root_target_word s i 4 (by decide) (root_buffers_separate s heap output)
  have target : s.getReg .x8+BitVec.ofNat 64 (8*i.val) = BitVec.ofNat 64 (4294971392+8*i.val) := by
    rw [output]
    change BitVec.ofNat 64 4294971392+BitVec.ofNat 64 (8*i.val) = _
    rw [←BitVec.ofNat_add]
  have source : s.getReg .x9+BitVec.ofNat 64 (32+8*i.val) = BitVec.ofNat 64 (heapBase+32*1+8*i.val) := by
    rw [heap]
    change BitVec.ofNat 64 heapBase+BitVec.ofNat 64 (32+8*i.val) = _
    rw [←BitVec.ofNat_add]
    congr 1
    omega
  simpa only [target,source,ite_eq_left i.isLt] using copied

end CommitGolfCandidate.Chained.Native
