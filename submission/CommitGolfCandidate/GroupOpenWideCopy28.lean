import CommitGolfCandidate.GroupOpenCapCopy

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Wide Shifted30 CapCopy
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Writer28

def cycles (target : Nat) : Nat :=
  if target % 4 = 0 then (if target % 8 = 0 then 12 else 19) else 26

def testState (s : MachineState) (mask : BitVec 12) (off : BitVec 13) : MachineState :=
  execInstrBr (execInstrBr s (.ANDI .x31 .x21 mask)) (.BEQ .x31 .x0 off)

def entered (s : MachineState) := testState s 3 8
def aligned (s : MachineState) := testState (entered s) 7 64
def words (s : MachineState) :=
  execInstrBr (pairsRun 4 .x7 0 0 0 7 (aligned s)) (.JAL .x0 36)
def dwords (s : MachineState) :=
  pairsRun 4 .x7 24 24 0 1 (pairsRun 8 .x7 0 0 0 3 (aligned s))
def routed (s : MachineState) := execInstrBr (entered s) (.JAL .x0 5204)
def chunks (s : MachineState) :=
  execCode (execCode (execCode (routed s) (Shifted32.chunkCode .x7 0 0))
    (Shifted32.chunkCode .x7 0 8)) (Shifted32.chunkCode .x7 0 16)
def shifted (s : MachineState) :=
  execInstrBr (pairsRun 2 .x7 24 24 0 2 (chunks s)) (.JAL .x0 2091964)
def state (s : MachineState) : MachineState :=
  if (s.getReg .x21).toNat % 4 = 0 then
    if (s.getReg .x21).toNat % 8 = 0 then dwords s else words s
  else shifted s

theorem jump {s t : MachineState} {S T n c word : Nat} (copy : Done s t S T n c word)
    (off : BitVec 21) (bound : word<1976) (code : Decodes word (.JAL .x0 off))
    (target : BitVec.ofNat 64 (4096+4*word)+signExtend21 off=BitVec.ofNat 64 (4096+4*638)) :
    Done s (execInstrBr t (.JAL .x0 off)) S T n (c+1) 638 := by
  have mem : (execInstrBr t (.JAL .x0 off)).mem=t.mem := rfl
  refine ⟨copy.run.next (run_step t word _ bound copy.pc code rfl rfl), ?_, ?_,
    copy_congr_mem mem copy.bytes, ?_⟩
  · change t.pc+signExtend21 off=_; rw [copy.pc, target]
  · intro r h
    have same : (execInstrBr t (.JAL .x0 off)).getReg r=t.getReg r := by cases r <;> rfl
    exact same.trans (copy.regs r h)
  · intro q low; exact (getMem_congr mem q).trans (copy.below q low)

theorem test (s : MachineState) (T word modulus : Nat) (mask : BitVec 12) (off : BitVec 13)
    (bound : word+1<1976) (pc : s.pc=BitVec.ofNat 64 (4096+4*word))
    (code1 : Decodes word (.ANDI .x31 .x21 mask))
    (code2 : Decodes (word+1) (.BEQ .x31 .x0 off))
    (small : 0<modulus ∧ modulus ≤ 8)
    (bits : s.getReg .x21 &&& signExtend12 mask=BitVec.ofNat 64 (T%modulus)) :
    RunsOpeningBlock s (testState s mask off) 2 ∧
      (testState s mask off).pc=(if T%modulus=0 then
        BitVec.ofNat 64 (4096+4*(word+1))+signExtend13 off
        else BitVec.ofNat 64 (4096+4*(word+2))) ∧
      (∀ r, r ≠ .x31 → (testState s mask off).getReg r=s.getReg r) ∧
      (testState s mask off).mem=s.mem := by
  let a := execInstrBr s (.ANDI .x31 .x21 mask)
  obtain ⟨pa, va, ma⟩ := andi_facts s mask
  have pca : a.pc=BitVec.ofNat 64 (4096+4*(word+1)) := by rw [pa, pc, ofNat_four]
  have run1 := run_step s word _ (by omega) pc code1 rfl rfl
  have run2 := run_step a (word+1) _ bound pca code2 rfl rfl
  obtain ⟨pb, mb⟩ := beq_facts a off
  have regb (r : Reg) : (testState s mask off).getReg r=a.getReg r := by
    by_cases zero : r = .x0
    · subst r; rfl
    · exact mb.regs r zero
  refine ⟨run1.next run2, ?_, fun r h => (regb r).trans (ma.regs r h),
    mb.mem.trans ma.mem⟩
  change (execInstrBr a (.BEQ .x31 .x0 off)).pc = _
  rw [pb, va, bits, pca]
  by_cases zero : T%modulus=0
  · simp only [zero, ite_true]
  · have ne : BitVec.ofNat 64 (T%modulus) ≠ (0#64) := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat] at h
      have := Nat.mod_lt T small.1
      omega
    simp only [ne, if_false, zero]
    rw [ofNat_four]

private theorem chunks_code : ∀ k : Fin 3,
    CodeAt (1913+6*k.val) (Shifted32.chunkCode .x7 0 (8*k.val)) := by
  unfold CodeAt; decide +kernel

theorem shifted_done (s : MachineState) (S T : Nat)
    (src : s.getReg .x7=BitVec.ofNat 64 S) (dst : s.getReg .x21=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%4=2) (apart : S+28 ≤ T) (room : T+28 ≤ MEMORY_BYTES)
    (ran : RunsOpeningBlock s (routed s) 3)
    (epc : (routed s).pc=BitVec.ofNat 64 (4096+4*1913))
    (regs : ∀ r, r ≠ .x31 → (routed s).getReg r=s.getReg r)
    (mem : (routed s).mem=s.mem) : Done s (shifted s) S T 28 26 638 := by
  have a := chunk_at 1913 (0 : Fin 3) (routed s) S T (chunks_code 0) (by decide) epc
    ((regs _ (by decide)).trans src) ((regs _ (by decide)).trans dst) sa ta apart room
  have b := chunk_at 1913 (1 : Fin 3) _ S T (chunks_code 1) (by decide) a.pc
    ((a.regs _ (by decide)).trans ((regs _ (by decide)).trans src))
    ((a.regs _ (by decide)).trans ((regs _ (by decide)).trans dst)) sa ta apart room
  have ab := append a b (by omega) (by omega)
  have c := chunk_at 1913 (2 : Fin 3) _ S T (chunks_code 2) (by decide) b.pc
    ((ab.regs _ (by decide)).trans ((regs _ (by decide)).trans src))
    ((ab.regs _ (by decide)).trans ((regs _ (by decide)).trans dst)) sa ta apart room
  have abc := append ab c (by omega) (by omega)
  have d := pairs _ S T 1931 24 2 2 (by omega) (by decide +kernel) (by decide) c.pc
    ((abc.regs _ (by decide)).trans ((regs _ (by decide)).trans src))
    ((abc.regs _ (by decide)).trans ((regs _ (by decide)).trans dst))
    (by omega) (by omega) (by decide) apart (by omega)
  have both := append abc d (by omega) (by omega)
  exact before ran regs mem (Writer28.jump both 2091964 (by decide) (by decide +kernel) (by decide))

theorem copy (s : MachineState) (S T : Nat) (pc : s.pc=BitVec.ofNat 64 (4096+4*610))
    (src : s.getReg .x7=BitVec.ofNat 64 S) (dst : s.getReg .x21=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%2=0) (apart : S+28 ≤ T) (room : T+28 ≤ MEMORY_BYTES) :
    Done s (state s) S T 28 (cycles T) 638 := by
  have fit : T<2^64 := by unfold MEMORY_BYTES at room; omega
  have tn : (s.getReg .x21).toNat=T := by rw [dst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  obtain ⟨ra, pa, ga, ma⟩ := test s T 610 4 3 8 (by decide) pc (by decide +kernel)
    (by decide +kernel) (by decide) (mask_bits s T 3 (by simp) dst fit)
  by_cases four : T%4=0
  · have pca : (entered s).pc=BitVec.ofNat 64 (4096+4*613) := by
      rw [if_pos four] at pa
      exact pa.trans (by decide)
    obtain ⟨rc, pc', gc, mc⟩ := test (entered s) T 613 8 7 64 (by decide) pca (by decide +kernel)
      (by decide +kernel) (by decide) (mask_bits (entered s) T 7 (by simp) ((ga _ (by decide)).trans dst) fit)
    have sr : (aligned s).getReg .x7=BitVec.ofNat 64 S := (gc _ (by decide)).trans ((ga _ (by decide)).trans src)
    have dr : (aligned s).getReg .x21=BitVec.ofNat 64 T := (gc _ (by decide)).trans ((ga _ (by decide)).trans dst)
    by_cases eight : T%8=0
    · have dpc : (aligned s).pc=BitVec.ofNat 64 (4096+4*630) := by
        rw [if_pos eight] at pc'
        exact pc'.trans (by decide)
      have a := pairs (aligned s) S T 630 0 8 3 (by omega) (by decide +kernel) (by decide) dpc sr dr
        (by omega) (by omega) (by decide) (by omega) (by omega)
      have d := pairs _ S T 636 24 4 1 (by omega) (by decide +kernel) (by decide) a.pc
        ((a.regs _ (by decide)).trans sr) ((a.regs _ (by decide)).trans dr)
        (by omega) (by omega) (by decide) apart (by omega)
      have body := append a d (by omega) (by omega)
      simpa [state, tn, four, eight, cycles, dwords, aligned, entered] using
        before ra ga ma (before rc gc mc body)
    · have wpc : (aligned s).pc=BitVec.ofNat 64 (4096+4*615) := by simpa [eight, aligned] using pc'
      have a := pairs (aligned s) S T 615 0 4 7 (by omega) (by decide +kernel) (by decide) wpc sr dr
        (by omega) (by omega) (by decide) apart (by omega)
      have body := Writer28.jump a 36 (by decide) (by decide +kernel) (by decide)
      simpa [state, tn, four, eight, cycles, words, aligned, entered] using
        before ra ga ma (before rc gc mc body)
  · have pca : (entered s).pc=BitVec.ofNat 64 (4096+4*612) := by simpa [entered, four] using pa
    have rb := run_step (entered s) 612 (.JAL .x0 5204) (by decide) pca (by decide +kernel) rfl rfl
    have pcb : (routed s).pc=BitVec.ofNat 64 (4096+4*1913) := by
      change (entered s).pc+signExtend21 5204=_; rw [pca]; decide
    have gb (r : Reg) (h : r ≠ .x31) : (routed s).getReg r=s.getReg r := by
      have same : (routed s).getReg r=(entered s).getReg r := by cases r <;> rfl
      exact same.trans (ga r h)
    have mb : (routed s).mem=s.mem := ma
    simpa [state, cycles, tn, four] using shifted_done s S T src dst sa (by omega) apart room (ra.next rb) pcb gb mb

end Writer28
end TwoPermutationPrototype.GroupedOpening
