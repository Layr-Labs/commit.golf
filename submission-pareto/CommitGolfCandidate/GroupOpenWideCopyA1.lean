import CommitGolfCandidate.GroupOpenWideCopy28

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Wide Shifted30 CapCopy
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace WriterA1

def cycles (target : Nat) : Nat :=
  if target % 4 = 0 then (if target % 8 = 0 then 14 else 22) else 27

def entered (s : MachineState) := Writer28.testState s 3 104
def aligned (s : MachineState) := Writer28.testState (execInstrBr (entered s) (.JAL .x0 6924)) 7 72
def words (s : MachineState) := execInstrBr (pairsRun 4 .x7 0 0 0 8 (aligned s)) (.JAL .x0 2090168)
def dwords (s : MachineState) := execInstrBr (pairsRun 8 .x7 0 0 0 4 (aligned s)) (.JAL .x0 2090132)
def chunks (s : MachineState) :=
  execCode (execCode (execCode (execCode (entered s) (Shifted32.chunkCode .x7 0 0))
    (Shifted32.chunkCode .x7 0 8)) (Shifted32.chunkCode .x7 0 16)) (Shifted32.chunkCode .x7 0 24)
def shifted (s : MachineState) := execInstrBr (chunks s) (.JAL .x0 16)
def state (s : MachineState) : MachineState :=
  if (s.getReg .x21).toNat % 4 = 0 then
    if (s.getReg .x21).toNat % 8 = 0 then dwords s else words s
  else shifted s

theorem jump {s t : MachineState} {S T n c word : Nat} (copy : Done s t S T n c word)
    (off : BitVec 21) (bound : word<1976) (code : Decodes word (.JAL .x0 off))
    (target : BitVec.ofNat 64 (4096+4*word)+signExtend21 off=BitVec.ofNat 64 (4096+4*220)) :
    Done s (execInstrBr t (.JAL .x0 off)) S T n (c+1) 220 := by
  have mem : (execInstrBr t (.JAL .x0 off)).mem=t.mem := rfl
  refine ⟨copy.run.next (run_step t word _ bound copy.pc code rfl rfl), ?_, ?_,
    copy_congr_mem mem copy.bytes, ?_⟩
  · change t.pc+signExtend21 off=_; rw [copy.pc, target]
  · intro r h
    have same : (execInstrBr t (.JAL .x0 off)).getReg r=t.getReg r := by cases r <;> rfl
    exact same.trans (copy.regs r h)
  · intro q low; exact (getMem_congr mem q).trans (copy.below q low)

private theorem chunks_code : ∀ k : Fin 4,
    CodeAt (192+6*k.val) (Shifted32.chunkCode .x7 0 (8*k.val)) := by
  unfold CodeAt; decide +kernel

theorem shifted_done (s : MachineState) (S T : Nat)
    (src : s.getReg .x7=BitVec.ofNat 64 S) (dst : s.getReg .x21=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%4=2) (apart : S+32 ≤ T) (room : T+32 ≤ MEMORY_BYTES)
    (ran : RunsOpeningBlock s (entered s) 2)
    (epc : (entered s).pc=BitVec.ofNat 64 (4096+4*192))
    (regs : ∀ r, r ≠ .x31 → (entered s).getReg r=s.getReg r)
    (mem : (entered s).mem=s.mem) : Done s (shifted s) S T 32 27 220 := by
  have a := chunk_at_width 192 4 (0 : Fin 4) (entered s) S T (chunks_code 0) (by decide) (by decide) epc
    ((regs _ (by decide)).trans src) ((regs _ (by decide)).trans dst) sa ta apart room
  have b := chunk_at_width 192 4 (1 : Fin 4) _ S T (chunks_code 1) (by decide) (by decide) a.pc
    ((a.regs _ (by decide)).trans ((regs _ (by decide)).trans src))
    ((a.regs _ (by decide)).trans ((regs _ (by decide)).trans dst)) sa ta apart room
  have ab := append a b (by omega) (by omega)
  have c := chunk_at_width 192 4 (2 : Fin 4) _ S T (chunks_code 2) (by decide) (by decide) b.pc
    ((ab.regs _ (by decide)).trans ((regs _ (by decide)).trans src))
    ((ab.regs _ (by decide)).trans ((regs _ (by decide)).trans dst)) sa ta apart room
  have abc := append ab c (by omega) (by omega)
  have d := chunk_at_width 192 4 (3 : Fin 4) _ S T (chunks_code 3) (by decide) (by decide) c.pc
    ((abc.regs _ (by decide)).trans ((regs _ (by decide)).trans src))
    ((abc.regs _ (by decide)).trans ((regs _ (by decide)).trans dst)) sa ta apart room
  have body := append abc d (by omega) (by omega)
  exact before ran regs mem (WriterA1.jump body 16 (by decide) (by decide +kernel) (by decide))

theorem copy (s : MachineState) (S T : Nat) (pc : s.pc=BitVec.ofNat 64 (4096+4*190))
    (src : s.getReg .x7=BitVec.ofNat 64 S) (dst : s.getReg .x21=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%2=0) (apart : S+32 ≤ T) (room : T+32 ≤ MEMORY_BYTES) :
    Done s (state s) S T 32 (cycles T) 220 := by
  have fit : T<2^64 := by unfold MEMORY_BYTES at room; omega
  have tn : (s.getReg .x21).toNat=T := by rw [dst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  obtain ⟨ra, pa, ga, ma⟩ := Writer28.test s T 190 4 3 104 (by decide) pc (by decide +kernel)
    (by decide +kernel) (by decide) (mask_bits s T 3 (by simp) dst fit)
  by_cases four : T%4=0
  · have pca : (entered s).pc=BitVec.ofNat 64 (4096+4*217) := by
      rw [if_pos four] at pa
      exact pa.trans (by decide)
    let b := execInstrBr (entered s) (.JAL .x0 6924)
    have rb := run_step (entered s) 217 (.JAL .x0 6924) (by decide) pca (by decide +kernel) rfl rfl
    have pcb : b.pc=BitVec.ofNat 64 (4096+4*1948) := by
      change (entered s).pc+signExtend21 6924=_; rw [pca]; decide
    have gb (r : Reg) (_ : r ≠ .x31) : b.getReg r=(entered s).getReg r := by cases r <;> rfl
    have mb : b.mem=(entered s).mem := rfl
    have gr (r : Reg) (h : r ≠ .x31) : b.getReg r=s.getReg r := (gb r h).trans (ga r h)
    obtain ⟨rc, pc', gc, mc⟩ := Writer28.test b T 1948 8 7 72 (by decide) pcb (by decide +kernel)
      (by decide +kernel) (by decide) (mask_bits b T 7 (by simp) ((gr _ (by decide)).trans dst) fit)
    have sr : (aligned s).getReg .x7=BitVec.ofNat 64 S := (gc _ (by decide)).trans ((gr _ (by decide)).trans src)
    have dr : (aligned s).getReg .x21=BitVec.ofNat 64 T := (gc _ (by decide)).trans ((gr _ (by decide)).trans dst)
    by_cases eight : T%8=0
    · have dpc : (aligned s).pc=BitVec.ofNat 64 (4096+4*1967) := by
        rw [if_pos eight] at pc'
        exact pc'.trans (by decide)
      have a := pairs (aligned s) S T 1967 0 8 4 (by omega) (by decide +kernel) (by decide) dpc sr dr
        (by omega) (by omega) (by decide) apart room
      have body := WriterA1.jump a 2090132 (by decide) (by decide +kernel) (by decide)
      simpa [state, tn, four, eight, cycles, dwords, aligned, entered, b] using
        before ra ga ma (before rb gb mb (before rc gc mc body))
    · have wpc : (aligned s).pc=BitVec.ofNat 64 (4096+4*1950) := by simpa [eight, aligned, b] using pc'
      have a := pairs (aligned s) S T 1950 0 4 8 (by omega) (by decide +kernel) (by decide) wpc sr dr
        (by omega) (by omega) (by decide) apart room
      have body := WriterA1.jump a 2090168 (by decide) (by decide +kernel) (by decide)
      simpa [state, tn, four, eight, cycles, words, aligned, entered, b] using
        before ra ga ma (before rb gb mb (before rc gc mc body))
  · have pca : (entered s).pc=BitVec.ofNat 64 (4096+4*192) := by simpa [entered, four] using pa
    simpa [state, cycles, tn, four] using shifted_done s S T src dst sa (by omega) apart room ra pca ga ma

end WriterA1
end TwoPermutationPrototype.GroupedOpening
