import CommitGolfCandidate.GroupOpenWideCopy28

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Wide Shifted30 CapCopy
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Writer16

def cycles (target : Nat) : Nat := if target % 4 = 0 then 12 else 15

def entered (s : MachineState) := Writer28.testState s 3 56
def aligned (s : MachineState) := execInstrBr (entered s) (.JAL .x0 7624)
def words (s : MachineState) :=
  execInstrBr (pairsRun 4 .x7 0 0 0 4 (aligned s)) (.JAL .x0 2089500)
def chunks (s : MachineState) :=
  execCode (execCode (entered s) (Shifted32.chunkCode .x7 0 0)) (Shifted32.chunkCode .x7 0 8)
def shifted (s : MachineState) := execInstrBr (chunks s) (.JAL .x0 8)
def state (s : MachineState) := if (s.getReg .x21).toNat % 4 = 0 then words s else shifted s

theorem jump {s t : MachineState} {S T n c word : Nat} (copy : Done s t S T n c word)
    (off : BitVec 21) (bound : word<1976) (code : Decodes word (.JAL .x0 off))
    (target : BitVec.ofNat 64 (4096+4*word)+signExtend21 off=BitVec.ofNat 64 (4096+4*34)) :
    Done s (execInstrBr t (.JAL .x0 off)) S T n (c+1) 34 := by
  have mem : (execInstrBr t (.JAL .x0 off)).mem=t.mem := rfl
  refine ⟨copy.run.next (run_step t word _ bound copy.pc code rfl rfl), ?_, ?_,
    copy_congr_mem mem copy.bytes, ?_⟩
  · change t.pc+signExtend21 off=_; rw [copy.pc, target]
  · intro r h
    have same : (execInstrBr t (.JAL .x0 off)).getReg r=t.getReg r := by cases r <;> rfl
    exact same.trans (copy.regs r h)
  · intro q low; exact (getMem_congr mem q).trans (copy.below q low)

private theorem chunks_code : ∀ k : Fin 2,
    CodeAt (20+6*k.val) (Shifted32.chunkCode .x7 0 (8*k.val)) := by
  unfold CodeAt; decide +kernel

theorem copy (s : MachineState) (S T : Nat) (pc : s.pc=BitVec.ofNat 64 (4096+4*18))
    (src : s.getReg .x7=BitVec.ofNat 64 S) (dst : s.getReg .x21=BitVec.ofNat 64 T)
    (sa : S%8=0) (ta : T%2=0) (apart : S+28 ≤ T) (room : T+28 ≤ MEMORY_BYTES) :
    Done s (state s) S T 16 (cycles T) 34 := by
  have fit : T<2^64 := by unfold MEMORY_BYTES at room; omega
  have tn : (s.getReg .x21).toNat=T := by rw [dst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  obtain ⟨ra, pa, ga, ma⟩ := Writer28.test s T 18 4 3 56 (by decide) pc (by decide +kernel)
    (by decide +kernel) (by decide) (mask_bits s T 3 (by simp) dst fit)
  by_cases four : T%4=0
  · have pca : (entered s).pc=BitVec.ofNat 64 (4096+4*33) := by
      rw [if_pos four] at pa
      exact pa.trans (by decide)
    have rb := run_step (entered s) 33 (.JAL .x0 7624) (by decide) pca (by decide +kernel) rfl rfl
    have pcb : (aligned s).pc=BitVec.ofNat 64 (4096+4*1939) := by
      change (entered s).pc+signExtend21 7624=_; rw [pca]; decide
    have gb (r : Reg) (_ : r ≠ .x31) : (aligned s).getReg r=(entered s).getReg r := by cases r <;> rfl
    have mb : (aligned s).mem=(entered s).mem := rfl
    have sr : (aligned s).getReg .x7=BitVec.ofNat 64 S := (gb _ (by decide)).trans ((ga _ (by decide)).trans src)
    have dr : (aligned s).getReg .x21=BitVec.ofNat 64 T := (gb _ (by decide)).trans ((ga _ (by decide)).trans dst)
    have a := pairs (aligned s) S T 1939 0 4 4 (by omega) (by decide +kernel) (by decide) pcb sr dr
      (by omega) (by omega) (by decide) (by omega) (by omega)
    have body := Writer16.jump a 2089500 (by decide) (by decide +kernel) (by decide)
    simpa [state, tn, four, cycles, words] using before ra ga ma (before rb gb mb body)
  · have pca : (entered s).pc=BitVec.ofNat 64 (4096+4*20) := by simpa [entered, four] using pa
    have mod4 : T%4=2 := by omega
    have a := chunk_at 20 (0 : Fin 3) (entered s) S T (chunks_code 0) (by decide) pca
      ((ga _ (by decide)).trans src) ((ga _ (by decide)).trans dst) sa mod4 apart room
    have b := chunk_at 20 (1 : Fin 3) _ S T (chunks_code 1) (by decide) a.pc
      ((a.regs _ (by decide)).trans ((ga _ (by decide)).trans src))
      ((a.regs _ (by decide)).trans ((ga _ (by decide)).trans dst)) sa mod4 apart room
    have body := Writer16.jump (append a b (by omega) (by omega)) 8 (by decide) (by decide +kernel) (by decide)
    simpa [state, tn, four, cycles, shifted, chunks] using before ra ga ma body

end Writer16
end TwoPermutationPrototype.GroupedOpening
