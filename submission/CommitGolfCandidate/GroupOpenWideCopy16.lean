import CommitGolfCandidate.GroupOpenWideCopy28

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Wide Shifted30 CapCopy
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Writer16

def cycles (target : Nat) : Nat := if target % 4 = 0 then 11 else 15

def entered (s : MachineState) := Writer28.testState s 3 2960
def aligned (s : MachineState) := entered s
def words (s : MachineState) :=
  execInstrBr (pairsRun 4 .x7 0 0 0 4 (aligned s)) (.JAL .x0 2094220)
def chunks (s : MachineState) :=
  execCode (execCode (entered s) (Shifted32.chunkCode .x7 0 0)) (Shifted32.chunkCode .x7 0 8)
def shifted (s : MachineState) := execInstrBr (chunks s) (.JAL .x0 8)
def state (s : MachineState) := if (s.getReg .x21).toNat % 4 = 0 then words s else shifted s

theorem jump {s t : MachineState} {S T n c word : Nat} (copy : Done s t S T n c word)
    (off : BitVec 21) (bound : word<6144) (code : Decodes word (.JAL .x0 off))
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

end Writer16
end TwoPermutationPrototype.GroupedOpening
