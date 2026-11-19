import CommitGolfCandidate.TailStreamInitial

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open ProofCodec.HeadStreamSeven
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

variable {image : Image} [CodeImage image]

theorem compact_loop (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Compact k L base H Q s0 0 s) (len : Q.length=L) (records : 480*k≤L)
    (small : L+7≤2^33) (room : base+2^34≤2^36)
    (source : ∀ j<L, s0.getByte (BitVec.ofNat 64 (base+j))=Q.getD j 0) :
    ∃ s', Compact k L base H Q s0 (L-k) s' ∧
      Runs image s s' (12*(L-k)-(479*k-435)) (15*(L-k)-(479*k-435)) := by
  obtain ⟨s',inv',runs⟩ := runs_loop (image := image) (fun p s => Compact k L base H Q s0 p s) (L-k)
    (copySteps k) (copyCycles k)
    (fun p hp s inv => compact_iter k L base H Q s0 s p inv len records small room hp source)
    (L-k) 0 s (by omega) inv
  refine ⟨s',inv',runs.cast ?_ ?_⟩
  · rw [← Finset.range_eq_Ico,copy_steps_sum,Nat.min_eq_right (by omega)]
  · rw [← Finset.range_eq_Ico,copy_cycles_sum,Nat.min_eq_right (by omega)]


theorem extract_loop (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Extract k L base H Q s0 0 s) (records : 480*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+k+8≤base+2^34)
    (source : ∀ p<L, s0.getByte (BitVec.ofNat 64 (base+p))=Q.getD p 0) :
    ∃ t, Extract k L base H Q s0 k t ∧ Runs image s t (7*k) (7*k) := by
  obtain ⟨t,inv',ran⟩ := runs_loop (image := image) (fun r s => Extract k L base H Q s0 r s) k
    (fun _ => 7) (fun _ => 7)
    (fun r hr s inv => extract_iter k L base H Q s0 s r inv records small gap room hroom hr source)
    k 0 s (by omega) inv
  refine ⟨t,inv',ran.cast ?_ ?_⟩ <;> simp [Nat.mul_comm]

def extractInit : List Nat := [0,1]
def extractExit : List Nat := [2]

theorem extract_initialize (k L base H : Nat) (Q : Proof) (s : MachineState)
    (regs : EntryRegs k L base H s) (pc : s.pc=pcOf 0) :
    Extract k L base H Q s 0 (run s extractInit) ∧ Runs image s (run s extractInit) 2 2 := by
  have ok : PathOK s extractInit := by
    simp [PathOK,extractInit,execInstrBr,pc,ordinaryInstr,memoryArgumentsValid,memAccess]
  refine ⟨⟨regs.keep extractInit (by decide),?_,?_,?_,by omega,?_⟩,
    (runs_path (image := image) _ s ok).cast rfl (by decide)⟩
  · simp [run,extractInit,execInstrBr,pc]
  · simp [run,extractInit,execInstrBr]
  · simp [run,extractInit,execInstrBr,regs.x20,w_add]
  · intro a
    rw [getByte_of_mem (run_mem extractInit s (by decide)),if_neg (by omega)]

theorem extract_exit (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Extract k L base H Q s0 k s) :
    EntryRegs k L base H (run s extractExit) ∧ (run s extractExit).pc=pcOf 9 ∧
      (∀ a, (run s extractExit).getByte a=s.getByte a) ∧ Runs image s (run s extractExit) 1 1 := by
  have regs := inv.regs
  have ok : PathOK s extractExit := by
    simp [PathOK,extractExit,execInstrBr,inv.pc,inv.x22,regs.x16,
      ordinaryInstr,memoryArgumentsValid,memAccess]
  refine ⟨regs.keep extractExit (by decide),?_,?_,(runs_path (image := image) _ s ok).cast rfl (by decide)⟩
  · simp [run,extractExit,execInstrBr,inv.pc,inv.x22,regs.x16]
  · intro a
    exact getByte_of_mem (run_mem extractExit s (by decide)) a

end TwoPermutationPrototype.PackedOpening.TailStream
