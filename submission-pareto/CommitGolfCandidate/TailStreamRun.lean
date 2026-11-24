import CommitGolfCandidate.StreamCopyRun
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
      Runs openingImage s s' (StreamCopy.price 479 k L) (StreamCopy.price 479 k L) := by
  have m (q : Word) : s.getByte q=s0.getByte q := by rw [inv.mem];simp
  have input (j : Nat) (hj:j<L) : s.getByte (StreamCopy.word (base+j))=Q.getD j 0 :=
    (m _).trans (source j hj)
  have inside (r j : Nat) (hr:r<k) (hj:j<479) :
      Q.getD (480*r+StreamCopy.copyOff 479 j) 0=convertedByte k Q (479*r+j) := by
    rw [convertedByte,len,if_pos (by omega),compact_record_source _ _ (by omega)]
    rw [show (479*r+j)/479=r by omega,show (479*r+j)%479=j by omega]
    simp only [StreamCopy.copyOff,Nat.reduceSub,Nat.add_assoc]
  have footer (j : Nat) (hj:j<L-480*k) :
      Q.getD (480*k+j) 0=convertedByte k Q (479*k+j) := by
    rw [convertedByte,len,if_pos (by omega),compact_footer_source _ _ (by omega)]
    apply congrArg (fun i => Q.getD i 0)
    omega
  obtain ⟨z,ran,pc,fr,count,mem⟩:=StreamCopy.compact false k L base Q (convertedByte k Q) s
    records (by omega) inv.pc inv.regs.x16 inv.regs.x18 inv.regs.x20 inv.x22 inv.x26 input
    (fun r hr j hj=>inside r j hr hj) footer
  refine ⟨z,⟨?_,pc,count,(fr _ (by decide)).trans inv.x26,le_rfl,?_⟩,ran⟩
  · constructor <;> rw [fr _ (by decide)]
    all_goals first | exact inv.regs.x5 | exact inv.regs.x10 | exact inv.regs.x11 |
      exact inv.regs.x16 | exact inv.regs.x20 | exact inv.regs.x27 | exact inv.regs.x18 |
      exact inv.regs.x9 | exact inv.regs.x7
  · intro q;rw [mem,m]

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
