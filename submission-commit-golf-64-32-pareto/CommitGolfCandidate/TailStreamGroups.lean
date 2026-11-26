import CommitGolfCandidate.TailStreamHeads

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack ProofCodec.HeadStreamSeven
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

structure Heads (k L base H : Nat) (Q : Proof) (s0 : MachineState) (g : Nat) (s : MachineState) : Prop where
  regs : Regs k L base H s
  pc : s.pc=pcOf 37
  x22 : s.getReg .x22=BitVec.ofNat 64 g
  x28 : s.getReg .x28=BitVec.ofNat 64 (H+8*g)
  x26 : s.getReg .x26=BitVec.ofNat 64 (base+(L-k)+7*g)
  bound : g≤(k+7)/8
  mem : ∀ a : Word, s.getByte a=
    if base+(L-k)≤a.toNat ∧ a.toNat<base+(L-k)+7*g
      then headPackedByte k Q (a.toNat-(base+(L-k))) else s0.getByte a

def groupGuard : List Nat := [37]
def advance : List Nat := [94,95,96,97]
def compactExit : List Nat := [23,35,36]

@[simp] theorem group_jump : pcOf 97+signExtend21 2096912#21=pcOf 37 := by decide
@[simp] theorem group_branch : pcOf 37+signExtend13 244#13=pcOf 98 := by decide
@[simp] theorem se12_8 : signExtend12 8#12=8#64 := by decide

variable {image : Image} [CodeImage image]

set_option maxHeartbeats 1400000 in
theorem group_iter (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (g : Nat)
    (inv : Heads k L base H Q s0 g s) (records : 480*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+k+8≤base+2^34) (hg : g<(k+7)/8)
    (headers : ∀ j<k+7, (s0.getByte (BitVec.ofNat 64 (H+j))).toNat%128=head k Q j) :
    ∃ t, Heads k L base H Q s0 (g+1) t ∧ Runs image s t 61 61 := by
  have regs := inv.regs
  have ne : BitVec.ofNat 64 g≠BitVec.ofNat 64 ((k+7)/8) := by
    rw [Ne,w_inj _ _ (by omega) (by omega)];omega
  have ok : PathOK s groupGuard := by
    simp [PathOK,groupGuard,execInstrBr,inv.pc,inv.x22,regs.x7,ne,
      ordinaryInstr,memoryArgumentsValid,memAccess]
  have first : Output k L base H Q s0 g 0 (run s groupGuard) := by
    refine ⟨regs.keep groupGuard (by decide),?_,?_,?_,?_,?_⟩
    · simp [run,groupGuard,execInstrBr,inv.pc,inv.x22,regs.x7,ne]
    · exact (run_keeps _ groupGuard s (by decide)).trans inv.x22
    · exact (run_keeps _ groupGuard s (by decide)).trans inv.x28
    · exact (run_keeps _ groupGuard s (by decide)).trans inv.x26
    · intro a
      simpa only [Nat.add_zero] using
        (getByte_of_mem (run_mem groupGuard s (by decide)) a).trans (inv.mem a)
  obtain ⟨t,finished,ran⟩ := output_loop (image := image) k L base H Q s0 _ g first records small gap room hroom hg headers
  have ready := finished.regs
  have endOK : PathOK t advance := by
    simp [PathOK,advance,execInstrBr,finished.pc,
      ordinaryInstr,memoryArgumentsValid,memAccess]
  have final : Heads k L base H Q s0 (g+1) (run t advance) := by
    refine ⟨ready.keep advance (by decide),?_,?_,?_,?_,by omega,?_⟩
    · simp [run,advance,execInstrBr,finished.pc]
    · simp [run,advance,execInstrBr,finished.x22,w_add]
    · simp [run,advance,execInstrBr,finished.x28,w_add]
      congr 1 <;> omega
    · simp [run,advance,execInstrBr,finished.x26,w_add]
      congr 1 <;> omega
    · intro a
      rw [getByte_of_mem (run_mem advance t (by decide)),finished.mem]
      rw [show 7*g+7=7*(g+1) by omega]
  exact ⟨_,final,(((runs_path (image := image) _ s ok).trans ran).trans
    (runs_path (image := image) _ t endOK)).cast rfl (by decide)⟩

theorem group_loop (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L base H Q s0 0 s) (records : 480*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+k+8≤base+2^34)
    (headers : ∀ j<k+7, (s0.getByte (BitVec.ofNat 64 (H+j))).toNat%128=head k Q j) :
    ∃ t, Heads k L base H Q s0 ((k+7)/8) t ∧ Runs image s t (61*((k+7)/8)) (61*((k+7)/8)) := by
  obtain ⟨t,inv',ran⟩ := runs_loop (image := image) (fun g s => Heads k L base H Q s0 g s) ((k+7)/8)
    (fun _ => 61) (fun _ => 61)
    (fun g hg s inv => group_iter k L base H Q s0 s g inv records small gap room hroom hg headers)
    ((k+7)/8) 0 s (by omega) inv
  refine ⟨t,inv',ran.cast ?_ ?_⟩ <;> simp [Nat.mul_comm]

theorem compact_exit (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Compact k L base H Q s0 (L-k) s) :
    Heads k L base H Q s 0 (run s compactExit) ∧ Runs image s (run s compactExit) 3 3 := by
  have regs := inv.regs
  have ok : PathOK s compactExit := by
    simp [PathOK,compactExit,execInstrBr,inv.pc,inv.x22,regs.x18,
      ordinaryInstr,memoryArgumentsValid,memAccess]
  refine ⟨⟨regs.keep compactExit (by decide),?_,?_,?_,?_,by omega,?_⟩,
    (runs_path (image := image) _ s ok).cast rfl (by decide)⟩
  · simp [run,compactExit,execInstrBr,inv.pc,inv.x22,regs.x18]
  · simp [run,compactExit,execInstrBr]
  · simp [run,compactExit,execInstrBr,regs.x27,inv.x22,regs.x18]
  · simpa only [Nat.mul_zero,Nat.add_zero] using
      (run_keeps _ compactExit s (by decide)).trans inv.x26
  · intro a
    rw [getByte_of_mem (run_mem compactExit s (by decide)),if_neg (by omega)]

end TwoPermutationPrototype.PackedOpening.TailStream
