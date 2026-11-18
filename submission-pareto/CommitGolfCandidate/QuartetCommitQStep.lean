import CommitGolfCandidate.QuartetCommitImage
import CommitGolfCandidate.QuartetCommitRanges
import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.Execution

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 850000
attribute [local irreducible] execute writeBits image

structure QRegs (s : MachineState) (g : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (qSource g)
  dest : s.getReg .x12 = wordAddress (qUpper g)
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1
  stop : s.getReg .x24=wordAddress (qSource 4194304)

def quadArgument (s : MachineState) (g : Nat) : BitVec 1600 :=
  packBuffer (window (memoryView s) (qSource g))
def qMove (s : MachineState) := execInstrBr s (.ADDI .x10 .x10 512)
def qMoves (s : MachineState) := execInstrBr (qMove s) (.ADDI .x12 .x12 32)
def qAfter (s : MachineState) (g : Nat) (reply : BitVec 1600) :=
  qMoves (writeBits s (wordAddress (qUpper g)) reply)

theorem q_next_pc (slot : Nat) : quadPC slot + 12 = quadPC (slot+1) := by
  change BitVec.ofNat 64 _+BitVec.ofNat 64 12=_
  unfold quadPC wordPC;rw [←BitVec.ofNat_add];congr 1 <;> omega

theorem q_post_pc (s : MachineState) (g : Nat) (reply : BitVec 1600) :
    (qAfter s g reply).pc = s.pc+12 := by
  change (writeBits s (wordAddress (qUpper g)) reply).pc+4+4=_
  rw [written_pc,BitVec.add_assoc,BitVec.add_assoc];rfl

theorem q_saved (s : MachineState) (g : Nat) (reply : BitVec 1600) (reg : Reg)
    (src : reg≠.x10) (dst : reg≠.x12) :
    (qAfter s g reply).getReg reg=s.getReg reg := by
  simp only [qAfter,qMoves,qMove,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm src), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm dst),
    CommitGolfCandidate.writeBits_register]

theorem q_next_regs (s : MachineState) (g : Nat) (reply : BitVec 1600) (r : QRegs s g) :
    QRegs (qAfter s g reply) (g+1) := by
  refine ⟨?_,?_,(q_saved s g reply .x5 (by decide) (by decide)).trans r.selector,
    (q_saved s g reply .x11 (by decide) (by decide)).trans r.size,
    (q_saved s g reply .x13 (by decide) (by decide)).trans r.primitive,
    (q_saved s g reply .x24 (by decide) (by decide)).trans r.stop⟩
  · change (writeBits s _ reply).getReg .x10+512=_
    rw [CommitGolfCandidate.writeBits_register,r.source]
    change wordAddress (qSource g)+wordAddress 64=_
    rw [←wordAddress_add];congr 1 <;> unfold qSource <;>omega
  · change (writeBits s _ reply).getReg .x12+32=_
    rw [CommitGolfCandidate.writeBits_register,r.dest]
    change wordAddress (qUpper g)+wordAddress 4=_
    rw [←wordAddress_add];congr 1 <;> unfold qUpper <;>omega

private theorem q_two_moves (s : MachineState) (slot : Fin 512) (pc : s.pc=quadPC slot.val+4)
    (fuel : Nat) :
    execute image (2+fuel) s true =
      (do let res ← execute image fuel (qMoves s) true; return res.charge 2 0) := by
  have f1 : fetch image s=some (.base (.ADDI .x10 .x10 512)) := fetch_quad s slot 1 pc
  have nextPC : (qMove s).pc=quadPC slot.val+8 := by
    change s.pc+4=_;rw [pc,BitVec.add_assoc];rfl
  have f2 : fetch image (qMove s)=some (.base (.ADDI .x12 .x12 32)) :=
    fetch_quad (qMove s) slot 2 nextPC
  rw [show 2+fuel=(fuel+1)+1 by omega,
    CommitGolfCandidate.execute_ordinary_step image _ s (qMove s) _ true f1 rfl,
    CommitGolfCandidate.execute_ordinary_step image _ (qMove s) (qMoves s) _ true f2 rfl]
  simp [Execution.charge,instructionCycles,←Nat.add_assoc]

theorem q_unit_run (s : MachineState) (g : Nat) (slot : Fin 512) (fuel : Nat)
    (hg : g<4194304) (r : QRegs s g) (pc : s.pc=quadPC slot.val) :
    execute image (3+fuel) s true = (do
      let reply ← World.query (.inr (.inr (.inl (quadArgument s g))))
      let res ← execute image fuel (qAfter s g reply) true
      return res.charge 10 1) := by
  have fetched : fetch image s=some (.base .ECALL) :=
    fetch_quad s slot 0 (by change s.pc=quadPC slot.val+0;simpa using pc)
  have call := execute_permutation_call image (2+fuel) s true (qSource g) (qUpper g)
    (by unfold qSource;omega) (by unfold qUpper;omega) r.source r.dest r.selector r.size r.primitive fetched
  rw [show 3+fuel=(2+fuel)+1 by omega,call]
  apply bind_congr_of_forall_mem_support
  intro reply _
  have here : (writeBits s (wordAddress (qUpper g)) reply).pc=quadPC slot.val+4 := by
    rw [written_pc,pc]
  rw [q_two_moves _ slot here]
  simp [qAfter,Execution.charge,←Nat.add_assoc] <;> rfl

theorem q_unit_memory (s : MachineState) (g : Nat) (reply : BitVec 1600) (hg : g<4194304) (w : Nat) (hw : w<2^33) :
    memoryView (qAfter s g reply) w =
      writeWindow (memoryView s) (qUpper g) (replyWords reply) w := by
  change memoryView (writeBits s (wordAddress (qUpper g)) reply) w=_
  exact permutation_write_memory s _ w reply (by unfold qUpper;omega) hw

end TwoPermutationPrototype.QuartetCommit
