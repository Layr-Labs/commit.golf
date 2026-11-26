import CommitGolfCandidate.LateParentRun
import CommitGolfCandidate.LateTreeMemory
import CommitGolfCandidate.TruncMask

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def laneReply (s : MachineState) (d : Fin 24) (p : Nat) (w : Digest) :=
  let ready:=parentReply s p (retain (23-d.val) w)
  ready.setPC (s.pc+BitVec.ofNat 64 (4*laneWidth d))

theorem laneReply_pc (s : MachineState) (d : Fin 24) (p : Nat) (w : Digest) :
    (laneReply s d p w).pc=s.pc+BitVec.ofNat 64 (4*laneWidth d) := rfl
theorem laneReply_reg (s : MachineState) (d : Fin 24) (p : Nat) (w : Digest) (r : Reg)
    (a : Reg.x10≠r) (b : Reg.x12≠r) : (laneReply s d p w).getReg r=s.getReg r :=
  (MachineState.getReg_setPC).trans (call_register _ _ _ _ _ _ _ a b)

private theorem masked_code : ∀ d : Fin 24, ∀ j : Fin 16, maskedPhase d → j.val<tileWidth d →
    parentPC d j+3<2655 ∧ packedWord (parentPC d j+3)=0x00061f23 := by decide

private theorem clear_run {s : MachineState} {d : Fin 24} {p : Nat} (regs : ParentRegs s d p)
    (inside : p<levelCount (d.val+1)) (pc : s.pc=pcAt (parentPC d (p%16))) (cut : maskedPhase d)
    (w : Digest) (fuel : Nat) :
    execute commitImage (fuel+1) (parentReply s p w) true =
      (do let result←execute commitImage fuel (laneReply s d p w) true;pure (result.charge 1 0)) := by
  let j : Fin 16:=⟨p%16,by omega⟩
  obtain ⟨small,enc⟩:=masked_code d j cut (by unfold tileWidth;dsimp [j];omega)
  have code:=decoded_word _ small (.SH .x12 .x0 30) (by rw [enc];rfl)
  let dst:=nodeAddress (d.val+1) p
  have dest:=(parent_addresses regs).2
  have al : dst%8=0 := by unfold dst nodeAddress levelOffset gapOffset;omega
  have top:=parent_below_salts (d.val+1) p inside
  have lim : dst+32≤MEMORY_BYTES := by unfold dst;unfold rowBase at top;unfold MEMORY_BYTES;omega
  have ptr : (parentReply s p w).getReg .x12=BitVec.ofNat 64 dst := (writeBits_register ..).trans dest
  have access : memoryArgumentsValid (parentReply s p w) (.SH .x12 .x0 30)=true := by
    change accessValid ((parentReply s p w).getReg .x12+BitVec.ofNat 64 30) 2=true
    rw [ptr,←BitVec.ofNat_add];have lim64 : dst+30<2^64 := by unfold MEMORY_BYTES at lim;omega
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt lim64,show dst+30+2≤MEMORY_BYTES by omega,
      show (dst+30)%2=0 by omega,decide_true,Bool.true_and]
  have atSite : (parentReply s p w).pc=pcAt (parentPC d j+3) := by
    rw [show (parentReply s p w).pc=s.pc+12 from call_pc ..,pc];unfold pcAt
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 12=_
    rw [←BitVec.ofNat_add];exact congrArg (BitVec.ofNat 64) (by dsimp [j];omega)
  have step:=Trunc.masked_reply_step (parentReady s p) dst w dest al (by unfold MEMORY_BYTES at lim;omega)
  have eq : execInstrBr (parentReply s p w) (.SH .x12 .x0 30)=laneReply s d p w := by
    apply step.trans
    have retained : retain (23-d.val) w=Trunc.padLow w := by unfold retain;rw [if_pos (show 0<23-d.val ∧ 23-d.val≤21 from cut)];rfl
    simp only [laneReply,retained,laneWidth,laneExtra,if_pos cut]
    change (parentReply s p (Trunc.padLow w)).setPC (s.pc+4+4+8)=_
    rw [BitVec.add_assoc,BitVec.add_assoc];rfl
  exact execute_ordinary_step _ _ _ _ _ _ (code _ atSite) (by simp only [ordinaryStep,access,↓reduceIte];exact congrArg some eq)

theorem lane_site_run {s : MachineState} {d : Fin 24} {p : Nat} (regs : ParentRegs s d p)
    (inside : p<levelCount (d.val+1)) (pc : s.pc=pcAt (parentPC d (p%16))) (fuel : Nat) :
    execute commitImage (fuel+laneWidth d) s true =
      (do let w ← hash (readBuffer s (nodeAddress d (2*p)) 96)
          let r←execute commitImage fuel (laneReply s d p w) true
          return r.charge (10+laneExtra d) 1) := by
  by_cases cut : maskedPhase d
  · simp only [laneWidth,laneExtra,if_pos cut]
    rw [show fuel+(3+1)=(fuel+1)+3 by omega,parent_site_run regs inside pc]
    apply bind_congr;intro w
    rw [clear_run regs inside pc cut]
    simp [bind_assoc,Execution.charge,←Nat.add_assoc]
  · simp only [laneWidth,laneExtra,if_neg cut,Nat.add_zero]
    rw [parent_site_run regs inside pc]
    apply bind_congr;intro w
    have retained : retain (23-d.val) w=w := if_neg cut
    have same (t : MachineState) : t.setPC t.pc=t := by cases t;rfl
    simp only [laneReply,retained,laneWidth,laneExtra,if_neg cut,Nat.add_zero]
    rw [show s.pc+BitVec.ofNat 64 (4*3)=(parentReply s p w).pc from (call_pc ..).symm,same]

end CommitGolfCandidate.Late
