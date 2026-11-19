import CommitGolfCandidate.HeadStreamCheckFinalMemory

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStreamZero
open PackedOpening.Pack (ordinaryInstr toNat_w)
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

theorem insert_initial (k B : Nat) (Q : Proof) (g : Word → Byte) (a : Word) : insertByte k B Q g 0 a=g a := by
  rw [insertByte,prefix_zero,installedByte,if_neg (by omega),if_neg (by omega)]

def insertEnter : List Nat := [38,50,51]
@[simp] theorem body_done_branch : 6440#64+signExtend13 48#13=6488#64 := by decide
@[simp] theorem se12_45 : signExtend12 45#12=45#64 := by decide

theorem body_to_insert (k L B : Nat) (Q : Proof) (sH s : MachineState)
    (inv : Body k L B Q sH 0 s) :
    Insert k L B Q s 0 (run s insertEnter) ∧ Hop s (run s insertEnter) 3 3 ∧ Reach s (run s insertEnter) := by
  have regs := inv.regs
  have ok : PathOK s insertEnter := by
    simp [PathOK,insertEnter,execInstrBr,inv.pc,inv.counter,ordinaryInstr,memoryArgumentsValid,memAccess,pcOf]
  refine ⟨⟨regs.keep insertEnter (by decide) (by decide),?_,?_,?_,by omega,?_⟩,
    (runs_path s insertEnter ok).cast rfl (by decide),reach_path s insertEnter ok⟩
  · simp [run,insertEnter,execInstrBr,inv.pc,inv.counter,pcOf]
  · simp [run,insertEnter,execInstrBr,inv.counter]
  · simp [run,insertEnter,execInstrBr,inv.counter,regs.x15,PackedOpening.Pack.w_add]
  · intro a
    rw [insert_initial]
    simp [run,insertEnter,execInstrBr,inv.counter]

def cleanupPath : List Nat := [52,63,64,65,66,67,68,69,70,71,72,73,74,75,76]
def restoredTemps : List Reg := [.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30,.x31]
@[simp] theorem insert_done_branch : 6496#64+signExtend13 44#13=6540#64 := by decide

set_option maxHeartbeats 1000000 in
theorem cleanup_run (k L B : Nat) (Q : Proof) (sB s : MachineState) (inv : Insert k L B Q sB k s) :
    (run s cleanupPath).pc=pcOf 77 ∧
      (∀ r∈restoredTemps,(run s cleanupPath).getReg r=0) ∧
      (∀ r,r∉restoredTemps → (run s cleanupPath).getReg r=s.getReg r) ∧
      (∀ a,(run s cleanupPath).getByte a=s.getByte a) ∧
      Hop s (run s cleanupPath) 15 15 ∧ Reach s (run s cleanupPath) := by
  have regs := inv.regs
  have ok : PathOK s cleanupPath := by
    simp [PathOK,cleanupPath,execInstrBr,inv.pc,inv.counter,regs.x16,ordinaryInstr,memoryArgumentsValid,memAccess,pcOf]
  refine ⟨?_,?_,?_,?_,(runs_path s cleanupPath ok).cast rfl (by decide),reach_path s cleanupPath ok⟩
  · simp [run,cleanupPath,execInstrBr,inv.pc,inv.counter,regs.x16,pcOf]
  · have all : restoredTemps.all (fun r => decide ((run s cleanupPath).getReg r=0))=true := by
      simp [restoredTemps,run,cleanupPath,execInstrBr,inv.counter,regs.x16]
    intro r hr
    exact of_decide_eq_true (List.all_eq_true.mp all r hr)
  · intro r hr
    apply keep_path s cleanupPath r (by decide)
    cases r <;> simp_all [restoredTemps,cleanupPath,writes]
  · intro a
    simp [run,cleanupPath,execInstrBr,inv.counter,regs.x16]

theorem Heads.read_front (k L B n : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L B Q s0 k s) (small : n<2^33) (room : B+2^34≤2^36)
    (source : ∀ j<2^34,s0.getByte (BitVec.ofNat 64 (B+j))=Q.getD j 0) :
    s.getByte (BitVec.ofNat 64 (B+n))=Q.getD n 0 := by
  rw [inv.mem,prefixByte,toNat_w _ (by omega),if_neg (by omega)]
  exact source n (by omega)

theorem Heads.read_scratch (k L B n : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L B Q s0 k s) (small : k≤2^24) (hn : n<k) (room : B+2^34≤2^36) :
    s.getByte (BitVec.ofNat 64 (B+2^33+n))=BitVec.ofNat 8 (restoredHead k Q n) := by
  rw [inv.mem,prefixByte,toNat_w _ (by omega),if_pos (by omega),Nat.add_sub_cancel_left]

theorem Body.read_scratch (k L B n : Nat) (Q : Proof) (sH s : MachineState)
    (inv : Body k L B Q sH 0 s) (small : n<2^24) (capacity : L≤8355061248) (room : B+2^34≤2^36) :
    s.getByte (BitVec.ofNat 64 (B+2^33+n))=sH.getByte (BitVec.ofNat 64 (B+2^33+n)) := by
  rw [inv.mem,bodyByte,toNat_w _ (by omega),if_neg (by omega)]

end TwoPermutationPrototype.Packed.Checker.HeadRestore
