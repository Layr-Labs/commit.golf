import CommitGolfCandidate.TailStreamCheckInsertMemory

namespace TwoPermutationPrototype.Packed.Checker.TailRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStreamSeven
open PackedOpening.Pack (ordinaryInstr w_add toNat_w w_inj accessValid_of setWidth_byte)
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

@[simp] theorem se12_481 : signExtend12 480#12=480#64 := by decide
@[simp] theorem insert_jump : 6836#64+signExtend21 2097124#21=6808#64 := by decide

structure Insert (k L B : Nat) (Q : Proof) (sB : MachineState) (r : Nat) (s : MachineState) : Prop where
  regs : Regs k L B s
  pc : s.pc=pcOf 52
  counter : s.getReg .x22=BitVec.ofNat 64 r
  cursor : s.getReg .x21=BitVec.ofNat 64 (B+480*r+44)
  bound : r≤k
  mem : ∀ a,s.getByte a=insertByte k B Q sB.getByte r a

def insertPath : List Nat := [52,53,54,55,56,57,58,59]

set_option maxHeartbeats 1000000 in
theorem insert_iter (k L B r : Nat) (Q : Proof) (sB s : MachineState)
    (inv : Insert k L B Q sB r s) (capacity : L≤8355061248) (records : 480*k≤L)
    (room : B+2^34≤2^36) (inside : r<k)
    (source : ∀ j<k,sB.getByte (BitVec.ofNat 64 (B+2^33+j))=BitVec.ofNat 8 (restoredHead k Q j)) :
    ∃ t, Insert k L B Q sB (r+1) t ∧ Hop s t 8 8 ∧ Reach s t := by
  have regs := inv.regs
  have ne : BitVec.ofNat 64 r≠BitVec.ofNat 64 k := by
    rw [Ne,w_inj _ _ (by omega) (by omega)];omega
  have load : s.getByte (BitVec.ofNat 64 (B+2^33+r))=BitVec.ofNat 8 (restoredHead k Q r) := by
    rw [inv.mem,insertByte,prefixByte,toNat_w _ (by omega),if_neg (by omega)]
    rw [installedByte,toNat_w _ (by omega),if_neg (by omega)]
    exact source r inside
  have load' : s.getByte (BitVec.ofNat 64 (B+(8589934592+r)))=BitVec.ofNat 8 (restoredHead k Q r) := by
    simpa only [Nat.add_assoc,Nat.reducePow] using load
  have ok : PathOK s insertPath := by
    simp (disch := omega) [PathOK,insertPath,execInstrBr,inv.pc,inv.counter,inv.cursor,regs.x16,regs.x19,
      ne,ordinaryInstr,memoryArgumentsValid,memAccess,w_add,Nat.add_assoc,pcOf]
    repeat' constructor
    all_goals apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
  have pc : (run s insertPath).pc=pcOf 52 := by
    simp [run,insertPath,execInstrBr,inv.pc,inv.counter,regs.x16,ne,pcOf]
  have counter : (run s insertPath).getReg .x22=BitVec.ofNat 64 (r+1) := by
    simp [run,insertPath,execInstrBr,inv.counter,regs.x16,ne,w_add]
  have cursor : (run s insertPath).getReg .x21=BitVec.ofNat 64 (B+480*(r+1)+44) := by
    simp [run,insertPath,execInstrBr,inv.counter,inv.cursor,regs.x16,ne,w_add]
    apply congrArg (BitVec.ofNat 64)
    omega
  have mem : ∀ a,(run s insertPath).getByte a=
      if a=BitVec.ofNat 64 (B+2^33+r) then 0 else
        if a=BitVec.ofNat 64 (B+480*r+44) then BitVec.ofNat 8 (restoredHead k Q r) else s.getByte a := by
    intro a
    simpa [run,insertPath,execInstrBr,inv.counter,inv.cursor,regs.x16,regs.x19,ne,w_add,
      Nat.add_assoc,load',setWidth_byte] using
      (set_byte_read (s.setByte (BitVec.ofNat 64 (B+480*r+44)) (BitVec.ofNat 8 (restoredHead k Q r)))
        (BitVec.ofNat 64 (B+2^33+r)) a 0)
  refine ⟨_,⟨regs.keep insertPath (by decide) (by decide),pc,counter,cursor,by omega,?_⟩,
    (runs_path s insertPath ok).cast rfl (by decide),reach_path s insertPath ok⟩
  intro a
  rw [mem,inv.mem]
  exact insert_step k B r Q sB.getByte a inside (by omega) (by omega)

theorem insert_count (k L B n r : Nat) (Q : Proof) (sB s : MachineState)
    (inv : Insert k L B Q sB r s) (count : r+n=k)
    (capacity : L≤8355061248) (records : 480*k≤L) (room : B+2^34≤2^36)
    (source : ∀ j<k,sB.getByte (BitVec.ofNat 64 (B+2^33+j))=BitVec.ofNat 8 (restoredHead k Q j)) :
    ∃ t,Insert k L B Q sB k t ∧ Hop s t (8*n) (8*n) ∧ Reach s t := by
  induction n generalizing r s with
  | zero =>
    have eq : r=k := by omega
    subst r
    exact ⟨s,inv,Hop.refl s,Reach.refl s⟩
  | succ n ih =>
    obtain ⟨t,inv',hop,reach⟩ := insert_iter k L B r Q sB s inv capacity records room (by omega) source
    obtain ⟨u,inv'',hop',reach'⟩ := ih (r+1) t inv' (by omega)
    exact ⟨u,inv'',(hop.thenDo hop').cast (by omega) (by omega),reach.trans reach'⟩

end TwoPermutationPrototype.Packed.Checker.TailRestore
