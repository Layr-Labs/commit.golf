import CommitGolfCandidate.HeadStreamCheckMemory

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStreamFive
open PackedOpening.Pack (ordinaryInstr w_add w_sub w_mul w_divu w_shl w_shr toNat_w w_inj accessValid_of setWidth_byte)
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

@[simp] theorem se12_5 : signExtend12 5#12=5#64 := by decide
@[simp] theorem se12_256 : signExtend12 256#12=256#64 := by decide
@[simp] theorem se12_31 : signExtend12 31#12=31#64 := by decide
@[simp] theorem head_jump : 6428#64+signExtend21 2097084#21=6360#64 := by decide

structure Regs (k L B : Nat) (s : MachineState) : Prop where
  x15 : s.getReg .x15=BitVec.ofNat 64 B
  x16 : s.getReg .x16=BitVec.ofNat 64 k
  x17 : s.getReg .x17=BitVec.ofNat 64 L
  x18 : s.getReg .x18=BitVec.ofNat 64 (L-k)
  x19 : s.getReg .x19=BitVec.ofNat 64 (B+2^33)
  x20 : s.getReg .x20=BitVec.ofNat 64 (B+(L-k))

theorem Regs.keep {k L B : Nat} {s : MachineState} (regs : Regs k L B s) (ns : List Nat)
    (bounded : ns.all (fun n => decide (n<75))=true)
    (kept : ([.x15,.x16,.x17,.x18,.x19,.x20] : List Reg).all
      (fun r => ns.all (fun n => !(writes (instrAt n) r)))=true) : Regs k L B (run s ns) := by
  have bounds : ∀ n∈ns,n<75 := by simpa only [List.all_eq_true,decide_eq_true_eq] using bounded
  simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at kept
  obtain ⟨h15,h16,h17,h18,h19,h20⟩ := kept
  exact ⟨(keep_path _ _ _ bounds h15).trans regs.x15,(keep_path _ _ _ bounds h16).trans regs.x16,
    (keep_path _ _ _ bounds h17).trans regs.x17,(keep_path _ _ _ bounds h18).trans regs.x18,
    (keep_path _ _ _ bounds h19).trans regs.x19,(keep_path _ _ _ bounds h20).trans regs.x20⟩

structure Heads (k L B : Nat) (Q : Proof) (s0 : MachineState) (r : Nat) (s : MachineState) : Prop where
  regs : Regs k L B s
  pc : s.pc=pcOf 18
  counter : s.getReg .x22=BitVec.ofNat 64 r
  bound : r≤k
  mem : ∀ a, s.getByte a=prefixByte (B+2^33) r (fun j => BitVec.ofNat 8 (restoredHead k Q j)) s0.getByte a

def headPath : List Nat := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]

theorem byte_wide (b : Byte) : b.setWidth 64=BitVec.ofNat 64 b.toNat := by
  rw [BitVec.ofNat_toNat]

set_option maxHeartbeats 1000000 in
theorem head_iter (k L B r : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L B Q s0 r s) (len : Q.length+3*k/8=L)
    (kb : k≤2^24) (capacity : L≤8355061248) (records : 481*k≤L)
    (room : B+2^34≤2^36) (inside : r<k)
    (source : ∀ j<2^34,s0.getByte (BitVec.ofNat 64 (B+j))=Q.getD j 0) :
    ∃ t, Heads k L B Q s0 (r+1) t ∧ Hop s t 18 24 ∧ Reach s t := by
  have regs := inv.regs
  let p := L-k+5*r/8
  have pb : p+1<2^33 := by dsimp [p];omega
  have ne : BitVec.ofNat 64 r≠BitVec.ofNat 64 k := by
    rw [Ne,w_inj _ _ (by omega) (by omega)];omega
  have five : r*5=5*r := by omega
  have shift : BitVec.ofNat 64 (5*r) &&& 7#64=BitVec.ofNat 64 (5*r%8) := by
    rw [show 7#64=BitVec.ofNat 64 (2^3-1) from rfl,and_mask _ 3 (by decide),toNat_w _ (by omega)]
    rfl
  have sn : (BitVec.ofNat 64 (5*r%8)).toNat%64=5*r%8 := by
    rw [toNat_w _ (by omega)]
    omega
  have shiftNat : ((5*r)%18446744073709551616 &&& 7)%64=5*r%8 := by
    rw [Nat.mod_eq_of_lt (show 5*r<18446744073709551616 by omega),
      show (7 : Nat)=2^3-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
    omega
  have shift64 : (5*r%8)%64=5*r%8 := Nat.mod_eq_of_lt (by omega)
  have load (j : Nat) (hj : j<2^33) : s.getByte (BitVec.ofNat 64 (B+j))=Q.getD j 0 := by
    rw [inv.mem,prefixByte,toNat_w _ (by omega),if_neg (by omega)]
    exact source j (by omega)
  have data :
      (((Q.getD p 0).setWidth 64 >>> (5*r%8)) |||
        ((Q.getD (p+1) 0).setWidth 64 * (256#64 >>> (5*r%8)))) &&& 31#64=
      BitVec.ofNat 64 (restoredHead k Q r) := by
    rw [byte_wide,byte_wide,header_word _ _ _ (by omega)]
    congr 1
    unfold restoredHead frontLength expandedLength
    rw [len]
  have dataByte := congrArg (fun w : Word => w.setWidth 8) data
  simp (disch := omega) [p,Nat.add_assoc,w_shr,shift64] at dataByte
  have ok : PathOK s headPath := by
    simp (disch := omega) [PathOK,headPath,execInstrBr,inv.pc,inv.counter,regs.x15,regs.x16,regs.x17,
      regs.x18,regs.x19,regs.x20,ne,ordinaryInstr,memoryArgumentsValid,memAccess,
      w_add,w_sub,w_mul,w_shl,w_shr,five,shift,sn,Nat.add_assoc,pcOf]
    repeat' constructor
    all_goals apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
  have nextpc : (run s headPath).pc=pcOf 18 := by
    simp (disch := omega) [run,headPath,execInstrBr,inv.pc,inv.counter,regs.x16,ne,pcOf]
  have next : (run s headPath).getReg .x22=BitVec.ofNat 64 (r+1) := by
    simp (disch := omega) [run,headPath,execInstrBr,inv.counter,regs.x16,ne,w_add]
  have mem : ∀ a, (run s headPath).getByte a=
      if a=BitVec.ofNat 64 (B+2^33+r) then BitVec.ofNat 8 (restoredHead k Q r) else s.getByte a := by
    intro a
    simpa (disch := omega) [run,headPath,execInstrBr,inv.counter,regs.x15,regs.x16,regs.x17,
      regs.x18,regs.x19,regs.x20,ne,w_add,w_sub,w_mul,w_shl,w_shr,five,shift,sn,
      Nat.add_assoc,shiftNat,shift64,load,dataByte,setWidth_byte] using
        (set_byte_read s (BitVec.ofNat 64 (B+2^33+r)) a (BitVec.ofNat 8 (restoredHead k Q r)))
  refine ⟨run s headPath,⟨regs.keep headPath (by decide) (by decide),nextpc,next,by omega,?_⟩,
    (runs_path s headPath ok).cast rfl (by decide),reach_path s headPath ok⟩
  intro a
  rw [mem,inv.mem]
  exact prefix_step _ _ _ _ _ (by omega)

end TwoPermutationPrototype.Packed.Checker.HeadRestore
