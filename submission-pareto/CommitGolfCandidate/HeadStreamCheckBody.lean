import CommitGolfCandidate.HeadStreamCheckHeads

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStreamFive
open PackedOpening.Pack (ordinaryInstr w_add w_sub w_divu toNat_w w_inj accessValid_of setWidth_byte ult_ofNat)
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

@[simp] theorem se12_435 : signExtend12 435#12=435#64 := by decide
@[simp] theorem se12_480 : signExtend12 480#12=480#64 := by decide
@[simp] theorem body_jump : 6484#64+signExtend21 2097108#21=6440#64 := by decide
@[simp] theorem body_branch : 6456#64+signExtend13 8#13=6464#64 := by decide

structure Body (k L B : Nat) (Q : Proof) (sH : MachineState) (p : Nat) (s : MachineState) : Prop where
  regs : Regs k L B s
  pc : s.pc=pcOf 38
  counter : s.getReg .x22=BitVec.ofNat 64 p
  divisor : s.getReg .x25=480
  bound : p≤L-k
  mem : ∀ a,s.getByte a=bodyByte k L B Q sH.getByte p a

def bodyLow : List Nat := [38,39,40,41,42,44,45,46,47,48,49]
def bodyHigh : List Nat := [38,39,40,41,42,43,44,45,46,47,48,49]
def bodySteps (k p : Nat) : Nat := if (p+435)/480<k then 11 else 12
def bodyCycles (k p : Nat) : Nat := if (p+435)/480<k then 14 else 15

set_option maxHeartbeats 1000000 in
theorem body_iter (k L B p : Nat) (Q : Proof) (sH s : MachineState)
    (inv : Body k L B Q sH (p+1) s) (capacity : L≤8355061248) (records : 481*k≤L)
    (room : B+2^34≤2^36)
    (source : ∀ j<L-k,sH.getByte (BitVec.ofNat 64 (B+j))=Q.getD j 0) :
    ∃ t, Body k L B Q sH p t ∧ Hop s t (bodySteps k p) (bodyCycles k p) ∧ Reach s t := by
  have regs := inv.regs
  have hp : p<L-k := by have := inv.bound;omega
  have targetBound : compactTarget k p≤p := Nat.sub_le _ _
  have load : s.getByte (BitVec.ofNat 64 (B+p))=Q.getD p 0 := by
    rw [inv.mem,bodyByte,toNat_w _ (by omega),Nat.add_sub_cancel_left,if_neg (by omega)]
    exact source p hp
  have ne : BitVec.ofNat 64 (p+1)≠0#64 := by
    intro h
    have eq := congrArg BitVec.toNat h
    rw [toNat_w _ (by omega)] at eq
    change p+1=0 at eq
    omega
  have dec : BitVec.ofNat 64 (p+1)+signExtend12 4095#12=BitVec.ofNat 64 p := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add,toNat_w _ (by omega),toNat_w _ (by omega)]
    rw [show (signExtend12 4095#12).toNat=18446744073709551615 from by decide]
    omega
  have finish (ns : List Nat) (ok : PathOK s ns)
      (bounded : ns.all (fun n => decide (n<75))=true)
      (kept : ([.x15,.x16,.x17,.x18,.x19,.x20] : List Reg).all
        (fun r => ns.all (fun n => !(writes (instrAt n) r)))=true)
      (pc : (run s ns).pc=pcOf 38) (counter : (run s ns).getReg .x22=BitVec.ofNat 64 p)
      (divisor : (run s ns).getReg .x25=480)
      (mem : ∀ a,(run s ns).getByte a=
        if a=BitVec.ofNat 64 (B+compactSource k p) then Q.getD p 0 else s.getByte a) :
      Body k L B Q sH p (run s ns) := by
    refine ⟨regs.keep ns bounded kept,pc,counter,divisor,by omega,?_⟩
    intro a
    rw [mem,inv.mem]
    exact body_step k L B p Q sH.getByte a records hp (by omega)
  by_cases low : (p+435)/480<k
  · have src : compactSource k p=(p+435)/480+p := by
      unfold compactSource;rw [Nat.min_eq_right (by omega)];omega
    have ok : PathOK s bodyLow := by
      simp (disch := omega) [PathOK,bodyLow,execInstrBr,inv.pc,inv.counter,inv.divisor,
        regs.x15,regs.x16,ne,dec,ordinaryInstr,memoryArgumentsValid,memAccess,
        w_add,w_divu,ult_ofNat,low,pcOf]
      constructor <;> apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
    have pc : (run s bodyLow).pc=pcOf 38 := by
      simp (disch := omega) [run,bodyLow,execInstrBr,inv.pc,inv.counter,inv.divisor,
        regs.x16,ne,dec,w_add,w_divu,ult_ofNat,low,pcOf]
    have counter : (run s bodyLow).getReg .x22=BitVec.ofNat 64 p := by
      simp (disch := omega) [run,bodyLow,execInstrBr,inv.counter,inv.divisor,regs.x16,
        ne,dec,w_add,w_divu,ult_ofNat,low]
    have divisor : (run s bodyLow).getReg .x25=480 :=
      (keep_path s bodyLow .x25 (by decide) (by decide)).trans inv.divisor
    have mem : ∀ a,(run s bodyLow).getByte a=
        if a=BitVec.ofNat 64 (B+compactSource k p) then Q.getD p 0 else s.getByte a := by
      intro a
      simpa (disch := omega) [run,bodyLow,execInstrBr,inv.counter,inv.divisor,regs.x15,regs.x16,
        ne,dec,w_add,w_divu,ult_ofNat,low,←src,load,setWidth_byte,Nat.add_assoc] using
        (set_byte_read s (BitVec.ofNat 64 (B+compactSource k p)) a (Q.getD p 0))
    exact ⟨_,finish bodyLow ok (by decide) (by decide) pc counter divisor mem,
      (runs_path s bodyLow ok).cast (by simp [bodySteps,low,bodyLow]) (by simp [bodyCycles,low];decide),
      reach_path s bodyLow ok⟩
  · have src : compactSource k p=k+p := by
      unfold compactSource;rw [Nat.min_eq_left (by omega)];omega
    have ok : PathOK s bodyHigh := by
      simp (disch := omega) [PathOK,bodyHigh,execInstrBr,inv.pc,inv.counter,inv.divisor,
        regs.x15,regs.x16,ne,dec,ordinaryInstr,memoryArgumentsValid,memAccess,
        w_add,w_divu,ult_ofNat,low,pcOf]
      constructor <;> apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
    have pc : (run s bodyHigh).pc=pcOf 38 := by
      simp (disch := omega) [run,bodyHigh,execInstrBr,inv.pc,inv.counter,inv.divisor,
        regs.x16,ne,dec,w_add,w_divu,ult_ofNat,low,pcOf]
    have counter : (run s bodyHigh).getReg .x22=BitVec.ofNat 64 p := by
      simp (disch := omega) [run,bodyHigh,execInstrBr,inv.counter,inv.divisor,regs.x16,
        ne,dec,w_add,w_divu,ult_ofNat,low]
    have divisor : (run s bodyHigh).getReg .x25=480 :=
      (keep_path s bodyHigh .x25 (by decide) (by decide)).trans inv.divisor
    have mem : ∀ a,(run s bodyHigh).getByte a=
        if a=BitVec.ofNat 64 (B+compactSource k p) then Q.getD p 0 else s.getByte a := by
      intro a
      simpa (disch := omega) [run,bodyHigh,execInstrBr,inv.counter,inv.divisor,regs.x15,regs.x16,
        ne,dec,w_add,w_divu,ult_ofNat,low,←src,load,setWidth_byte,Nat.add_assoc] using
        (set_byte_read s (BitVec.ofNat 64 (B+compactSource k p)) a (Q.getD p 0))
    exact ⟨_,finish bodyHigh ok (by decide) (by decide) pc counter divisor mem,
      (runs_path s bodyHigh ok).cast (by simp [bodySteps,low,bodyHigh]) (by simp [bodyCycles,low];decide),
      reach_path s bodyHigh ok⟩

end TwoPermutationPrototype.Packed.Checker.HeadRestore
