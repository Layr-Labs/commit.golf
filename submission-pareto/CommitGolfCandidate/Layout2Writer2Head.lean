import CommitGolfCandidate.Layout2Writer2Code
import CommitGolfCandidate.Layout2Writer2Context
namespace CommitGolfCandidate.Layout2Writer2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase Layout2Writer
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem rd (m : MachineState) (t r : Reg) (x : Word) (nz : t≠.x0) :
    (m.setReg t x).getReg r=if t=r then x else m.getReg r := by
  by_cases eq : t=r
  · subst r;simp [MachineState.getReg_setReg_eq nz]
  · simp [eq,MachineState.getReg_setReg_ne _ _ _ _ eq]

private theorem mask (n : Nat) (small : n<2^64) : addr n &&& 3#64=addr (n%4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,show (3#64).toNat=2^2-1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n%4<2^64 by omega)]

theorem start_head {I : Image} {s p pos B l22 c} (e : Layout2Phase2.PhaseEntry s p pos B l22 c)
    (code : InstrsAt I (Layout2Phase2.bodyWord p) headOps) :
    ∃ a, RunsBlock I s a 4 ∧ a.pc=wordAddress (Layout2Phase2.bodyWord p+4) ∧ a.mem=s.mem ∧
      (∀ r, Free r → a.getReg r=s.getReg r) ∧ Core a p pos B l22 c := by
  let w:=Layout2Phase2.bodyWord p
  have small : w+4<2^40 := by dsimp [w,Layout2Phase2.bodyWord];split_ifs <;> decide
  have hpc : s.pc=wordAddress w := e.pc
  have sel := mask pos (by have:=e.index;omega)
  have scale : addr (pos%4) <<< (5:Nat)=addr (32*(pos%4)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow];change addr (pos%4)*addr 32=_
    rw [←BitVec.ofNat_mul,Nat.mul_comm]
  have loc : addr B+addr (32*(pos%4))=addr (B+32*(pos%4)) := (BitVec.ofNat_add ..).symm
  have ptr := e.pointer
  change s.getMem (addr (B+16))=addr l22 at ptr
  have eq16 : addr B+16#64=addr (B+16) := (BitVec.ofNat_add ..).symm
  have room:=e.room.2
  have width : 528≤stride p := by unfold stride;split <;> decide
  let a1:=execInstrBr s (.ANDI .x10 .x6 3)
  have mem1 : a1.mem=s.mem := rfl
  have reg1 (r : Reg) : a1.getReg r=if .x10=r then addr (pos%4) else s.getReg r := by
    cases r <;> simp [a1,execInstrBr,rd,signExtend12,MachineState.getMem,e.posReg,e.dest,sel,scale,loc,eq16] <;> first | rfl | exact ptr
  have pc1 : a1.pc=wordAddress (w+1) := by
    change s.pc+4=_
    rw [hpc,pc_next] <;> rfl
  have cd1 : (I.code[w+0]?).bind decodeInstruction=some (.base (.ANDI .x10 .x6 3)) := code ⟨0,by decide⟩
  have ok1 : memoryArgumentsValid s (.ANDI .x10 .x6 3)=true := rfl
  have run1 : RunsBlock I s a1 1 := unit s (w+0) (.ANDI .x10 .x6 3) (by omega) hpc cd1
    (by simp only [ordinaryStep,ok1,ite_true]) rfl
  let a2:=execInstrBr a1 (.SLLI .x10 .x10 5)
  have mem2 : a2.mem=s.mem := rfl
  have reg2 (r : Reg) : a2.getReg r=if .x10=r then addr (32*(pos%4)) else s.getReg r := by
    cases r <;> simp [a2,execInstrBr,rd,signExtend12,MachineState.getMem,e.posReg,e.dest,sel,scale,loc,eq16,reg1,mem1] <;> first | rfl | exact ptr
  have pc2 : a2.pc=wordAddress (w+2) := by
    change a1.pc+4=_
    rw [pc1,pc_next] <;> rfl
  have cd2 : (I.code[w+1]?).bind decodeInstruction=some (.base (.SLLI .x10 .x10 5)) := code ⟨1,by decide⟩
  have ok2 : memoryArgumentsValid a1 (.SLLI .x10 .x10 5)=true := rfl
  have run2 : RunsBlock I a1 a2 1 := unit a1 (w+1) (.SLLI .x10 .x10 5) (by omega) pc1 cd2
    (by simp only [ordinaryStep,ok2,ite_true]) rfl
  let a3:=execInstrBr a2 (.ADD .x28 .x21 .x10)
  have mem3 : a3.mem=s.mem := rfl
  have reg3 (r : Reg) : a3.getReg r=if .x28=r then addr (B+32*(pos%4)) else if .x10=r then addr (32*(pos%4)) else s.getReg r := by
    cases r <;> simp [a3,execInstrBr,rd,signExtend12,MachineState.getMem,e.posReg,e.dest,sel,scale,loc,eq16,reg2,mem2] <;> first | rfl | exact ptr
  have pc3 : a3.pc=wordAddress (w+3) := by
    change a2.pc+4=_
    rw [pc2,pc_next] <;> rfl
  have cd3 : (I.code[w+2]?).bind decodeInstruction=some (.base (.ADD .x28 .x21 .x10)) := code ⟨2,by decide⟩
  have ok3 : memoryArgumentsValid a2 (.ADD .x28 .x21 .x10)=true := rfl
  have run3 : RunsBlock I a2 a3 1 := unit a2 (w+2) (.ADD .x28 .x21 .x10) (by omega) pc2 cd3
    (by simp only [ordinaryStep,ok3,ite_true]) rfl
  let a4:=execInstrBr a3 (.LD .x7 .x21 16)
  have mem4 : a4.mem=s.mem := rfl
  have reg4 (r : Reg) : a4.getReg r=if .x7=r then addr l22 else if .x28=r then addr (B+32*(pos%4)) else if .x10=r then addr (32*(pos%4)) else s.getReg r := by
    cases r <;> simp [a4,execInstrBr,rd,signExtend12,MachineState.getMem,e.posReg,e.dest,sel,scale,loc,eq16,reg3,mem3] <;> first | rfl | exact ptr
  have pc4 : a4.pc=wordAddress (w+4) := by
    change a3.pc+4=_
    rw [pc3,pc_next] <;> rfl
  have cd4 : (I.code[w+3]?).bind decodeInstruction=some (.base (.LD .x7 .x21 16)) := code ⟨3,by decide⟩
  have ok4 : memoryArgumentsValid a3 (.LD .x7 .x21 16)=true := by
    change accessValid (a3.getReg .x21+signExtend12 16) 8=true
    rw [reg3];simp only [reduceCtorEq,ite_false,e.dest,show signExtend12 16=16#64 from rfl,eq16]
    apply access8 <;> have:=e.aligned <;> omega
  have run4 : RunsBlock I a3 a4 1 := unit a3 (w+3) (.LD .x7 .x21 16) (by omega) pc3 cd4
    (by simp only [ordinaryStep,ok4,ite_true]) rfl
  refine ⟨a4,join_run (join_run (join_run run1 run2) run3) run4,pc4,mem4,?_,
    ⟨e.index,e.aligned,e.room,e.quad,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro r free
    rcases free with ⟨_,b,d,_,f,_⟩
    simp only [reg4,if_neg b.symm,if_neg d.symm,if_neg f.symm]
  all_goals simp [reg4,e.dest,e.carry,e.heap,e.leaves,e.posReg]

end CommitGolfCandidate.Layout2Writer2
