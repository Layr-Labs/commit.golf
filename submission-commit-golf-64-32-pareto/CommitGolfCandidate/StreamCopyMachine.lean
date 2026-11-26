import CommitGolfCandidate.FastPackCore

namespace TwoPermutationPrototype.PackedOpening.StreamCopy
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Pack
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
attribute [local simp] Opening.getReg_setReg set_byte_read

abbrev word (n : Nat) := BitVec.ofNat 64 n

inductive Span where | record | eight | last deriving DecidableEq

def latch (h : Bool) := origin h+4+2*width h
def start (h : Bool) : Span → Nat
 | .record => origin h+4
 | .eight => latch h+8
 | .last => latch h+28
def size (h : Bool) : Span → Nat
 | .record => width h
 | .eight => 8
 | .last => 1
def offset (h : Bool) : Span → Nat → Nat
 | .record,j => copyOff (width h) j
 | _,j => j

private theorem offsetSmall (h : Bool) (sp : Span) (j : Nat) (hj:j<size h sp) : offset h sp j<498 := by
  cases h <;> cases sp <;> simp [offset,copyOff,width,size] at hj ⊢ <;> (try split_ifs) <;> omega

private theorem span_op (h : Bool) (sp : Span) (j : Nat) (small : j<2*size h sp) :
    instrAt (start h sp+j) =
      if j%2=0 then .LBU .x23 .x30 (BitVec.ofNat 12 (offset h sp (j/2)))
      else .SB .x24 .x23 (BitVec.ofNat 12 (j/2)) := by
  let ops := fun (i : Fin (2*size h sp)) =>
    if i.val%2=0 then Instr.LBU .x23 .x30 (BitVec.ofNat 12 (offset h sp (i.val/2)))
    else .SB .x24 .x23 (BitVec.ofNat 12 (i.val/2))
  have tbl : (packCode.drop (start h sp)).take (2*size h sp) = List.ofFn ops := by
    cases h <;> cases sp <;> rfl
  have atWord := congrArg (fun xs : List Instr => xs[j]?) tbl
  simp only [List.getElem?_take, small, ite_true,List.getElem?_drop,List.getElem?_ofFn,dite_true] at atWord
  simpa only [instrAt,List.getD_eq_getElem?_getD,atWord,Option.getD_some,ops]

def Frame (a b : MachineState) : Prop :=
  ∀ r, r ∉ ([.x22,.x23,.x24,.x25,.x28,.x30] : List Reg) → b.getReg r=a.getReg r

theorem Frame.refl (a : MachineState) : Frame a a := fun _ _=>rfl
theorem Frame.thenDo {a b c : MachineState} (p : Frame a b) (q : Frame b c) : Frame a c :=
  fun r hr => (q r hr).trans (p r hr)

def Bytes (base : Nat) (f : Nat→Byte) (orig : MachineState) (n : Nat) (s : MachineState) :=
  ∀ q : Word, s.getByte q=if base≤q.toNat ∧ q.toNat<base+n then f (q.toNat-base) else orig.getByte q

theorem fixedLoop {s : MachineState} (I : Nat→MachineState→Prop) (n c : Nat)
    (one : ∀ j<n, ∀ u, I j u → ∃ v, I (j+1) v ∧ Runs u v c c) (init : I 0 s) :
    ∃ v, I n v ∧ Runs s v (c*n) (c*n) := by
  obtain ⟨v,h,r⟩:=runs_loop I n (fun _=>c) (fun _=>c) one n 0 s (by omega) init
  exact ⟨v,h,by simpa [Nat.mul_comm] using r⟩

/-- The source relation and disjointness from the written prefix are the only codec-specific facts. -/
theorem copySpan (h : Bool) (sp : Span) (base d src L : Nat) (Q : Proof) (f : Nat→Byte)
    (orig s : MachineState) (small : base+L<2^36)
    (ready : s.pc=pcOf (start h sp)) (dstReg : s.getReg .x24=word (base+d))
    (srcReg : s.getReg .x30=word (base+src)) (prior : Bytes base f orig d s)
    (source : ∀ j<L, orig.getByte (word (base+j))=Q.getD j 0)
    (layout : ∀ j<size h sp, d+j≤src+offset h sp j ∧ src+offset h sp j<L ∧
      Q.getD (src+offset h sp j) 0=f (d+j)) :
    ∃ z, Runs s z (2*size h sp) (2*size h sp) ∧ z.pc=pcOf (start h sp+2*size h sp) ∧
      (∀ r, r≠.x23 → z.getReg r=s.getReg r) ∧ Bytes base f orig (d+size h sp) z := by
  let I := fun j (u : MachineState) => u.pc=pcOf (start h sp+2*j) ∧
    (∀ r, r≠.x23 → u.getReg r=s.getReg r) ∧ Bytes base f orig (d+j) u
  have init : I 0 s:=⟨by simpa using ready,fun _ _=>rfl,by simpa using prior⟩
  have step (j : Nat) (hj:j<size h sp) (u : MachineState) (invu:I j u) :
      ∃ z, I (j+1) z ∧ Runs u z 2 2 := by
    obtain ⟨pc,regs,mem⟩:=invu
    obtain ⟨lower,upper,value⟩:=layout j hj
    let idx:=start h sp+2*j
    have ld : instrAt idx=.LBU .x23 .x30 (BitVec.ofNat 12 (offset h sp j)) := by
      simp [idx,span_op h sp (2*j) (by omega)]
    have st : instrAt (idx+1)=.SB .x24 .x23 (BitVec.ofNat 12 j) := by
      rw [show idx+1=start h sp+(2*j+1) by dsimp [idx];omega,span_op _ _ _ (by omega)]
      simp [show (2*j+1)/2=j by omega]
    have off := offsetSmall h sp j hj
    have maxSize : size h sp≤480 := by cases h <;> cases sp <;> decide
    have imm (v : Nat) (hv:v<498) : signExtend12 (BitVec.ofNat 12 v)=word v :=
      (show ∀ i : Fin 498, signExtend12 (BitVec.ofNat 12 i.val)=word i.val by decide) ⟨v,hv⟩
    have a : u.getReg .x30+signExtend12 (BitVec.ofNat 12 (offset h sp j))=word (base+(src+offset h sp j)) := by
      rw [regs _ (by decide),srcReg,imm _ off,w_add,Nat.add_assoc]
    have b : u.getReg .x24+signExtend12 (BitVec.ofNat 12 j)=word (base+(d+j)) := by
      rw [regs _ (by decide),dstReg,imm _ (by omega),w_add,Nat.add_assoc]
    have addr (z : Nat) (hz:z<L) : accessValid (word (base+z)) 1=true :=
      accessValid_of _ (by rw [toNat_w _ (by omega)];omega)
    have byte := source _ upper
    have get : u.getByte (word (base+(src+offset h sp j)))=f (d+j) := by
      rw [mem,toNat_w _ (by omega),if_neg (by omega),byte,value]
    have ix : idx+1<3312 := by cases h <;> cases sp <;> simp [idx,start,latch,size,origin,width] at hj ⊢ <;> omega
    let path:List Nat:=[idx,idx+1]
    have ok:PathOK u path := by
      simp [path,PathOK,ld,st,pc,idx,ordinaryInstr,execInstrBr,memoryArgumentsValid,memAccess,a,b,
        addr _ upper,addr _ (by omega : d+j<L),show idx<3312 by omega,ix]
    let z:=run u path
    have frame (r : Reg) (neq:r≠.x23) : z.getReg r=u.getReg r := by
      simp [z,run,path,ld,st,execInstrBr,Ne.symm neq]
    refine ⟨z,⟨?_,fun r hr => (frame r hr).trans (regs r hr),?_⟩,
      (runs_path _ u ok).cast rfl (by simp [path,pathCycles,cost,ld,st,instructionCycles])⟩
    · simp [z,run,path,ld,st,execInstrBr,pc,idx] <;> congr 1 <;> omega
    · apply extend_region z u base (d+j) f orig.getByte (f (d+j)) (by omega) mem
      · intro q;simp [z,run,path,ld,st,execInstrBr,a,b,get,setWidth_byte]
      · rfl
  obtain ⟨z,⟨pc,fr,mem⟩,ran⟩:=fixedLoop I _ 2 step init
  exact ⟨z,ran,pc,fr,mem⟩

end TwoPermutationPrototype.PackedOpening.StreamCopy
