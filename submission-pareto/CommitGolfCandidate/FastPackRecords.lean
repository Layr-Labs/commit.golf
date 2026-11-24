import CommitGolfCandidate.FastPackCore

namespace TwoPermutationPrototype.PackedOpening.Pack
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
attribute [local simp] Opening.getReg_setReg set_byte_read

abbrev w64 (n : Nat) := BitVec.ofNat 64 n
def cursor (j : Nat) := 347+2*j

private theorem suffix_op (t : Nat) (ht : t<974) : instrAt (342+t)=recordOp t := by
  have h : packPrefix = packPrefix.take 342 ++ List.ofFn (fun j : Fin 974 => recordOp j.val) := by rfl
  have len : (packPrefix.take 342).length=342 := rfl
  unfold instrAt
  have pre2 : packPrefix.length=1316 := rfl
  rw [show packCode=packPrefix ++ (StreamCopy.code true ++ StreamCopy.code false) by simp [packCode,List.append_assoc],
      List.getD_eq_getElem?_getD,List.getElem?_append_left (by rw [pre2];omega),h,List.getElem?_append_right (by rw [len]; omega),len,
      show 342+t-342=t by omega,List.getElem?_ofFn]
  simp only [ht, dite_true, Option.getD_some]

private theorem src_lt (j : Nat) (h : j<481) : laneSource j<498 := by
  unfold laneSource
  split_ifs <;> omega

private theorem positive_imm (n : Nat) (h : n<498) :
    signExtend12 (BitVec.ofNat 12 n)=w64 n := by
  exact (show ∀ i : Fin 498, signExtend12 (BitVec.ofNat 12 i.val)=w64 i.val by decide) ⟨n,h⟩

private theorem load_op (j : Nat) (h : j<481) :
    instrAt (cursor j)=.LBU .x23 (sourceReg j) (BitVec.ofNat 12 (laneSource j)) := by
  rw [show cursor j=342+(5+2*j) by unfold cursor;omega, suffix_op _ (by omega)]
  simp [recordOp,show 5+2*j<967 by omega]

private theorem store_op (j : Nat) (h : j<481) :
    instrAt (cursor j+1)=.SB .x26 .x23 (BitVec.ofNat 12 j) := by
  rw [show cursor j+1=342+(6+2*j) by unfold cursor;omega, suffix_op _ (by omega)]
  simp [recordOp,show 6+2*j<967 by omega,show 6+2*j-5=2*j+1 by omega,show ¬6+2*j<5 by omega,show (2*j+1)/2=j by omega]

structure CopyRegs (k b base r : Nat) (s : MachineState) : Prop extends PackRegs k b base s where
  x29 : s.getReg .x29=w64 (481*k)
  x30 : s.getReg .x30=w64 (base+498*r)
  x26 : s.getReg .x26=w64 (base+481*r)
  x25 : s.getReg .x25=w64 (scratch base+rounded k b+r)
  x22 : s.getReg .x22=w64 (k-r)

private def BytesAt (k base : Nat) (P : List Byte) (original : MachineState) (i : Nat)
    (s : MachineState) : Prop := ∀ a : Word, s.getByte a =
  if base≤a.toNat ∧ a.toNat<base+i then bodyByte P k (a.toNat-base) else original.getByte a

private def readAt (b k base r j : Nat) :=
  if j=45 then scratch base+rounded k b+r else base+498*r+laneSource j

private theorem source_word {s : MachineState} {k b base r j : Nat} (regs : CopyRegs k b base r s)
    (hj : j<481) : s.getReg (sourceReg j)+signExtend12 (BitVec.ofNat 12 (laneSource j)) =
      w64 (readAt b k base r j) := by
  rw [positive_imm _ (src_lt j hj)]
  by_cases h : j=45
  · subst j;simp [sourceReg,laneSource,readAt,regs.x25]
  · simp [sourceReg,readAt,h,regs.x30,w64,w_add]

private theorem read_byte {k b base r j : Nat} {s orig : MachineState} {P : List Byte}
    (hr : r<k) (hj : j<481) (fits : 498*k+30*b≤capacityBytes) (room : base+2^34≤2^36)
    (src : Unpacked k b base P orig)
    (heads : ∀ i<k, orig.getByte (w64 (scratch base+rounded k b+i))=ProofCodec.headByte P i)
    (m : BytesAt k base P orig (481*r+j) s) :
    (readAt b k base r j)<2^36 ∧
      s.getByte (w64 (readAt b k base r j))=bodyByte P k (481*r+j) := by
  have inRecord : 481*r+j<481*k := by omega
  have div : (481*r+j)/481=r := by omega
  have rem : (481*r+j)%481=j := by omega
  have origFits:=fits
  unfold capacityBytes at fits
  by_cases z : j=45
  · subst j
    have small : scratch base + rounded k b + r < 2^36 := by unfold scratch rounded count;omega
    simp only [readAt,if_true]
    refine ⟨small,?_⟩
    rw [m,toNat_w _ (by omega),if_neg (by unfold scratch;omega),heads r hr]
    simp [bodyByte,inRecord,rem,div]
  · have geom : ProofCodec.packedSource k (481*r+j)=498*r+laneSource j := by
      simp [ProofCodec.packedSource,laneSource,inRecord,div,rem,z];split_ifs <;> omega
    have bd:=packed_source_bounds k b (481*r+j) (by unfold bodyLen count;omega) (by omega)
    rw [geom] at bd
    simp only [readAt,if_neg z]
    constructor
    · omega
    · rw [m,toNat_w _ (by omega),if_neg (by omega),src]
      · simp [bodyByte,inRecord,rem,z,geom,toNat_w _ (by omega : base+498*r+laneSource j<2^64),
          show base+498*r+laneSource j-base=498*r+laneSource j by omega]
      · rw [toNat_w _ (by omega)];omega
      · rw [toNat_w _ (by omega)];omega

private theorem byte_pair {k b base r j : Nat} {s orig : MachineState} {P : List Byte}
    (hr : r<k) (hj : j<481) (fits : 498*k+30*b≤capacityBytes) (room : base+2^34≤2^36)
    (src : Unpacked k b base P orig)
    (heads : ∀ i<k, orig.getByte (w64 (scratch base+rounded k b+i))=ProofCodec.headByte P i)
    (regs : CopyRegs k b base r s) (m : BytesAt k base P orig (481*r+j) s)
    (pc : s.pc=pcOf (cursor j)) :
    ∃ z, Runs s z 2 2 ∧ CopyRegs k b base r z ∧ BytesAt k base P orig (481*r+(j+1)) z ∧
      z.pc=pcOf (cursor (j+1)) := by
  have srcAddr:=source_word regs hj
  obtain ⟨srcBound,rd⟩:=read_byte hr hj fits room src heads m
  have dest : s.getReg .x26+signExtend12 (BitVec.ofNat 12 j)=w64 (base+(481*r+j)) := by
    rw [regs.x26,positive_imm _ (by omega),w_add,Nat.add_assoc]
  have db : base+(481*r+j)<2^36 := by unfold capacityBytes at fits;omega
  let a:=cursor j
  let path:List Nat:=[a,a+1]
  have load:=load_op j hj
  have store:=store_op j hj
  have h0 : cursor j<3312 := by unfold cursor;omega
  have h1 : cursor j+1<3312 := by unfold cursor;omega
  have ok : PathOK s path := by
    simp [PathOK,path,a,load,store,pc,ordinaryInstr,execInstrBr,memoryArgumentsValid,memAccess,
      srcAddr,dest,h0,h1,accessValid_of _ (by rw [toNat_w _ (by omega)];omega : (w64 (readAt b k base r j)).toNat+1≤68719476736),
      accessValid_of _ (by rw [toNat_w _ (by omega)];omega : (w64 (base+(481*r+j))).toNat+1≤68719476736)]
  let z:=run s path
  have keep (reg : Reg) (neq : reg≠.x23) : z.getReg reg=s.getReg reg := by
    simp [z,run,path,a,load,store,execInstrBr,Ne.symm neq]
  have nextRegs : CopyRegs k b base r z := by
    constructor
    · constructor
      · exact ⟨(keep _ (by decide)).trans regs.x5,(keep _ (by decide)).trans regs.x10,
          (keep _ (by decide)).trans regs.x16,(keep _ (by decide)).trans regs.x20⟩
      all_goals rw [keep _ (by decide)];first | exact regs.x18 | exact regs.x19 | exact regs.x27 | exact regs.x28
    all_goals rw [keep _ (by decide)];first | exact regs.x29 | exact regs.x30 | exact regs.x26 | exact regs.x25 | exact regs.x22
  refine ⟨z,(runs_path path s ok).cast rfl (by simp [path,pathCycles,cost,a,load,store,instructionCycles]),nextRegs,?_,?_⟩
  · apply extend_region z s base (481*r+j) (bodyByte P k) orig.getByte (bodyByte P k (481*r+j)) (by omega) m
    · intro q
      simp [z,run,path,a,load,store,execInstrBr,srcAddr,dest,rd,setWidth_byte]
    · rfl
  · simp [z,run,path,a,load,store,execInstrBr,pc]
    <;> (congr 1 <;> unfold cursor <;> omega)

@[local simp] private theorem control_342 : instrAt 342 = .ADDI .x30 .x20 0 := rfl

@[local simp] private theorem control_343 : instrAt 343 = .ADDI .x26 .x20 0 := rfl

@[local simp] private theorem control_344 : instrAt 344 = .ADDI .x25 .x27 0 := rfl

@[local simp] private theorem control_345 : instrAt 345 = .ADDI .x22 .x16 0 := rfl

@[local simp] private theorem control_346 : instrAt 346 = .BEQ .x22 .x0 3872 := rfl

@[local simp] private theorem control_1309 : instrAt 1309 = .ADDI .x30 .x30 498 := rfl

@[local simp] private theorem control_1310 : instrAt 1310 = .ADDI .x26 .x26 481 := rfl

@[local simp] private theorem control_1311 : instrAt 1311 = .ADDI .x25 .x25 1 := rfl

@[local simp] private theorem control_1312 : instrAt 1312 = .ADDI .x22 .x22 4095 := rfl

@[local simp] private theorem control_1313 : instrAt 1313 = .BNE .x22 .x0 4328 := rfl

@[local simp] private theorem control_1314 : instrAt 1314 = .ADDI .x22 .x29 0 := rfl

@[local simp] private theorem control_1315 : instrAt 1315 = .JAL .x0 2092156 := rfl

private def entryWords : List Nat := [65,342,343,344,345,346]
private def nextWords : List Nat := [1309,1310,1311,1312,1313]
private def finalWords : List Nat := [1314,1315]

@[local simp] private theorem redirect_target : pcOf 65 + signExtend21 1108#21 = pcOf 342 := by decide
private theorem entry_target : pcOf 346 + signExtend13 3872#13 = pcOf 1314 := by decide
private theorem loop_target : pcOf 1313 + signExtend13 4328#13 = pcOf 347 := by decide
private theorem exit_target : pcOf 1315 + signExtend21 2092156#21 = pcOf 66 := by decide

private def recordPC (r k : Nat) := if r<k then pcOf 347 else pcOf 1314

private theorem enter_records {k b base : Nat} {P : List Byte} {s orig : MachineState}
    (e : RecordsEntry k b base s) (fits : 498*k+30*b≤capacityBytes)
    (m : ∀ a, s.getByte a=orig.getByte a) :
    ∃ v, Runs s v 6 6 ∧ CopyRegs k b base 0 v ∧ BytesAt k base P orig 0 v ∧ v.pc=recordPC 0 k := by
  have sm : k<2^64 := by unfold capacityBytes at fits;omega
  have ok : PathOK s entryWords := by
    simp [PathOK,entryWords,execInstrBr,e.pc,ordinaryInstr,memoryArgumentsValid,memAccess]
  let v:=run s entryWords
  have frame:=e.regs.keep entryWords (by decide)
  have young (r : Reg) (h : writesAny entryWords r=false) := run_keeps r entryWords s h
  have flag : (w64 k==0#64)=decide (k=0) := beq_ofNat k 0 sm (by decide)
  have post : CopyRegs k b base 0 v ∧ v.pc=recordPC 0 k := by
    by_cases zero:k=0
    · subst k
      refine ⟨⟨frame,(young .x29 (by decide)).trans e.x29,?_,?_,?_,?_⟩,?_⟩ <;>
        simp [v,run,entryWords,execInstrBr,e.pc,e.regs.x20,e.regs.x27,e.regs.x16,recordPC,entry_target,w64]
    · have wn : BitVec.ofNat 64 k≠0#64 := fun eq => zero ((w_inj k 0 sm (by decide)).mp eq)
      refine ⟨⟨frame,(young .x29 (by decide)).trans e.x29,?_,?_,?_,?_⟩,?_⟩ <;>
        simp [v,run,entryWords,execInstrBr,e.pc,e.regs.x20,e.regs.x27,e.regs.x16,recordPC,
          wn,zero,Nat.pos_of_ne_zero zero]
  refine ⟨v,(runs_path _ s ok).cast rfl (by decide),post.1,?_,post.2⟩
  intro a
  rw [getByte_of_mem (run_mem entryWords s (by decide)),m]
  simp

private theorem dec_remaining {k r : Nat} (hr : r<k) :
    w64 (k-r)+signExtend12 4095#12=w64 (k-(r+1)) := by
  have e : k-r=(k-(r+1))+1 := by omega
  unfold w64
  rw [e, BitVec.ofNat_add]
  change (w64 (k-(r+1))+1)+(-1)=w64 (k-(r+1))
  rw [BitVec.add_assoc, show (1 : Word) + (-1) = 0#64 by decide, BitVec.add_zero]

private theorem next_record {k b base r : Nat} {s orig : MachineState} {P : List Byte}
    (hr : r<k) (fits : 498*k+30*b≤capacityBytes)
    (regs : CopyRegs k b base r s) (m : BytesAt k base P orig (481*r+481) s)
    (pc : s.pc=pcOf 1309) :
    ∃ z, Runs s z 5 5 ∧ CopyRegs k b base (r+1) z ∧ BytesAt k base P orig (481*(r+1)) z ∧
      z.pc=recordPC (r+1) k := by
  have small : k-(r+1)<2^64 := by unfold capacityBytes at fits;omega
  have wordZero : w64 (k-(r+1)) = 0#64 ↔ ¬r+1<k := by
    rw [w_inj _ 0 small (by decide)];omega
  have ok : PathOK s nextWords := by
    simp [PathOK,nextWords,execInstrBr,pc,ordinaryInstr,memoryArgumentsValid,memAccess]
  let z:=run s nextWords
  have frame:=regs.toPackRegs.keep nextWords (by decide)
  have a : base+498*r+498=base+498*(r+1) := by omega
  have d : base+481*r+481=base+481*(r+1) := by omega
  have offset498 : signExtend12 498 = w64 498 := by decide
  have offset481 : signExtend12 481 = w64 481 := by decide
  have post : CopyRegs k b base (r+1) z ∧ z.pc=recordPC (r+1) k := by
    by_cases cont : r+1<k <;>
      refine ⟨⟨frame,(run_keeps _ _ _ (by decide)).trans regs.x29,?_,?_,?_,?_⟩,?_⟩ <;>
      simp [z,run,nextWords,execInstrBr,pc,regs.x22,regs.x30,regs.x26,regs.x25,dec_remaining hr,
        offset498,offset481,wordZero,cont,w_add,a,d,Nat.add_assoc,loop_target,recordPC]
  refine ⟨z,(runs_path _ s ok).cast rfl (by decide),post.1,?_,post.2⟩
  intro q; rw [getByte_of_mem (run_mem nextWords s (by decide)),m]
  simp [Nat.mul_add]

private theorem iterate_const {s : MachineState} (I : Nat → MachineState → Prop)
    (steps cycles N : Nat)
    (one : ∀ j<N, ∀ s, I j s → ∃ z, I (j+1) z ∧ Runs s z steps cycles)
    (init : I 0 s) : ∃ z, I N z ∧ Runs s z (steps*N) (cycles*N) := by
  obtain ⟨z,post,r⟩:=runs_loop I N (fun _=>steps) (fun _=>cycles) one N 0 s (by omega) init
  exact ⟨z,post,by simpa [Nat.mul_comm] using r⟩

theorem records_and_footer (k b base : Nat) (P : List Byte) (orig s : MachineState)
    (e : RecordsEntry k b base s)
    (src : Unpacked k b base P orig)
    (heads : ∀ r<k, orig.getByte (w64 (scratch base+rounded k b+r))=ProofCodec.headByte P r)
    (fits : 498*k+30*b≤capacityBytes) (room : base+2^34≤2^36)
    (m : ∀ a,s.getByte a=orig.getByte a) :
    ∃ z, PackBody k b base P orig (bodyLen k b) z ∧
      Runs s z (8+967*k+551*b) (8+967*k+899*b) := by
  let I:=fun r (v : MachineState) => CopyRegs k b base r v ∧ BytesAt k base P orig (481*r) v ∧ v.pc=recordPC r k
  obtain ⟨v,entered,atZero,mZero,pcZero⟩:=enter_records (P:=P) e fits m
  have start : I 0 v:=⟨atZero,by simpa using mZero,pcZero⟩
  have one (r : Nat) (hr:r<k) (v : MachineState) (inv:I r v) :
      ∃ z, I (r+1) z ∧ Runs v z 967 967 := by
    obtain ⟨regs,mem,pc⟩:=inv
    let J:=fun j (q : MachineState) => CopyRegs k b base r q ∧ BytesAt k base P orig (481*r+j) q ∧ q.pc=pcOf (cursor j)
    have init:J 0 v:=⟨regs,by simpa using mem,by simpa [recordPC,hr,cursor] using pc⟩
    have pair (j : Nat) (hj:j<481) (q : MachineState) (f:J j q) :
        ∃ z, J (j+1) z ∧ Runs q z 2 2 := by
      obtain ⟨z,ran,fr,m,pc⟩:=byte_pair hr hj fits room src heads f.1 f.2.1 f.2.2
      exact ⟨z,⟨fr,m,pc⟩,ran⟩
    obtain ⟨q,⟨fr,mq,pcq⟩,run⟩:=iterate_const J 2 2 481 pair init
    obtain ⟨z,latch,fz,mz,pcz⟩:=next_record hr fits fr mq (by simpa [cursor] using pcq)
    exact ⟨z,⟨fz,mz,pcz⟩,run.trans latch⟩
  obtain ⟨q,⟨fr,mq,pcq⟩,all⟩:=iterate_const I 967 967 k one start
  have pcend:q.pc=pcOf 1314:=by simpa [recordPC] using pcq
  have ok:PathOK q finalWords:=by simp [PathOK,finalWords,execInstrBr,pcend,ordinaryInstr,memoryArgumentsValid,memAccess]
  let u:=run q finalWords
  have length : bodyLen k b=481*k+29*b:=by unfold bodyLen count;ring
  have f : PackBody k b base P orig (481*k) u := by
    refine ⟨fr.toPackRegs.keep finalWords (by decide),(run_keeps _ _ _ (by decide)).trans fr.x29,?_,?_,by omega,?_⟩
    · simp [u,run,finalWords,execInstrBr,pcend,exit_target]
    · simp [u,run,finalWords,execInstrBr,fr.x29]
    · intro a;rw [getByte_of_mem (run_mem finalWords q (by decide)),mq]
  let J:=fun j=>PackBody k b base P orig (481*k+j)
  have foot (j : Nat) (hj:j<29*b) (q : MachineState) (g:J j q) :
      ∃ z, J (j+1) z ∧ Runs q z 19 31 := by
    obtain ⟨z,fz,rz⟩:=pack_iter k b base P orig q (481*k+j) g src heads (by omega) fits room
    exact ⟨z,by simpa [J,Nat.add_assoc] using fz,by simpa [packSteps,packCycles] using rz⟩
  obtain ⟨z,endInv,tail⟩:=iterate_const J 19 31 (29*b) foot (by simpa [J] using f)
  refine ⟨z,by simpa [J,length] using endInv,?_⟩
  exact (((entered.trans all).trans ((runs_path _ q ok).cast (s2:=2) (c2:=2) rfl (by decide))).trans tail).cast (by omega) (by omega)

end TwoPermutationPrototype.PackedOpening.Pack
