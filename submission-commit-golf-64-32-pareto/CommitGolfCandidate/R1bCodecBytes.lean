import CommitGolfCandidate.R1bCodecFields
namespace CommitGolfCandidate.R1b.Codec
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Carry (group pieces carrier prev)
open R1bPC (pcAt pc_succ)
structure ByteState (d : Bool) (s t : MachineState) (k : Nat) extends Common d s t k (group k 0) : Prop where
  pc : t.pc=pcAt (bytePC d k)

private theorem nonempty (k : Nat) : 0<pieces k:=by unfold pieces;split <;> decide
private theorem byteBound (d : Bool) (k : Nat) (hk : k<352) : bytePC d k<(program d).count := by
  exact (show ∀ b : Bool,∀ n : Fin 352,bytePC b n.val<(program b).count by decide) d ⟨k,hk⟩

theorem initByte (law : CodeLaw) (d : Bool) (s t : MachineState) (k : Nat) (hk : k<352) (st : ByteState d s t k) :
    ∃ u,Fields d s u k 0 ∧ Runs (program d) t u 1 1 := by
  let op:=(beginByte d k).instr
  let u:=execInstrBr t op
  have code:=stood (law d k hk).1
  have a : t.getReg .x22+signExtend12 (BitVec.ofNat 12 k)=W (proofBase+67488+k):=by
    rw [st.tail,immediate _ (by omega),←BitVec.ofNat_add]
  have access : accessValid (t.getReg .x22+signExtend12 (BitVec.ofNat 12 k)) 1=true:=by
    rw [a];apply Safe.valid;exact ⟨by unfold proofBase MEMORY_BYTES;omega,Nat.mod_one _⟩
  have oneRun : Runs (program d) t u 1 1:=by
    cases d
    · have ok : memoryArgumentsValid t (.LBU .x7 .x22 (BitVec.ofNat 12 k))=true:=access
      exact one (byteBound _ k hk) st.pc _ code (by simp only [beginByte,Bool.false_eq_true,ite_false,Sym.Calc.instr,ordinaryStep,if_pos ok];rfl)
    · exact one (byteBound _ k hk) st.pc _ code rfl
  have mem : u.mem=t.mem:=by cases d <;> rfl
  have keep (r : Reg) (h : r≠.x7 ∧ r≠.x8) : u.getReg r=t.getReg r:=by
    cases d
    · exact MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.1.symm)
    · exact MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.2.symm)
  refine ⟨u,⟨⟨st.memory.still mem,(keep _ (by decide)).trans st.ptr,(keep _ (by decide)).trans st.tail,?_⟩,?_,?_,?_⟩,oneRun⟩
  · intro r hr;have e:=hr.1;unfold controlReg at e;simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at e
    exact (keep _ e.2.2).trans (st.keep r hr)
  · have loc : lanePC d k 0=bytePC d k+1:=by rw [lanePC,if_pos (nonempty k)];cases d <;> rfl
    rw [loc,pc_succ,←st.pc];cases d <;> rfl
  · intro enc _;subst d
    change (t.getByte (t.getReg .x22+signExtend12 (BitVec.ofNat 12 k))).zeroExtend 64=_
    rw [a,Nat.add_assoc proofBase 67488 k];change (byte t (proofBase+(67488+k))).zeroExtend 64=_ 
    rw [st.memory.atByte _ (by omega),Carry.readTail];rfl
  · intro dec;subst d;rfl

theorem endOfByte (law : CodeLaw) (d : Bool) (s t : MachineState) (k : Nat) (hk : k<352) (st : Fields d s t k (pieces k)) :
    ∃ u,ByteState d s u (k+1) ∧ Runs (program d) t u (if d then 1 else 0) (if d then 1 else 0) := by
  have done := Carry.group_next k
  have ip:=st.pc;rw [lanePC,if_neg (Nat.lt_irrefl _)] at ip
  have pbound : bytePC true (k+1)≤Code.check.count ∧ 0<bytePC true (k+1):=
    (show ∀ j : Fin 352,bytePC true (j.val+1)≤Code.check.count ∧ 0<bytePC true (j.val+1) by decide) ⟨k,hk⟩
  cases d with
  | false=>
    exact ⟨t,⟨⟨done ▸ st.memory.encByte,done ▸ st.ptr,st.tail,st.keep⟩,by simpa only [Bool.false_eq_true,ite_false,Nat.sub_zero] using ip⟩,Runs.refl _ _⟩
  | true=>
    let a:=proofBase+67488+k
    let n:=bytePC true (k+1)-1
    let op:=endByte k
    let u:=execInstrBr t op
    have addr : t.getReg .x22+signExtend12 (BitVec.ofNat 12 k)=W a:=by rw [st.tail,immediate _ (by omega),←BitVec.ofNat_add]
    obtain ⟨run,atEnd,reg,write⟩:=flagRun (c:=.check) (n:=n) (by dsimp only [n];omega) ip (stood ((law true k hk).2.1 rfl)) addr (by dsimp [a,proofBase,MEMORY_BYTES];omega)
    have value : (t.getReg .x8).truncate 8=Carry.restored (original s) k:=by
      rw [st.dec rfl,Carry.assembled];exact BitVec.setWidth_setWidth_of_le _ (by decide)
    have effect : Wrote t u a 1 (fun _=>Carry.restored (original s) k):=by intro q b;simpa only [u,op,endByte,value] using write q b
    exact ⟨u,⟨⟨done ▸ st.memory.doneByte hk effect,done ▸ (reg .x21).trans st.ptr,(reg .x22).trans st.tail,
      fun r hr=>(reg r).trans (st.keep r hr)⟩,atEnd.trans (congrArg pcAt (by dsimp only [n];omega))⟩,run⟩

theorem oneByte (law : CodeLaw) (d : Bool) (s t : MachineState) (k : Nat) (hk : k<352) (st : ByteState d s t k) :
    ∃ u,ByteState d s u (k+1) ∧ Runs (program d) t u (bytePC d (k+1)-bytePC d k) (bytePC d (k+1)-bytePC d k) := by
  obtain ⟨v,s0,init⟩:=initByte law d s t k hk st
  obtain ⟨w,s1,middle⟩:=fieldLine law d s v k (pieces k) hk le_rfl s0
  obtain ⟨u,e,last⟩:=endOfByte law d s w k hk s1
  have count : 1+(lanePC d k (pieces k)-lanePC d k 0)+(if d then 1 else 0)=bytePC d (k+1)-bytePC d k:=
    (show ∀ b : Bool,∀ j : Fin 352,1+(lanePC b j (pieces j)-lanePC b j 0)+(if b then 1 else 0)=bytePC b (j.val+1)-bytePC b j by decide) d ⟨k,hk⟩
  exact ⟨u,e,by simpa only [count] using (init.trans middle).trans last⟩
theorem manyBytes (law : CodeLaw) (d : Bool) (s t : MachineState) (k : Nat) (hk : k≤352) (st : ByteState d s t 0) :
    ∃ u,ByteState d s u k ∧ Runs (program d) t u (bytePC d k-bytePC d 0) (bytePC d k-bytePC d 0) := by
  induction k with
  | zero=>exact ⟨t,st,by rw [Nat.sub_self];exact Runs.refl _ _⟩
  | succ k ih=>
    obtain ⟨u,mid,before⟩:=ih (by omega)
    obtain ⟨w,last,path⟩:=oneByte law d s u k (by omega) mid
    have lo : bytePC d 0≤bytePC d k ∧ bytePC d k≤bytePC d (k+1):=
      (show ∀ b : Bool,∀ j : Fin 352,bytePC b 0≤bytePC b j ∧ bytePC b j≤bytePC b (j.val+1) by decide) d ⟨k,by omega⟩
    have m : bytePC d k-bytePC d 0+(bytePC d (k+1)-bytePC d k)=bytePC d (k+1)-bytePC d 0:=by omega
    exact ⟨w,last,by simpa only [m] using before.trans path⟩
end CommitGolfCandidate.R1b.Codec
