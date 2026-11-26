import CommitGolfCandidate.R1bCodecPrefix
namespace CommitGolfCandidate.R1b.Codec
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Carry (group carrier prev pieces)
open R1bPC (pcAt pc_succ)

structure PieceResult (d : Bool) (s t : MachineState) (k p a : Nat) : Prop where
  run : Runs (program d) s t (sequence d k p).length (sequence d k p).length
  pc : t.pc=pcAt (nextPiece d k p)
  write : Wrote s t a 1 (fun _=>(loadedField d (byte s a) (s.getReg .x7)).truncate 8)
  ptr : t.getReg .x21=W a
  shifted : d=false →
    t.getReg .x7=if p+1<pieces k then s.getReg .x7 >>> 2 else s.getReg .x7
  combined : d=true → t.getReg .x8=s.getReg .x8 ||| (highWord (byte s a) <<< (2*p))
  keep : ∀ r,controlReg r → t.getReg r=s.getReg r

theorem runPieceAt (d : Bool) (s : MachineState) (base k p : Nat) (hk : k<352) (hp : p<pieces k)
    (pc : s.pc=pcAt (piecePC d k p)) (ptr : s.getReg .x21=W (base+Carry.prev (group k p)))
    (room : base+67840≤MEMORY_BYTES)
    (enc : Matches (program d) (piecePC d k p) (sequence d k p)) :
    ∃ t,PieceResult d s t k p (base+carrier (group k p)) := by
  let prog:=program d
  let a:=base+carrier (group k p)
  let ip:=piecePC d k p
  let endOps:=suffixOps d k p
  have p4 : p<4:=by unfold pieces at hp;split at hp <;> omega
  have ci:=(Carry.groupSpec k p hk hp).1
  have word : Matches prog ip (((prefixOps d k p).map Sym.Calc.instr)++(.SB .x21 .x6 0::endOps.map Sym.Calc.instr)):=by
    simpa only [sequence,List.append_assoc,List.singleton_append] using enc
  have sz : (sequence d k p).length=preLen d+1+endOps.length := by
    simp only [sequence,List.length_append,List.length_singleton,List.length_map]
    have preSize : (prefixOps d k p).length=preLen d:=by cases d <;> rfl
    rw [preSize]
  obtain ⟨last,bound⟩:=price d k p hk hp
  rw [sz] at bound last
  have space : ip+preLen d≤prog.count:=by dsimp [ip,prog];omega
  obtain ⟨u,pre⟩:=runPrefix d prog s ip base (group k p) ci pc space word.left ptr (by omega)
  have preWords : ((prefixOps d k p).map Sym.Calc.instr).length=preLen d:=by cases d <;> rfl
  have rem:=word.right
  rw [preWords] at rem
  have ba : a+1≤MEMORY_BYTES:=by dsimp only [a];have:=(Carry.location _ ci).2;omega
  have ad : u.getReg .x21+signExtend12 0=W a:=by rw [pre.addr];exact BitVec.add_zero _
  obtain ⟨storeRun,afterPC,regStore,wrote⟩:=flagRun (c:=prog) (by change ip+preLen d<(program d).count;dsimp [ip];omega) pre.pc rem.head ad ba
  let v:=execInstrBr u (.SB .x21 .x6 0)
  let z:=Sym.evaluated endOps v
  have small : ip+preLen d+1+endOps.length≤prog.count:=by dsimp only [ip,prog];omega
  have nr : endOps.all (fun op=>op.dst != .x0)=true:=by
    dsimp [endOps,suffixOps,after];split <;> split <;> rfl
  have reads : Sym.requirements Sym.original endOps=[]:=by dsimp [endOps,suffixOps,after];split <;> split <;> rfl
  obtain ⟨finish,regs,mem,endPC⟩:=calcRegs prog v endOps (ip+preLen d+1) afterPC small rem.tail nr reads
  have cost : Sym.price endOps=endOps.length:=by dsimp [endOps,suffixOps,after];split <;> split <;> rfl
  rw [cost] at finish
  have writers : registersPreserved endOps [.x7,.x8]:=by dsimp [endOps,suffixOps,after];split <;> split <;> rfl
  have keepEnd (r : Reg) (hr : r∉[Reg.x7,.x8]) : z.getReg r=u.getReg r:=
    (outsideCalc endOps v z regs _ writers r hr).trans (regStore r)
  have s7 : v.getReg .x7=preValue d (byte s a) (s.getReg .x7):=(regStore _).trans pre.next
  have s8 (yes : d=true) : v.getReg .x8=s.getReg .x8:=(regStore _).trans (pre.accumulator yes)
  refine ⟨z,⟨?_,?_,?_,(keepEnd _ (by decide)).trans pre.addr,?_,?_,?_⟩⟩
  · rw [sz];exact (pre.run.trans storeRun).trans finish
  · exact endPC.trans (congrArg pcAt (by dsimp only [ip];omega))
  · intro q hq
    have val:=wrote q hq
    have eqmem : z.mem=v.mem:=mem
    have left : byte z q=byte v q:=by simp only [byte,MachineState.getByte,MachineState.getMem,eqmem]
    have saved : byte u q=byte s q:=by simp only [byte,MachineState.getByte,MachineState.getMem,pre.mem]
    rw [left,val,saved,pre.val]
  · intro yes;subst d
    by_cases b:p+1<pieces k
    · rw [if_pos b]
      have z7 : z.getReg .x7=v.getReg .x7 >>> 2:=by simp only [z,endOps,suffixOps,after,b,decide_true,Bool.false_eq_true,ite_false,ite_true];rfl
      exact z7.trans (congrArg (fun x : Word=>x >>> (2 : Nat)) (show v.getReg .x7=s.getReg .x7 from s7))
    · rw [if_neg b]
      have z7 : z.getReg .x7=v.getReg .x7:=by simp only [z,endOps,suffixOps,after,b,decide_false,Bool.false_eq_true,ite_false];rfl
      exact z7.trans s7
  · intro yes;subst d
    by_cases zero:p=0
    · subst p;have z8 : z.getReg .x8=v.getReg .x8 ||| v.getReg .x7:=rfl
      rw [z8,s7,s8 rfl];simp [preValue,a]
    · have z8 : z.getReg .x8=v.getReg .x8 ||| (v.getReg .x7 <<< (BitVec.ofNat 6 (2*p)).toNat):=by
        simp only [z,endOps,suffixOps,after,zero,ite_true,ite_false];rfl
      rw [z8,s7,s8 rfl,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];rfl
  · intro r hr
    have no : r∉[Reg.x7,.x8]:=by intro h;exact hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    exact (keepEnd r no).trans (pre.keep r hr)
end CommitGolfCandidate.R1b.Codec
