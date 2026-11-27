import CommitGolfCandidate.Stage3cCapHash
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def markOps : List Sym.Calc := [.lui .x6 16,.addi .x6 .x6 1024,.slli .x7 .x23 1,.add .x6 .x6 .x7,.lbu .x7 .x6 0,.lbu .x28 .x6 1]
def pairAddressOps : List Sym.Calc := [.lui .x4 24,.srli .x6 .x23 1,.slli .x29 .x6 1,.add .x29 .x29 .x6,
  .slli .x29 .x29 5,.andi .x6 .x23 1,.slli .x6 .x6 5,.add .x6 .x29 .x6,.add .x4 .x4 .x6,.bor .x6 .x7 .x28]
def markedWord (v : Option Late.Digest) : Word:=(markBit v).zeroExtend 64
def touched (a b : Option Late.Digest):=a.isSome || b.isSome
private theorem either (a b : Option Late.Digest) : ((markedWord a ||| markedWord b) != 0#64)=touched a b:=by cases a <;> cases b <;> simp [markedWord,markBit,touched] <;> decide
private theorem addrCalc (p : Fin 256) : W marksBuf+(W p.val <<< 1)=W (marksBuf+2*p.val) ∧
    W capBase+(((((W p.val >>> 1) <<< 1)+(W p.val >>> 1)) <<< 5)+((W p.val &&& 1) <<< 5))=W (nodeAt 0 p.val) :=
  (by decide +kernel : ∀ i : Fin 256,W marksBuf+(W i.val <<< 1)=W (marksBuf+2*i.val) ∧
    W capBase+(((((W i.val >>> 1) <<< 1)+(W i.val >>> 1)) <<< 5)+((W i.val &&& 1) <<< 5))=W (nodeAt 0 i.val)) p
private theorem keeps_mark (s : MachineState) (q : Reg) (ne : q∉([.x6,.x7,.x28] : List Reg)) :
    ((markOps.foldl Sym.bump Sym.original) q).eval s=s.getReg q:=by cases q <;> first | (exfalso;apply ne;decide) | rfl
private theorem keeps_addr (s : MachineState) (q : Reg) (ne : q∉([.x4,.x6,.x29] : List Reg)) :
    ((pairAddressOps.foldl Sym.bump Sym.original) q).eval s=s.getReg q:=by cases q <;> first | (exfalso;apply ne;decide) | rfl
private theorem read_marks (o : Oracle) (s : MachineState) (p : Nat) (sm : p<256) (a b : Option Late.Digest)
    (pc : s.pc=pcAt 817) (n : s.getReg .x23=W p)
    (left : Open.byteAt s (marksBuf+2*p)=markBit a) (right : Open.byteAt s (marksBuf+(2*p+1))=markBit b) :
    ∃ u,Flow o s u 6 0 ∧ u.pc=pcAt 823 ∧ u.getReg .x7=markedWord a ∧ u.getReg .x28=markedWord b ∧
      u.mem=s.mem ∧ (∀ q,q∉([.x6,.x7,.x28] : List Reg)→u.getReg q=s.getReg q) := by
  let addr:=W marksBuf+(s.getReg .x23 <<< 1)
  have loc : addr=W (marksBuf+2*p):=by dsimp [addr];rw [n];exact (addrCalc ⟨p,sm⟩).1
  have plus : addr+1#64=W (marksBuf+(2*p+1)) := (congrArg (·+1#64) loc).trans ((BitVec.ofNat_add (marksBuf+2*p) 1).symm.trans (congrArg W (by omega)))
  let e:=Sym.Expr.op .add (.lit (W marksBuf)) (.op .shl (.reg .x23) (.lit 1))
  have av : ∀ x∈Sym.requirements Sym.original markOps,accessValid (x.1.eval s) x.2=true := by
    intro x member;change x∈[(Sym.Expr.op .add e (.lit 0),1),(.op .add e (.lit 1),1)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · change accessValid (addr+0#64) 1=true;rw [BitVec.add_zero,loc];apply access_ok <;> dsimp [marksBuf,MEMORY_BYTES] <;> omega
    · change accessValid (addr+1#64) 1=true;rw [plus];apply access_ok <;> dsimp [marksBuf,MEMORY_BYTES] <;> omega
  obtain ⟨run,regs,mem,ep⟩:=Sym.compiled o markOps 817 s pc (by decide +kernel) av
  refine ⟨_,run,ep,?_,?_,mem,fun q h=>(regs q).trans (keeps_mark s q h)⟩
  · apply (regs .x7).trans;change (s.getByte (addr+0#64)).zeroExtend 64=_;rw [BitVec.add_zero,loc];exact congrArg (fun v : Byte=>v.zeroExtend 64) left
  · apply (regs .x28).trans;change (s.getByte (addr+1#64)).zeroExtend 64=_;rw [plus];exact congrArg (fun v : Byte=>v.zeroExtend 64) right

structure PairHead (o : Oracle) (s t : MachineState) (p : Nat) (a b : Option Late.Digest) : Prop where
  run : Flow o s t 17 0
  pc : t.pc=pcAt (if touched a b then 846 else 834)
  left : t.getReg .x7=markedWord a
  right : t.getReg .x28=markedWord b
  dest : t.getReg .x4=W (nodeAt 0 p)
  mem : t.mem=s.mem
  keep : CapKeeps s t
theorem pair_head (o : Oracle) (s : MachineState) (p : Nat) (sm : p<256) (a b : Option Late.Digest)
    (pc : s.pc=pcAt 817) (n : s.getReg .x23=W p)
    (left : Open.byteAt s (marksBuf+2*p)=markBit a) (right : Open.byteAt s (marksBuf+(2*p+1))=markBit b) :
    ∃ t,PairHead o s t p a b := by
  obtain ⟨u,one,ip,l,r,um,uk⟩:=read_marks o s p sm a b pc n left right
  obtain ⟨two,regs,vm,vp⟩:=Sym.compiled o pairAddressOps 823 u ip (by decide +kernel) (by change ∀ z∈([] : List (Sym.Expr×Nat)),_;simp)
  let v:=Sym.evaluated pairAddressOps u
  have vk (q : Reg) (ok : q∉([.x4,.x6,.x29] : List Reg)) : v.getReg q=u.getReg q:=(regs q).trans (keeps_addr u q ok)
  have dst : v.getReg .x4=W (nodeAt 0 p):=by
    apply (regs .x4).trans
    change W capBase+(((((u.getReg .x23 >>> 1) <<< 1)+(u.getReg .x23 >>> 1)) <<< 5)+((u.getReg .x23 &&& 1) <<< 5))=_
    rw [(uk _ (by decide)).trans n];exact (addrCalc ⟨p,sm⟩).2
  have cond : Rel.ne.test (v.getReg .x6) (v.getReg .x0)=touched a b:=by
    have val : v.getReg .x6=u.getReg .x7 ||| u.getReg .x28:=regs .x6
    change (v.getReg .x6 != 0#64)=_;rw [val,l,r];exact either a b
  have jump_:=branch o v 833 846 .ne .x6 .x0 (by decide +kernel) vp (touched a b) cond
  refine ⟨_,⟨(one.trans two).trans jump_,rfl,MachineState.getReg_setPC.trans ((vk _ (by decide)).trans l),
    MachineState.getReg_setPC.trans ((vk _ (by decide)).trans r),MachineState.getReg_setPC.trans dst,vm.trans um,?_⟩⟩
  intro q h;apply MachineState.getReg_setPC.trans;apply (vk q ?_).trans (uk q ?_)
  all_goals cases q <;> simp_all [capRegs]
end CommitGolfCandidate.Chained.BinaryMachine.Check
