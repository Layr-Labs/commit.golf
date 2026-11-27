import CommitGolfCandidate.S4PairCode

set_option Elab.async false
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)
def leftChild (H : Compression) (v : View) (j : Nat) := served H v 128 (2*j)
def rightChild (H : Compression) (v : View) (j : Nat) := served H v 128 (2*j+1)
def touched (H : Compression) (v : View) (j : Nat) := (leftChild H v j).isSome || (rightChild H v j).isSome
abbrev pairKeep (r : Reg) := r∈[Reg.x1,.x5,.x9,.x11,.x13,.x19,.x23,.x27,.x29,.x30]
def flagRead (off : Nat) := Sym.Expr.byteLoad (Sym.mkOp .add (.reg .x1) (.lit (W off)))
def childPtr (cap : Nat) (d : Option Digest) := if d.isSome then cap else 352
structure PairLoaded (o : Oracle) (x : CheckInput) (s t : MachineState) (j steps : Nat) : Prop where
  run : CheckRuns o s t steps 0
  pc : t.pc=pcAt (if touched o.compression (readView x) j then 4461 else 4495)
  frame : SameOutside s t 352 32
  keep : ∀ r,pairKeep r → t.getReg r=s.getReg r
  cursor : t.getReg .x18=W (wireSlot (j+1))
  left : t.getReg .x3=flagBit (leftChild o.compression (readView x) j).isSome
  right : t.getReg .x4=flagBit (rightChild o.compression (readView x) j).isSome
  slot : readBuffer t 352 32=(readView x).slot j

private theorem nzBits (left right : Bool) : (((flagBit left ||| flagBit right)==(0 : Word))==false)=(left || right) := by
  cases left <;> cases right <;> decide
private theorem slotNext (j : Nat) : wireSlot j+30=wireSlot (j+1):=by unfold wireSlot;omega
attribute [local irreducible] loaded Sym.evaluated
set_option maxRecDepth 4000 in
theorem pairLoad (o : Oracle) (x : CheckInput) (s : MachineState) (j : Nat) (bj : j<171)
    (f : PairCursor o.compression x s j) : ∃ t steps,steps≤68 ∧ PairLoaded o x s t j steps := by
  let v:=readView x
  let a:=leftChild o.compression v j;let b:=rightChild o.compression v j
  have pc : s.pc=pcAt 4393:=by have e:=f.pc;rw [pairPC,if_pos bj] at e;exact e
  have sz : 32768≤wireSlot j ∧ wireSlot j+30≤MEMORY_BYTES:=by unfold wireSlot proofBase MEMORY_BYTES;omega
  let u:=loaded s 352 30
  have load:=loadField s 4393 (wireSlot j) 352 30 (Or.inr (Or.inl rfl)) pairSites.slot (by decide) pc f.proof rfl
    (by exact ⟨by decide,by decide⟩) sz.2 (by omega)
  have info : readBuffer u 352 32=v.slot j:=by
    apply (load.digest (Or.inl rfl)).trans
    apply congrArg (BitVec.setWidth 256)
    apply (f.data.read (wireSlot j) 30 sz.1 (sz.2.trans (by decide))).trans
    unfold proofAt initial
    apply congrArg (fun addr=>readBuffer (Late.submission.initialState .check x) addr 30)
    change proofBase+65280+30*j=proofBase+(65280+30*j);omega
  have flags (z : Nat) (bound : z<342) : byte u (flagAddr z)=if (served o.compression v 128 z).isSome then 1 else 0:=
    (load.outside (flagAddr z) (by unfold flagAddr;omega) (Or.inr (by unfold flagAddr;omega))).trans (f.seen.flags z bound)
  have ptr : u.getReg .x1=W (flagAddr (2*j)):=(load.keep _ (by decide) (by decide) (by decide)).trans f.flagsPtr
  have addr (off : Nat) : u.getReg .x1+W off=W (flagAddr (2*j+off)):=by rw [ptr];exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by unfold flagAddr;omega))
  have get (off : Nat) (limit : 2*j+off<342) :
      (flagRead off).eval u=flagBit (served o.compression v 128 (2*j+off)).isSome:=by
    simp only [flagRead,Sym.Expr.eval,Sym.eval_mkOp,Sym.Bin.apply,addr]
    change (byte u (flagAddr (2*j+off))).zeroExtend 64=_;rw [flags _ limit];cases (served o.compression v 128 (2*j+off)).isSome <;> rfl
  let t:=Sym.evaluated pairFlags u
  have access (off : Nat) (small : off<2) : accessValid (u.getReg .x1+W off) 1=true:=by
    rw [addr];exact Safe.valid ⟨by unfold flagAddr MEMORY_BYTES;omega,Nat.mod_one _⟩
  have reads : Sym.requirements Sym.original pairFlags=
      [(Sym.mkOp .add (.reg .x1) (.lit (W 0)),1),(Sym.mkOp .add (.reg .x1) (.lit (W 1)),1)]:=rfl
  obtain ⟨run,regs,mem,next⟩:=evalMath .check pairFlags 4456 4459 u load.pc pairSites.flags
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : pairFlags.all (fun c=>c.dst != .x0)=true) c h))
    (fun e he=>by rw [reads] at he;simp only [List.mem_cons,List.not_mem_nil,or_false] at he
                  rcases he with rfl|rfl <;> simp only [Sym.eval_mkOp,Sym.Expr.eval,Sym.Bin.apply]
                  · exact access 0 (by decide)
                  · exact access 1 (by decide))
  have l : t.getReg .x3=flagBit a.isSome:=(regs .x3).trans (get 0 (by omega))
  have r : t.getReg .x4=flagBit b.isSome:=(regs .x4).trans (get 1 (by omega))
  have test : ((t.getReg .x7==t.getReg .x0)==false)=touched o.compression v j:=by
    have flag : t.getReg .x7=flagBit a.isSome ||| flagBit b.isSome:=by
      apply (regs .x7).trans;change (flagRead 0).eval u ||| (flagRead 1).eval u=_
      rw [get 0 (by omega),get 1 (by omega)];rfl
    rw [flag];change (((flagBit a.isSome ||| flagBit b.isSome)==(0 : Word))==false)=(a.isSome || b.isSome)
    exact nzBits a.isSome b.isSome
  have edge:=alternate .check 4459 4461 4495 .x7 .x0 false pairSites.touched pairSites.empty rfl t next
  rw [test] at edge
  let yes:=touched o.compression v j
  let z:=t.setPC (pcAt (if yes then 4461 else 4495))
  have head : ∃ n,n≤68 ∧ CheckRuns o s z n 0:=by
    by_cases hit : yes=true
    · have e : Runs .check t z 1 1:=by dsimp only [z];simpa only [hit,ite_true,yes] using edge
      exact ⟨67,by decide,ofRuns o ((load.run.trans run).trans e)⟩
    · have e : Runs .check t z 2 2:=by dsimp only [z];have no:=Bool.eq_false_iff.mpr hit;simpa only [no,yes,Bool.false_eq_true,ite_false] using edge
      exact ⟨68,by decide,ofRuns o ((load.run.trans run).trans e)⟩
  obtain ⟨n,hn,go⟩:=head
  have same : z.mem=u.mem:=mem
  have old (reg : Reg) (ok : reg∉[Reg.x3,.x4,.x7]) : z.getReg reg=u.getReg reg:=
    MachineState.getReg_setPC.trans (outsideCalc pairFlags u t regs _ (by decide) reg ok)
  have disjoint : ∀ r : Reg,pairKeep r → r∉[Reg.x3,.x4,.x7] ∧ r≠.x6 ∧ r≠.x14 ∧ r≠.x18:=by intro r;cases r <;> decide
  refine ⟨z,n,hn,⟨go,rfl,?_,fun reg ok=>(old reg (disjoint reg ok).1).trans
    (load.keep _ (disjoint reg ok).2.1 (disjoint reg ok).2.2.1 (disjoint reg ok).2.2.2),
    (old _ (by decide)).trans (load.cursor.trans (congrArg W (slotNext j))),l,r,
    (read_buffer_memory_congr z u same _ _).trans info⟩⟩
  intro q h away;simpa only [byte,MachineState.getByte,MachineState.getMem,same] using load.outside q h away
end CommitGolfCandidate.S4.Machine
