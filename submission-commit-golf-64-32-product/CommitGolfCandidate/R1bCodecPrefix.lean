import CommitGolfCandidate.R1bCodecCode
namespace CommitGolfCandidate.R1b.Codec
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine
open R1bPC (pcAt pc_succ)

def controlReg (r : Reg) := r∉[Reg.x21,.x6,.x7,.x8]
def loadedField (dec : Bool) (old : Byte) (z : Word) : Word :=
  let a:=old.zeroExtend 64
  if dec then a &&& 63 else (a &&& 63) ||| ((z &&& 3) <<< 6)
def highWord (v : Byte) : Word := v.zeroExtend 64 >>> 6
def preValue (dec : Bool) (old : Byte) (z : Word) : Word := if dec then highWord old else z
def preLen (dec : Bool) := if dec then 4 else 6

private theorem shortImm : ∀ j : Fin 353,signExtend12 (BitVec.ofNat 12 j.val)=W j.val := by decide
theorem immediate (j : Nat) (b : j<353) : signExtend12 (BitVec.ofNat 12 j)=W j := shortImm ⟨j,b⟩
theorem prevAddr (base c : Nat) (hc : c<1396) :
    W (base+Carry.prev c)+signExtend12 (BitVec.ofNat 12 (Carry.delta c))=W (base+Carry.carrier c) := by
  have g:=Carry.walk c hc
  rw [immediate _ (by omega),←BitVec.ofNat_add];exact congrArg W (by omega)

structure PrefixResult (dec : Bool) (c : Code) (s t : MachineState) (site a : Nat) : Prop where
  run : Runs c s t (preLen dec) (preLen dec)
  pc : t.pc=pcAt (site+preLen dec)
  mem : t.mem=s.mem
  addr : t.getReg .x21=W a
  val : t.getReg .x6=loadedField dec (byte s a) (s.getReg .x7)
  next : t.getReg .x7=preValue dec (byte s a) (s.getReg .x7)
  accumulator : dec=true → t.getReg .x8=s.getReg .x8
  keep : ∀ r,controlReg r → t.getReg r=s.getReg r

private def compute (d : Bool) : List Sym.Calc :=
  if d then [.srli .x7 .x6 6,.andi .x6 .x6 63] else
    [.andi .x8 .x7 3,.slli .x8 .x8 6,.andi .x6 .x6 63,.bor .x6 .x6 .x8]
private theorem lengthComp (d : Bool) : 2+(compute d).length=preLen d := by cases d <;> rfl

theorem runPrefix (dec : Bool) (c : Code) (s : MachineState) (site base idx : Nat) (ci : idx<1396)
    (pc : s.pc=pcAt site) (room : site+preLen dec≤c.count)
    (matchesCode : Matches c site ((before dec idx).map Sym.Calc.instr))
    (ptr : s.getReg .x21=W (base+Carry.prev idx)) (bound : base+67488≤MEMORY_BYTES) :
    ∃ t,PrefixResult dec c s t site (base+Carry.carrier idx) := by
  let a:=base+Carry.carrier idx
  let off:=BitVec.ofNat 12 (Carry.delta idx)
  let u:=execInstrBr s (.ADDI .x21 .x21 off)
  let v:=execInstrBr u (.LBU .x6 .x21 0)
  have steps:=lengthComp dec
  have okA : a+1≤MEMORY_BYTES:=by dsimp only [a];have:=(Carry.location idx ci).2;omega
  have layout : Matches c site (.ADDI .x21 .x21 off::.LBU .x6 .x21 0::(compute dec).map Sym.Calc.instr):=by
    cases dec <;> exact matchesCode
  have step1:=stepAdd c s site .x21 .x21 off (by omega) pc layout.head
  have ra : u.getReg .x21=W a:=by
    rw [getAfterAdd s .x21 .x21 off (by decide),ptr];exact prevAddr base idx ci
  have ip1 : u.pc=pcAt (site+1):=addPC .x21 .x21 off pc
  have valid : memoryArgumentsValid u (.LBU .x6 .x21 0)=true:=by
    change accessValid (u.getReg .x21+0) 1=true
    rw [show u.getReg .x21+(0 : Word)=u.getReg .x21 from BitVec.add_zero _,ra];exact Safe.valid ⟨okA,Nat.mod_one _⟩
  have step2 : Runs c u v 1 1:=one (by omega) ip1 _ layout.tail.head (by simp only [ordinaryStep,if_pos valid];rfl)
  have ip2 : v.pc=pcAt (site+2):=(congrArg (·+4) ip1).trans (pc_succ (site+1)).symm
  let t:=Sym.evaluated (compute dec) v
  have preSize : site+2+(compute dec).length≤c.count:=by omega
  obtain ⟨run,regs,frame,endPC⟩:=calcRegs c v (compute dec) (site+2) ip2 preSize layout.tail.tail
    (by cases dec <;> rfl) (by cases dec <;> rfl)
  have cost : Sym.price (compute dec)=(compute dec).length:=by cases dec <;> rfl
  have rd6 : v.getReg .x6=(byte s a).zeroExtend 64:=by
    change (u.getByte (u.getReg .x21+0)).zeroExtend 64=_
    rw [show u.getReg .x21+(0 : Word)=u.getReg .x21 from BitVec.add_zero _,ra];rfl
  have rd7 : v.getReg .x7=s.getReg .x7:=rfl
  have fr : v.mem=s.mem:=rfl
  have keep0 (r : Reg) (nr : controlReg r) : v.getReg r=s.getReg r:=by
    have diff : Reg.x21≠r ∧ Reg.x6≠r:=by
      unfold controlReg at nr;simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at nr
      exact ⟨Ne.symm nr.1,Ne.symm nr.2.1⟩
    exact MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ diff.2).trans (keepAdd s .x21 .x21 r off diff.1))
  rw [cost] at run
  refine ⟨t,⟨?_,?_,frame.trans fr,?_,?_,?_,?_,?_⟩⟩
  · rw [←steps];exact (step1.trans step2).trans run
  · exact endPC.trans (congrArg pcAt (by omega))
  · have kr:=outsideCalc (compute dec) v t regs [.x6,.x7,.x8] (by cases dec <;> decide) .x21 (by decide)
    exact kr.trans ra
  · cases dec
    · change (v.getReg .x6 &&& 63) ||| ((v.getReg .x7 &&& 3) <<< 6)=_;rw [rd6,rd7];rfl
    · change v.getReg .x6 &&& 63=_;rw [rd6];rfl
  · cases dec
    · exact rd7
    · change v.getReg .x6 >>> 6=_;rw [rd6];rfl
  · intro yes;subst dec;rfl
  · intro r nr
    have away : r∉[Reg.x6,.x7,.x8]:=by intro h;exact nr (List.mem_cons_of_mem _ h)
    exact (outsideCalc (compute dec) v t regs [.x6,.x7,.x8] (by cases dec <;> decide) r away).trans (keep0 r nr)
end CommitGolfCandidate.R1b.Codec
