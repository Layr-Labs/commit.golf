import CommitGolfCandidate.S5FieldPayload
import CommitGolfCandidate.S5WriterFrame
import CommitGolfCandidate.S5Gates
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Writer (PackedPrefix pushBits Below)

inductive EmitSite | salt | bottomFirst | bottomSecond | sibling (d : Fin 14) | cap deriving DecidableEq,Fintype
def EmitSite.pc : EmitSite→Nat | .salt=>154 | .bottomFirst=>168 | .bottomSecond=>176 | .sibling d=>189+12*d.val | .cap=>377
def EmitSite.width : EmitSite→Nat | .salt=>192 | .bottomFirst|.bottomSecond=>256 | .sibling d=>S5.bits (d.val+1) | .cap=>230
def EmitSite.setup (e : EmitSite) : PathCode := [(e.pc,.ADDI .x11 .x0 (BitVec.ofNat 12 e.width)),(e.pc+1,.JAL .x1 (disp21 (e.pc+1) 21))]
def emitStart (e : EmitSite) (s : MachineState) := pathEnd s e.setup
private theorem siteFacts : ∀ e : EmitSite,e.setup.all (matchesWord .opening) ∧
    pcAt (e.pc+1)+signExtend21 (disp21 (e.pc+1) 21)=pcAt 21 ∧
    pcAt (e.pc+2) &&& ~~~1#64=pcAt (e.pc+2) ∧
    signExtend12 (BitVec.ofNat 12 e.width)=W e.width ∧ e.width≤256 := by decide +kernel

private theorem direct_call (e : EmitSite) (s : MachineState) (atPC : s.pc=pcAt e.pc) :
    let t:=emitStart e s
    Runs s t 2 2 ∧ t.pc=pcAt 21 ∧ t.getReg .x1=pcAt (e.pc+2) ∧ t.getReg .x11=W e.width ∧ t.mem=s.mem ∧
    ∀ r : Reg,r ≠ .x1 → r ≠ .x11 → t.getReg r=s.getReg r := by
  let u:=execInstrBr s (.ADDI .x11 .x0 (BitVec.ofNat 12 e.width))
  obtain ⟨layout,land,_,imm,_⟩:=siteFacts e
  have ip : u.pc=pcAt (e.pc+1) := by change s.pc+4=_;rw [atPC,pc_succ]
  have ok : pathReady s e.setup:=⟨atPC,rfl,rfl,ip,rfl,rfl,True.intro⟩
  refine ⟨path_run _ true _ _ layout ok,?_,?_,?_,rfl,?_⟩
  · change u.pc+signExtend21 (disp21 (e.pc+1) 21)=_;rw [ip,land]
  · change u.pc+4=_;rw [ip,pc_succ]
  · change 0#64+signExtend12 (BitVec.ofNat 12 e.width)=_;rw [BitVec.zero_add,imm]
  · intro r ra size
    exact MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ ra.symm).trans
      (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ size.symm)))

structure ProofCursor (data : Prop) (s : MachineState) (n v : Nat) : Prop where
  ptr : s.getReg .x19=W (proofBase+8*(n/64))
  count : s.getReg .x24=W (n%64)
  sixty : s.getReg .x27=64
  payload : data → PackedPrefix s proofBase n v

theorem cursor_same {s t n v valid} (c : ProofCursor valid s n v) (mem : t.mem=s.mem)
    (ptr : t.getReg .x19=s.getReg .x19) (count : t.getReg .x24=s.getReg .x24)
    (sixty : t.getReg .x27=s.getReg .x27) (buf : t.getReg .x23=s.getReg .x23) : ProofCursor valid t n v := by
  refine ⟨ptr.trans c.ptr,count.trans c.count,sixty.trans c.sixty,?_⟩
  intro ok;have p:=c.payload ok
  exact ⟨p.value,ptr.trans p.ptr,count.trans p.bits,(congrArg BitVec.toNat buf).trans p.held,
    fun j hj=>(congrArg BitVec.toNat (congrFun mem _)).trans (p.words j hj)⟩

def emitted (e : EmitSite) (n : Nat) (s : MachineState) := pathEnd (emitStart e s) (Writer.fieldCode e.width (n%64))
def emitCycles (e : EmitSite) (n : Nat) :=2+(Writer.measureField ⟨n%64,0⟩ e.width).cycles

theorem emit_field (s : MachineState) (e : EmitSite) (valid : Prop) (n v a x : Nat) (cur : ProofCursor valid s n v)
    (pc : s.pc=pcAt e.pc) (source : s.getReg .x10=W a) (align : a%8=0) (low : a+32≤proofBase) (upto : n≤555170)
    (word : valid → Writer.SourceWords s a x (Writer.parts e.width)) (xSize : valid → x<2^e.width) :
    let t:=emitted e n s
    Runs s t (emitCycles e n) (emitCycles e n) ∧ t.pc=pcAt (e.pc+2) ∧
    ProofCursor valid t (n+e.width) (pushBits v n x) ∧ Below s t (proofBase+8*(n/64)) ∧
      ∀ r : Reg,Writer.preserved r → r≠.x1 → r≠.x11 → t.getReg r=s.getReg r := by
  obtain ⟨head,ip,ret,size,mem,keep⟩:=direct_call e s pc
  let u:=emitStart e s
  let d:=proofBase+8*(n/64)
  have cu : ProofCursor valid u n v:=cursor_same cur mem (keep _ (by decide) (by decide)) (keep _ (by decide) (by decide))
    (keep _ (by decide) (by decide)) (keep _ (by decide) (by decide))
  have addr : u.getReg .x10=W a := (keep _ (by decide) (by decide)).trans source
  obtain ⟨_,_,even,_,bound⟩:=siteFacts e
  have destAlign : d%8=0 := by dsimp [d,proofBase];omega
  have destBound : d+32≤MEMORY_BYTES:=by dsimp [d,proofBase];change _≤2^36;omega
  have result:=Writer.field_call u e.width (n%64) a d bound (Nat.mod_lt _ (by decide)) ip size cu.count cu.sixty
    addr cu.ptr align destAlign (low.trans (by decide)) destBound
  obtain ⟨run,back,bits,ptr⟩:=result
  let t:=emitted e n s
  have newPtr : t.getReg .x19=W (proofBase+8*((n+e.width)/64)) := ptr.trans (congrArg W (by dsimp [d];omega))
  have newBits : t.getReg .x24=W ((n+e.width)%64):=bits.trans (congrArg W (by omega))
  have saved (r : Reg) (h : Writer.preserved r) : t.getReg r=u.getReg r := Writer.field_framed e.width (n%64) u r h
  have codeSize : (Writer.fieldCode e.width (n%64)).length≤100 := (by decide +kernel : ∀ e : EmitSite,∀ k : Fin 64,(Writer.fieldCode e.width k.val).length≤100) e ⟨n%64,Nat.mod_lt _ (by decide)⟩
  have outside:=Writer.field_below u e.width (n%64) d cu.ptr (by change d+32≤2^36 at destBound;omega)
  refine ⟨head.trans run,back.trans ((congrArg (· &&& ~~~1#64) ret).trans even),
    ⟨newPtr,newBits,(saved _ (by simp [Writer.preserved])).trans cu.sixty,?_⟩,
    fun j hj=>(outside j hj).trans (congrFun mem _),fun r h a b=>(saved r h).trans (keep r a b)⟩
  intro ok
  have words:=Writer.source_below proofBase a x (Writer.parts e.width) (word ok) (fun j _=>congrFun mem _) (by
    have count : (Writer.parts e.width).length≤4 := by simp only [Writer.parts,List.length_append,List.length_replicate];split <;> simp <;> omega
    omega)
  exact (Writer.field_payload u e.width proofBase n v a x (cu.payload ok) words bound (xSize ok) ip size addr cu.sixty
    (by decide) align low (by unfold proofBase;change _≤2^36;omega)).1
end CommitGolfCandidate.S5Machine.Open
