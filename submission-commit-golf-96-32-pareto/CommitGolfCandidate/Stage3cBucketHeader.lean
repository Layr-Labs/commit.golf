import CommitGolfCandidate.Stage3cBucketMemory
import CommitGolfCandidate.Stage3cCheckCompare
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def bucketOps : List Sym.Calc:=[.lui .x6 16,.addi .x6 .x6 1024,.add .x7 .x6 .x14,.lbu .x28 .x7 0,
  .lui .x29 17,.addi .x29 .x29 2048,.slli .x30 .x14 5,.add .x29 .x29 .x30]
def duplicateCmp : CompareSite:=⟨772,2144,true,.x29,.x27,.x30,.x31⟩
def bucketTemps : List Reg:=[.x6,.x7,.x28,.x29,.x30]
private theorem preserved (s : MachineState) (q : Reg) (ne : q∉bucketTemps) :
    ((bucketOps.foldl Sym.bump Sym.original) q).eval s=s.getReg q := by
  cases q <;> first | (exfalso;apply ne;decide) | rfl
structure BucketHeader (o : Oracle) (s t : MachineState) (j : Nat) (prev : Option Late.Digest) : Prop where
  run : Flow o s t 9 0
  pc : t.pc=pcAt (if prev.isSome then 772 else 789)
  marks : t.getReg .x7=W (marksBuf+j)
  slot : t.getReg .x29=W (bucketAddress j)
  mem : t.mem=s.mem
  keep : ∀ q,q∉bucketTemps → t.getReg q=s.getReg q

theorem bucket_header (o : Oracle) (s : MachineState) (j : Nat) (prev : Option Late.Digest) (small : j<512)
    (pc : s.pc=pcAt 763) (idx : s.getReg .x14=W j) (mark : Open.byteAt s (marksBuf+j)=markBit prev) :
    ∃ t,BucketHeader o s t j prev := by
  let u:=Sym.evaluated bucketOps s
  have addr : (W marksBuf+s.getReg .x14)+0#64=W (marksBuf+j):=by rw [idx,BitVec.add_zero];exact (BitVec.ofNat_add ..).symm
  have safe : ∀ e∈Sym.requirements Sym.original bucketOps,accessValid (e.1.eval s) e.2=true := by
    intro e h
    change e∈[(Sym.Expr.op .add (.op .add (.lit (W marksBuf)) (.reg .x14)) (.lit 0),1)] at h
    obtain rfl:=List.mem_singleton.mp h
    change accessValid ((W marksBuf+s.getReg .x14)+0#64) 1=true;rw [addr]
    apply access_ok <;> dsimp [marksBuf,MEMORY_BYTES] <;> omega
  obtain ⟨begin_,regs,mem,ip⟩:=Sym.compiled o bucketOps 763 s pc (by decide +kernel) safe
  have seen : u.getReg .x28=(markBit prev).zeroExtend 64:=by
    apply (regs .x28).trans;change (s.getByte ((W marksBuf+s.getReg .x14)+0#64)).zeroExtend 64=_;rw [addr];exact congrArg (fun v : Byte=>v.zeroExtend 64) mark
  have dst : u.getReg .x29=W (bucketAddress j):=by
    apply (regs .x29).trans;change W compBase+(s.getReg .x14 <<< 5)=_
    rw [idx];unfold W;rw [Open.shifted,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);unfold bucketAddress;omega
  have mp : u.getReg .x7=W (marksBuf+j):=by
    apply (regs .x7).trans;change W marksBuf+s.getReg .x14=_;rw [idx];exact (BitVec.ofNat_add ..).symm
  have flag : Rel.eq.test (u.getReg .x28) (u.getReg .x0)= !prev.isSome:=by
    change (u.getReg .x28==0#64)=_;rw [seen];cases prev <;> rfl
  have control:=branch o u 771 789 .eq .x28 .x0 (by decide +kernel) ip _ flag
  let t:=u.setPC (pcAt (if prev.isSome then 772 else 789))
  have eq : (if !prev.isSome then 789 else 771+1)=(if prev.isSome then 772 else 789):=by cases prev <;> rfl
  rw [eq] at control
  exact ⟨t,⟨begin_.trans control,rfl,MachineState.getReg_setPC.trans mp,MachineState.getReg_setPC.trans dst,mem,
    fun q h=>MachineState.getReg_setPC.trans ((regs q).trans (preserved s q h))⟩⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
