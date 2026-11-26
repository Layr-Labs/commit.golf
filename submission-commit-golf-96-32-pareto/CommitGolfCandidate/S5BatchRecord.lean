import CommitGolfCandidate.S5BatchRecordFields
import CommitGolfCandidate.S5BatchSalt
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)

def saltField (salt : SaltTape) (i : Index) : S5.Field := (192,(salt i).toNat)
def biased (i : Index) : Nat := if i.val%2=0 then 1 else 0
structure RecordBody (s t : MachineState) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (r : Nat) (fs : List S5.Field) : Prop where
  run : let i:=ix xs r;let cost:=202+biased i+energy (widths fs) (S5.record tree salt i true)
        Runs s t cost (cost+12)
  pc : t.pc=pcAt 347
  bucket : t.getReg .x14=W (indexAbove (ix xs r) 15)
  nextIndex : t.getReg .x9=W (indexBase+8*(r+1))
  cursor : FieldCursor tree t (fs++S5.record tree salt (ix xs r) true)
  input : InputRows t xs seen tree salt
  keep : ∀ reg∈outerRegs,reg≠.x9 → t.getReg reg=s.getReg reg

attribute [local irreducible] ix S5.record energy Writer.measureField
theorem batch_record (s : MachineState) (r : Nat) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (fs : List S5.Field) (hr : r<xs.length) (size : xs.length≤LENGTH) (limit : widths fs+4030≤555170)
    (cur : FieldCursor tree s fs) (env : InputRows s xs seen tree salt) (pc : s.pc=pcAt 144)
    (indexPtr : s.getReg .x9=W (indexBase+8*r)) (row : s.getReg .x20=W rowBase) (gp : s.getReg .x3=W 2048)
    (three : s.getReg .x25=3) : ∃ t,RecordBody s t xs seen tree salt r fs := by
  let i:=ix xs r
  let saltF:=saltField salt i
  let fsA:=fs++[saltF]
  let peers:=peerFields tree i
  let fsB:=fsA++peers
  have wa : widths fsA=widths fs+192:=by simp [widths,fsA,saltF,saltField]
  have wb : widths fsB=widths fsA+512:=by rw [show fsB=fsA++peers from rfl,sum_append];rfl
  obtain ⟨u,one,ipu,idx,next,cA,inputA,keepA⟩:=batch_salt s r xs seen tree salt fs hr size (by omega) cur env pc indexPtr row
  obtain ⟨v,two,ipv,idxV,cB,inputB,keepB⟩:=batch_ternary u i xs seen tree salt fsA size (by omega) inputA cA ipu
    ((keepA .x3 (by decide) (by decide)).trans gp) ((keepA .x25 (by decide) (by decide)).trans three) idx
  obtain ⟨t,path,ipt,bucket,cC,inputC,keepC⟩:=batch_path v 0 14 i xs seen tree salt size inputB fsB (by decide)
    (by rw [upper_width];omega) cB ipv ((keepB .x3 (by decide)).trans ((keepA .x3 (by decide) (by decide)).trans gp)) idxV
  have layout : fs++S5.record tree salt i true=fsB++binaryFields tree i 0 14 := by
    simp only [fsB,fsA,peers,saltF,saltField,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,batch_record_fields]
  refine ⟨t,⟨?_,ipt,bucket,(keepC .x9 (by decide)).trans ((keepB .x9 (by decide)).trans next),layout ▸ cC,
    inputC,fun q h ne=>(keepC q h).trans ((keepB q h).trans (keepA q h ne))⟩⟩
  let au:=(Writer.measureField ⟨widths fs%64,0⟩ 192).cycles
  let av:=energy (widths fsA) peers
  let atail:=energy (widths fsB) (binaryFields tree i 0 14)
  have charged : energy (widths fs) (S5.record tree salt i true)=au+(av+atail) := by
    rw [batch_record_fields,energy,energy_append]
    change au+(energy (widths fs+192) peers+energy (widths fs+192+widths peers) _)=_
    rw [←wa,←sum_append]
  have all:=(one.trans two).trans path
  change Runs s t (((if i.val%2=0 then 10 else 9)+(2+au)+(23+av))+(168+atail))
    (((if i.val%2=0 then 10 else 9)+(2+au)+(23+av+12))+(168+atail)) at all
  change Runs s t (202+biased i+energy (widths fs) (S5.record tree salt i true)) (202+biased i+energy (widths fs) (S5.record tree salt i true)+12)
  rw [charged]
  by_cases b : i.val%2=0 <;> simp only [biased,b,ite_true,ite_false] at all ⊢ <;> convert all using 1 <;> omega
end CommitGolfCandidate.S5Machine.Open
