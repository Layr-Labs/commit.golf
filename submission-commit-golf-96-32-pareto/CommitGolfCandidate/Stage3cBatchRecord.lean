import CommitGolfCandidate.Stage3cBatchPath
import CommitGolfCandidate.Stage3cBatchSalt
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)

def saltField (salt : SaltTape) (i : Index) : Binary.Field := ⟨192,(salt i).toNat⟩
def biased (i : Index) : Nat := if i.val%2=0 then 1 else 0
structure RecordBody (s t : MachineState) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (r : Nat) (fs : List Binary.Field) : Prop where
  run : let i:=ix xs r;let cost:=193+energy (widths fs) (Binary.recordFields tree salt i)
        Runs s t cost (cost+3)
  pc : t.pc=pcAt 320
  bucket : t.getReg .x14=W (indexAbove (ix xs r) 15)
  nextIndex : t.getReg .x9=W (indexBase+8*(r+1))
  cursor : FieldCursor tree t (fs++Binary.recordFields tree salt (ix xs r))
  input : InputRows t xs seen tree salt
  keep : ∀ reg∈outerRegs,reg≠.x9 → t.getReg reg=s.getReg reg

theorem batch_record_fields (t : Levels) (salt : SaltTape) (i : Index) :
    Binary.recordFields t salt i = saltField salt i :: binaryFields t i 0 15 := by
  unfold Binary.recordFields binaryFields;rw [List.range_eq_range']
  congr 1
theorem batch_record_width (t s i) : widths (Binary.recordFields t s i)=3780:=by
  unfold widths;rw [Writer.record_widths];decide +kernel
theorem batch_record (s : MachineState) (r : Nat) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (fs : List Binary.Field) (hr:r<xs.length) (size:xs.length≤LENGTH) (limit:widths fs+3780≤542720)
    (cur : FieldCursor tree s fs) (env:InputRows s xs seen tree salt) (pc:s.pc=pcAt 127)
    (indices:s.getReg .x9=W (indexBase+8*r)) (row:s.getReg .x20=W rowBase) (gp:s.getReg .x3=W 2048) :
    ∃ t,RecordBody s t xs seen tree salt r fs:=by
  let i:=ix xs r
  obtain ⟨u,first,ip,idx,next,cu,data,keep⟩:=batch_salt s r xs seen tree salt fs hr size (by omega) cur env pc indices row
  let fsA:=fs++[saltField salt i]
  let fields:=binaryFields tree i 0 15
  have wa:widths fsA=widths fs+192:=by simp [fsA,widths,saltField]
  have wb:widths fields=3588:=by have h:=batch_record_width tree salt i;rw [batch_record_fields] at h;change 192+widths fields=3780 at h;omega
  obtain ⟨t,rest,close,bucket,packed,env',stable⟩:=batch_path u 0 15 i xs seen tree salt size data fsA (by decide)
    (by rw [wa,wb];omega) cu ip ((keep .x3 (by decide) (by decide)).trans gp) (by simpa [indexAbove,i] using idx)
  refine ⟨t,⟨?_,close,bucket,(stable _ (by decide)).trans next,?_,env',fun q m diff=>(stable q m).trans (keep q m diff)⟩⟩
  · have both:=first.trans rest
    have e1 : energy (widths fs) (Binary.recordFields tree salt i)=(Writer.measureField ⟨widths fs%64,0⟩ 192).cycles+energy (widths fs+192) fields := by
      rw [batch_record_fields];rfl
    have m : emitCycles .salt (widths fs)=2+(Writer.measureField ⟨widths fs%64,0⟩ 192).cycles := rfl
    rw [wa] at both
    have hfg : energy (widths fs+192) fields=energy (widths fs+192) (binaryFields tree i 0 15) := rfl
    show Runs s t (193+energy (widths fs) (Binary.recordFields tree salt i)) (193+energy (widths fs) (Binary.recordFields tree salt i)+3)
    rw [e1];convert both using 1 <;> omega
  · simpa only [batch_record_fields,fsA,fields,List.append_assoc,List.singleton_append] using packed
end CommitGolfCandidate.Chained.BinaryMachine.Open
