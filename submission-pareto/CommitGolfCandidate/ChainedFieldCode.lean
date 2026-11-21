import CommitGolfCandidate.ChainedFieldBuild

/-! Exact instruction images for straight-line low-body and descriptor construction. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def fieldBuildWord (n index : Nat) : BitVec 32 :=
  if index<4*n then byteCopyWords.getD (index%4) 0 else fieldDescriptorWords.getD (index-4*n) 0
def fieldBuildOp (n index : Nat) : Instr :=
  if index<4*n then byteCopyOp (index%4) else fieldDescriptorOp (index-4*n)
def fieldBuildWords (n : Nat) : List (BitVec 32) := List.ofFn fun i : Fin (4*n+5) => fieldBuildWord n i.val
def fieldBuildImage (n : Nat) : Image := ⟨fieldBuildWords n,[]⟩

theorem field_build_decode (n : Nat) (i : Fin (4*n+5)) :
    ((fieldBuildWords n)[i.val]?).bind decodeInstruction=some (.base (fieldBuildOp n i.val)) := by
  simp only [fieldBuildWords,List.getElem?_ofFn,dite_eq_left i.isLt,Option.bind_some]
  unfold fieldBuildWord fieldBuildOp
  split_ifs with inside
  · have bound : i.val%4<4 := Nat.mod_lt _ (by decide)
    generalize remainder : i.val%4=index at *
    interval_cases index <;> rfl
  · have bound : i.val-4*n<5 := by omega
    generalize remainder : i.val-4*n=index at *
    interval_cases index <;> rfl

private theorem field_image_fetch (image : Image) (s : MachineState) (index : Nat) (op : Instr)
    (fit : 4096+4*index<2^64) (pc : s.pc=BitVec.ofNat 64 (4096+4*index))
    (decoded : (image.code[index]?).bind decodeInstruction=some (.base op)) : fetch image s=some (.base op) := by
  have numeric : s.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  rw [fetch,numeric,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega]
  cases entry : image.code[index]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry,Option.bind_some] using decoded

theorem field_build_copy_at (n : Nat) (room : 4096+4*(4*n+5)<2^64) : LowCopyAt (fieldBuildImage n) 4096 n := by
  intro index inside i s pc
  have bound : 4*index+i.val<4*n := by have := i.isLt; omega
  have same : fieldBuildOp n (4*index+i.val)=byteCopyOp i.val := by
    have remainder : (4*index+i.val)%4=i.val := by have := i.isLt; omega
    simp only [fieldBuildOp,ite_eq_left bound,remainder]
  apply field_image_fetch (fieldBuildImage n) s (4*index+i.val) _ (by omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (16*index)+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add] at pc
    rw [pc]
    congr 1
    omega
  · simpa only [fieldBuildImage,same] using field_build_decode n ⟨4*index+i.val,by omega⟩

theorem field_build_descriptor_at (n : Nat) (room : 4096+4*(4*n+5)<2^64) :
    FieldDescriptorAt (fieldBuildImage n) (4096+BitVec.ofNat 64 (16*n)) := by
  intro i s pc
  have bound : 4*n+i.val<4*n+5 := by have := i.isLt; omega
  have same : fieldBuildOp n (4*n+i.val)=fieldDescriptorOp i.val := by
    simp [fieldBuildOp]
  apply field_image_fetch (fieldBuildImage n) s (4*n+i.val) _ (by omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (16*n)+BitVec.ofNat 64 (4*i.val) at pc
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add] at pc
    rw [pc]
    congr 1
    omega
  · simpa only [fieldBuildImage,same] using field_build_decode n ⟨4*n+i.val,bound⟩

end CommitGolfCandidate.Chained.Native
