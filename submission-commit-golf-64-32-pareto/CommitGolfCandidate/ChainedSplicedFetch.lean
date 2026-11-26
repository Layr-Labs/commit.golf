import CommitGolfCandidate.ChainedRelocation
import CommitGolfCandidate.ChainedPrefixSuffix

/-! Fetches in the chained postpass spliced after the actual cached prefix. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.PackedOpening (openingImage)
set_option maxRecDepth 8192

def cachedControllerImage : Image := ⟨openingImage.code.take 1435++openingControllerWords,openingImage.data⟩

theorem cached_controller_prefix : cachedControllerImage.code.take 1435=openingImage.code.take 1435 := by
  have length : (openingImage.code.take 1435).length=1435 := by decide
  change (openingImage.code.take 1435++openingControllerWords).take 1435=_
  rw [List.take_append,length,Nat.sub_self,List.take_zero,List.append_nil,List.take_take]
  rfl

theorem controller_fetched (s : MachineState) (instruction : Instruction)
    (fetched : fetch openingControllerImage s=some instruction) :
    ∃ i : Fin 2248, s.pc=BitVec.ofNat 64 (4096+4*i.val) ∧
      instruction=.base (openingControllerOps.getD i.val .EBREAK) := by
  obtain ⟨index,inside,pc,decoded⟩ := fetched_index openingControllerImage s instruction fetched
  have bound : index<2248 := by simpa only [openingControllerImage,opening_controller_words_length] using inside
  refine ⟨⟨index,bound⟩,?_,?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    exact pc
  · exact Option.some.inj (decoded.symm.trans (opening_controller_decode_at ⟨index,bound⟩))

theorem cached_controller_fetch (s : MachineState) (i : Fin 2248)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i.val)) :
    fetch cachedControllerImage (relocatedState 5740 s)=
      some (.base (openingControllerOps.getD i.val .EBREAK)) := by
  have small := i.isLt
  have numeric : (relocatedState 5740 s).pc.toNat=9836+4*i.val := by
    rw [relocated_pc,pc,BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [show (5740 : Word).toNat=5740 from rfl]
    rw [Nat.mod_eq_of_lt (show 4096+4*i.val<2^64 by omega),Nat.mod_eq_of_lt (by omega)]
    omega
  have length : (openingImage.code.take 1435).length=1435 := by decide
  rw [fetch,numeric,ite_eq_left (by omega),show (9836+4*i.val-4096)/4=1435+i.val by omega]
  simp only [cachedControllerImage]
  rw [List.getElem?_append,length,ite_eq_right (by omega),show 1435+i.val-1435=i.val by omega]
  cases word : openingControllerWords[i.val]? <;>
    simpa only [word,Option.bind_none,Option.bind_some] using opening_controller_decode_at i

theorem cached_controller_same (s : MachineState) (instruction : Instruction)
    (fetched : fetch openingControllerImage s=some instruction) :
    fetch cachedControllerImage (relocatedState 5740 s)=some instruction := by
  obtain ⟨i,pc,rfl⟩ := controller_fetched s instruction fetched
  exact cached_controller_fetch s i pc

private theorem controller_no_early_ecall : .ECALL∉openingControllerOps.take 2247 := by
  decide +kernel

theorem controller_ecall_last (i : Fin 2248) (ecall : openingControllerOps.getD i.val .EBREAK=.ECALL) :
    i.val=2247 := by
  by_contra outside
  have early : i.val<2247 := by omega
  have inside : i.val<(openingControllerOps.take 2247).length := by
    rw [List.length_take,opening_controller_ops_length]
    omega
  have member := List.getElem_mem inside
  have word : (openingControllerOps.take 2247)[i.val]=.ECALL := by
    rw [List.getElem_take]
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [opening_controller_ops_length]; exact i.isLt)] at ecall
    exact ecall
  rw [word] at member
  exact controller_no_early_ecall member

end CommitGolfCandidate.Chained.Native
