import CommitGolfCandidate.GroupOpenTable
import CommitGolfCandidate.GroupOpenVirtual

/-! The trusted loader puts the embedded table (`GroupOpenTable`) at `dataBase`: every opening starts
with `TableAt` for every trapdoor and position set. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate TwoPermutationPrototype.RV64

theorem actual_data_base : dataBase (actual.image .opening)=tableBase := by
  rw [image_actual]; exact table_base_eq

theorem actual_data (k : Nat) (hk : k<65536) :
    (actual.image .opening).data[k]?.getD 0=BitVec.ofNat 8 (tableByte k) := by
  rw [image_actual]; exact table_data k hk

/-- The trusted loader leaves the embedded table at the top of memory. -/
theorem initial_table (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    TableAt (actual.initialState .opening (td,p)) := by
  intro e he h hh
  have card : p.card≤LENGTH := by simpa [Index] using Finset.card_le_univ p
  have big : 8*(tableWord e+h)+8≤2^36 := by simp only [tableWord, tableBase]; omega
  change (actual.initialState .opening (td,p)).getMem (BitVec.ofNat 64 (8*(tableWord e+h)))=_
  rw [initial_input_word actual .opening (td,p) _ (by omega)]
  have byte (j : Nat) (hj : j<8) :
      inputByte actual .opening (td,p) (8*(tableWord e+h)+j)=BitVec.ofNat 8 (tabEntry e h/2^(8*j)%256) := by
    have before : ¬ (trapdoorBase ≤ 8*(tableWord e+h)+j ∧
        8*(tableWord e+h)+j < trapdoorBase + (8 * trapdoorBytes + 7) / 8) := by
      norm_num [trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH, tableWord]
      omega
    have outside : ¬ (indicesBase ≤ 8*(tableWord e+h)+j ∧
        8*(tableWord e+h)+j < indicesBase + 8 * (p.sort (· ≤ ·)).length) := by
      rw [Finset.length_sort]
      norm_num [indicesBase, trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH, tableWord] at card ⊢
      omega
    have db : dataBase (actual.image .opening)≤8*(tableWord e+h)+j := by
      rw [actual_data_base]; simp only [tableWord, tableBase]; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      actual_layout.trapdoor, actual_layout.trapdoorSize, actual_layout.indices, before, outside, decide_false,
      List.find?_nil, Bool.false_eq_true, ite_false, if_pos db]
    rw [actual_data_base, actual_data _ (by simp only [tableWord, tableBase]; omega)]
    have k16 : (8*(tableWord e+h)+j-tableBase)/16=e := by simp only [tableWord, tableBase]; omega
    have k2 : (8*(tableWord e+h)+j-tableBase)/8%2=h := by simp only [tableWord, tableBase]; omega
    have k8 : (8*(tableWord e+h)+j-tableBase)%8=j := by simp only [tableWord, tableBase]; omega
    unfold tableByte
    rw [k16, k2, k8]
  rw [Finset.sum_congr rfl (fun j hj => by rw [byte j (Finset.mem_range.mp hj)])]
  have bytes : ∀ j ∈ Finset.range 8, (BitVec.ofNat 8 (tabEntry e h/2^(8*j)%256)).toNat*2^(8*j)=
      (tabEntry e h/2^(8*j)%256)*2^(8*j) := by
    intro j _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.mod_lt (tabEntry e h/2^(8*j)) (show 256>0 by decide); omega)]
  rw [Finset.sum_congr rfl bytes, bytes_reassemble _ (tab_entry_lt e h)]

end TwoPermutationPrototype.GroupedOpening
