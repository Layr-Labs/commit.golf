import CommitGolfCandidate.CapBRaw
import CommitGolfCandidate.Layout2Memory
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open TwoPermutationPrototype.GroupedOpening.CapB (flushBytes)
set_option maxHeartbeats 1400000

abbrev WritesList (s t : MachineState) (b : Nat) (xs : List Byte) :=
  Layout2.Writes s t b xs.length (fun i=>xs[i]?.getD 0)

theorem joinWrites {s u t b xs ys} (first : WritesList s u b xs) (second : WritesList u t (b+xs.length) ys) :
    WritesList s t b (xs++ys) := by
  intro q hq;rw [second q hq,first q hq,List.length_append]
  dsimp only
  split_ifs <;> first | omega | rfl | (rw [List.getElem?_append_left (by omega)]) |
    (rw [List.getElem?_append_right (by omega)];congr 2 <;> omega)

theorem flatWordLength (ws : List Word) : (ws.flatMap wordBytes).length=8*ws.length := by
  induction ws with | nil=>rfl | cons w ws ih=>simp [wordBytes,List.flatMap_cons,ih,Nat.mul_add]
theorem flatWordGet (ws : List Word) (i j : Nat) (hi : i<ws.length) (hj : j<8) :
    (ws.flatMap wordBytes)[8*i+j]?.getD 0=extractByte (ws.getD i 0) j := by
  induction ws generalizing i with
  | nil=>simp at hi
  | cons w ws ih=>
    rw [List.flatMap_cons]
    have len : (wordBytes w).length=8 := by simp [wordBytes]
    cases i with
    | zero=>simp only [Nat.mul_zero,Nat.zero_add];rw [List.getElem?_append_left (by omega)]
            interval_cases j <;> rfl
    | succ i=>rw [List.getElem?_append_right (by omega),len,show 8*(i+1)+j-8=8*i+j by omega,ih _ (by simpa using hi)]
              rfl

theorem Buffer.bytes {s t b ws} (h : Buffer s t b ws) (aligned : b%8=0) (room : b+8*ws.length≤MEMORY_BYTES) :
    WritesList s t b (ws.flatMap wordBytes) := by
  intro q hq
  rw [flatWordLength]
  have lim : MEMORY_BYTES<2^64 := by decide
  by_cases span : b≤q ∧ q<b+8*ws.length
  · rw [if_pos span]
    let i:=(q-b)/8;let j:=(q-b)%8
    have hi : i<ws.length := by dsimp [i];omega
    have hj : j<8 := by dsimp [j];omega
    have offset : q-b=8*i+j := by dsimp [i,j];omega
    have dest : q=(b+8*i)+j := by omega
    dsimp only
    rw [offset,flatWordGet _ _ _ hi hj]
    change gbyte t q=_
    rw [dest,byte_word _ _ _ (by omega) hj (by omega),h.word _ hi]
  · rw [if_neg span]
    unfold Layout2.byte MachineState.getByte
    rw [h.frame _ (by rw [align_nat _ (by omega)];omega)]

theorem carryWrites {s t b n v} (width : n≤8) (write : Layout2.Writes s t b n (extractByte v)) :
    WritesList s t b ((wordBytes v).take n) := by
  intro q hq;rw [write q hq,List.length_take,show (wordBytes v).length=8 by simp [wordBytes],Nat.min_eq_left width]
  split <;> rename_i span
  · dsimp only
    have h : q-b<n := by omega
    rw [List.getElem?_take_of_lt h]
    unfold wordBytes;rw [List.getElem?_eq_getElem (by simp;omega),Option.getD_some,List.getElem_ofFn]
  · rfl
end CommitGolfCandidate.CapB
