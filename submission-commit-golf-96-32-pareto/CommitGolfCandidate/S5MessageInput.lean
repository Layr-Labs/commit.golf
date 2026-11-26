import CommitGolfCandidate.S5Initialize
import CommitGolfCandidate.S5SaltRead
import CommitGolfCandidate.S5LeafContents


namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev startState (m : Message) := Artifact.submission.initialState .commit m

theorem initial_entry (m : Message) (i : Index) :
    readBuffer (startState m) (msgAddr i) 256 = m i := by
  have h := i.isLt
  change i.val < 16777216 at h
  have bytes (j : Nat) (hj : j < 256) :
      (startState m).getByte (BitVec.ofNat 64 (msgAddr i+j)) = (m i).extractLsb' (8*(0+j)) 8 := by
    apply (initial_input_byte Artifact.submission .commit m (msgAddr i+j) (by unfold msgAddr; omega)).trans
    have low : 4096 ≤ msgAddr i + j := by unfold msgAddr; omega
    have high : msgAddr i + j < 4096 + 16777216*256 := by unfold msgAddr; omega
    have off : msgAddr i + j - 4096 = 256*i.val+j := by unfold msgAddr; omega
    have q : (256*i.val+j)/256 = i.val := by omega
    have r : (256*i.val+j)%256 = j := by omega
    unfold inputByte
    change (match [messageBuffer 4096 m].find? (fun b => decide
      (b.address ≤ msgAddr i+j ∧ msgAddr i+j < b.address+b.length)) with
      | some b => b.byteAt (msgAddr i+j-b.address)
      | none => _) = _
    simp only [List.find?_cons, messageBuffer, show LEAF_SIZE / 8 = 256 by decide,
      show LENGTH = 16777216 by decide, low, high, and_self, decide_true, if_true,
      off, q, r, show i.val < 16777216 from h, ↓reduceDIte, Fin.eta, Nat.zero_add]
  exact (read_serialized_slice _ (m i) _ 0 256 bytes).trans BitVec.extractLsb'_eq_self

end CommitGolfCandidate.S5Machine
