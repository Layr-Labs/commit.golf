import CommitGolfCandidate.Layout2ABI
import CommitGolfCandidate.GroupOpenModel

/-! Layout 2 opener: proofs as pure functions of a loaded state. `l2Proof` (V1's layout: the V1 phase writers'
blocks `writerByte`, the 6/4/2/0-byte flush, the cap footer) is the reference the honest bridge (`Layout2Area`)
converts; `l2Proof2` is what the V2a machine outputs (`v2Byte` blocks: the written dwords and the bytes the pass
left), `read_l2_proof`. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate Sampling
open CommitGolfCandidate.Layout2Phase (stride writerByte)
open QuartetOpening (proofLength)
open Opening (openingNodes)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-- Record `j`'s block. -/
def physRecord (loaded : MachineState) (positions : Positions) (j : Nat) : Proof :=
  (List.range (stride (j%4))).map (writerByte (j%4) (srcAt loaded positions j) (carryAt loaded positions j))

/-- The pending stream bytes after the last record. -/
def physFlush (loaded : MachineState) (positions : Positions) : Proof :=
  (List.range (flushLen ((positions.card+3)%4))).map
    (fun b => (carryAt loaded positions positions.card).extractLsb' (8*b) 8)

/-- The Layout 2 proof of a loaded state: the record blocks, the flush, the cap. -/
def l2Proof (loaded : MachineState) (positions : Positions) (cap : Proof) : Proof :=
  (List.range positions.card).flatMap (physRecord loaded positions) ++ physFlush loaded positions ++ cap

/-- The Layout 2 proof the opener outputs from a (virtual) trapdoor. -/
def l2ProofFromTrapdoor {s : Submission} (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions) : Proof :=
  l2Proof (s.initialState .opening (t, positions)) positions
    (foldNodes ((openingNodes positions).map (Opening.trapdoorHeap (s:=s) t)))

/-- V2a: record `j`'s block. -/
def physRecord2 (loaded pass : MachineState) (positions : Positions) (j : Nat) : Proof :=
  (List.range (stride (j%4))).map (v2Byte loaded pass positions j)

/-- V2a: the proof of a loaded state and the pass's state: the record blocks, the flush, the cap. -/
def l2Proof2 (loaded pass : MachineState) (positions : Positions) (cap : Proof) : Proof :=
  (List.range positions.card).flatMap (physRecord2 loaded pass positions) ++ physFlush loaded positions ++ cap

/-- V2a: the proof the opener outputs from the trapdoor and the state the pass left. -/
def l2ProofFromPass {s : Submission} (t : BitVec (8*s.sizes.trapdoor)) (pass : MachineState) (positions : Positions) :
    Proof :=
  l2Proof2 (s.initialState .opening (t, positions)) pass positions
    (foldNodes ((openingNodes positions).map (Opening.trapdoorHeap (s:=s) t)))

theorem dest_zero : destOf 0=proofBase := by unfold destOf Layout2Phase.phaseBase; simp

theorem dest_end (k : Nat) : destOf k+flushLen ((k+3)%4)=proofBase+534*k := by
  unfold destOf Layout2Phase.phaseBase flushLen
  split_ifs <;> omega

theorem records_read (loaded pass state : MachineState) (positions : Positions)
    (lower : L2Bytes loaded pass positions state positions.card) :
    ∀ n, n ≤ positions.card →
      bytesAt state proofBase (destOf n-proofBase)=(List.range n).flatMap (physRecord2 loaded pass positions) := by
  intro n
  induction n with
  | zero => intro _; rw [dest_zero, Nat.sub_self]; rfl
  | succ n ih =>
    intro hn
    have lo := (dest_bound n).1
    have step := dest_next n
    rw [show destOf (n+1)-proofBase=(destOf n-proofBase)+stride (n%4) by omega, bytes_at_append, ih (by omega),
      List.range_succ, List.flatMap_append, List.flatMap_singleton]
    congr 1
    unfold bytesAt physRecord2
    apply List.map_congr_left
    intro b hb
    have hb' := List.mem_range.mp hb
    rw [show proofBase+(destOf n-proofBase)+b=destOf n+b by omega]
    exact lower n (by omega) b hb'

/-- The decoded output of the V2a opener. -/
theorem read_l2_proof (s : Submission) (abi : L2ABI s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (pass : MachineState) (result : Execution)
    (physical : L2OpenPhysical s trapdoor positions pass result) :
    s.readProof result = l2ProofFromPass (s := s) trapdoor pass positions := by
  have fit : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    exact (QuartetOpening.capacity_all positions).trans abi.capacity
  have success : s.openingSucceeded result = true := by
    simp [Submission.openingSucceeded, physical.success, fit]
  simp only [Submission.readProof, success, ite_true, physical.length, abi.toOpeningLayout.proof]
  change bytesAt result.state proofBase (proofLength positions) = _
  have lo := (dest_bound positions.card).1
  have fl := dest_end positions.card
  have split : proofLength positions =
      (destOf positions.card-proofBase)+flushLen ((positions.card+3)%4)+capOffset (openingNodes positions).length := by
    unfold proofLength capOffset
    omega
  rw [split, bytes_at_append, bytes_at_append, records_read _ _ _ positions physical.lower _ (Nat.le_refl _)]
  unfold l2ProofFromPass l2Proof2
  congr 2
  · unfold bytesAt physFlush
    apply List.map_congr_left
    intro b hb
    rw [show proofBase+(destOf positions.card-proofBase)+b=destOf positions.card+b by omega]
    exact physical.flush b (List.mem_range.mp hb)
  · rw [show proofBase+(destOf positions.card-proofBase+flushLen ((positions.card+3)%4))=recordBase positions.card by
      unfold recordBase recordBytes; omega]
    exact physical.footer

end TwoPermutationPrototype.GroupedOpening.Layout2
