import CommitGolfCandidate.ReconstructedCheckRecordFrontier
import CommitGolfCandidate.ReconstructedCheckEpilogue
import CommitGolfCandidate.ReconstructedCheckLaunchGate

namespace CommitGolfCandidate.Reconstruction.CheckRecordClaims
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckRecorded CheckLayout CheckRecordABI
open CheckRecordSlots CheckRecordLedger CheckRecordDecision CheckRecordFrontier
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 11500
set_option maxHeartbeats 1200000

theorem reject (o : Oracle) (s : MachineState) (failure : Failure s) : CheckLaunchGate.Reject o 20 s := by
  obtain ⟨t,exitAt,entry,status,_⟩:=CheckEpilogue.positive o s CheckLayout.sp (by decide) (by decide) failure.pc failure.sp failure.saved
  exact CheckLaunchGate.extend exitAt (CheckLaunchGate.reject o t entry (status.trans failure.status))

theorem witness (o : Oracle) (input : CheckInput) (a : Slots) (rs all : List PublicRow) (s : MachineState)
    (h : Ledger o input input.positions.card a rs) (sh : Holds s a) (subset : rs⊆all)
    (rooted : ∀ i : Ordinal input,
      Binding.Path (history all) (oracleCompression o) 9 (CheckPath.dirs (index input i) 9) (unpack input.commitment)
        (CommitParents.cell s (4194304+32*slot input i))) :
    ∀ p : {k // k∈input.positions},Nonempty (Binding.Opening o p.val (input.values p) input.commitment all) := by
  intro p;obtain ⟨i,eq⟩:=exhaust input p
  obtain ⟨whereAt,auth⟩:=h.record i i.isLt
  have heap:=physical s (slot input i) _ (sh.words _ (hashRange _).2 _ whereAt)
  have upper:=rooted i;rw [heap] at upper
  have done:=auth all subset input.commitment upper
  change Nonempty (Binding.Opening o (position input i).val (input.values (position input i)) input.commitment all) at done
  simpa only [eq] using done

theorem calls (input : CheckInput) (rs qs : List PublicRow) (low : rs.length=84*input.positions.card) (hi : qs.length≤2303) :
    (rs++qs).length≤2^31 := by
  have b:=CheckLoader.positions_card_bound input.positions
  rw [List.length_append,low];omega

end CommitGolfCandidate.Reconstruction.CheckRecordClaims
