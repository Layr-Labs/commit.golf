import CommitGolfCandidate.ReconstructedCheckCapPaths
import CommitGolfCandidate.ReconstructedCheckRecordFrontier

namespace CommitGolfCandidate.Reconstruction.CheckCapRooted
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckCapLevel CheckCapIterate CheckRecordABI
open CheckRecordSlots CheckRecordLedger
open TwoPermutationPrototype.Sampling

/-- Every lower record's saved node has a full upper authentication path in
the public oracle history of an accepting checker. -/
theorem rooted {o : Oracle} (input : CheckInput) {c endC : Nat} {s u t : MachineState} {qs all : List PublicRow}
    (mem : u.mem=s.mem) (trail : Trail o (CapEntry.flags input.positions) (Wire.unpackBytes input.proof) 9 c u (some endC) t qs)
    (root : node t 1=unpack input.commitment) (sub : qs⊆all) (i : Ordinal input) :
    Binding.Path (history all) (oracleCompression o) 9 (CheckPath.dirs (index input i) 9)
      (unpack input.commitment) (CommitParents.cell s (4194304+32*slot input i)) := by
  have bounds:=hashRange (index input i)
  change 512≤slot input i ∧ slot input i<1024 at bounds
  have eq : slot input i=512+(slot input i-512):=by omega
  have active:=(CheckRecordFrontier.flags input (slot input i-512) (by omega)).mpr ⟨i,eq⟩
  have live : Live (CapEntry.flags input.positions) 9 (CheckWalkValues.heap (index input i) 9)=true:=active
  have path:=CheckCapPaths.paths trail rfl (by decide) (index input i) live all sub
  rw [root] at path
  change Binding.Path _ _ _ _ _ (CommitParents.cell u (4194304+32*slot input i)) at path
  rwa [CommitParents.cell_congr mem] at path

end CommitGolfCandidate.Reconstruction.CheckCapRooted
