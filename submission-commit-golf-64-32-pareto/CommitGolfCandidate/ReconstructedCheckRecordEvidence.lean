import CommitGolfCandidate.ReconstructedCheckRecordFlight

namespace CommitGolfCandidate.Reconstruction.CheckRecordEvidence
open CommitGolf CommitGolf.Riscv Binding CheckWalkValues CheckRecordSpec
open TwoPermutationPrototype TwoPermutationPrototype.Sampling
set_option maxRecDepth 9500
set_option maxHeartbeats 850000

def Evidence (o : Oracle) (idx : Index) (value : Entry) (cap : Binding.Digest) (record : List PublicRow) :=
  ∀ all : List PublicRow,record⊆all→∀ root : Commitment,
    Binding.Path (history all) (oracleCompression o) 9 (CheckPath.dirs idx 9) (unpack root) cap →
      Nonempty (Binding.Opening o idx value root all)

theorem lift (o : Oracle) (idx : Index) (value : Entry) (bits c : Nat)
    (h : CheckWalk.Lifts o idx (lower o idx bits c (entryWords value)).2 24 (leaf o idx bits c (entryWords value))
      (lower o idx bits c (entryWords value)).1.node) :
    Evidence o idx value (lower o idx bits c (entryWords value)).1.node (rows o idx bits c (entryWords value)) := by
  intro all included root upper
  let n:=CheckRecordHeader.salt bits c
  let m:=entryWords value
  have path:=h all (fun _ e=>included (List.mem_append_right _ e)) (unpack root) upper
  have dirs : CheckPath.dirs idx 24=route idx:=by simp only [CheckPath.dirs,route,show 24-24=0 by decide,show List.range' 0 24=List.range 24 by decide]
  rw [dirs] at path
  refine ⟨n,?_,?_,path⟩
  · apply included;apply List.mem_append_left;exact List.mem_cons_self
  · apply included;apply List.mem_append_left;exact List.mem_cons_of_mem _ List.mem_cons_self

theorem mono {o : Oracle} {idx : Index} {v : Entry} {cap : Binding.Digest} {r s : List PublicRow}
    (h : Evidence o idx v cap r) (extend : r⊆s) : Evidence o idx v cap s :=
  fun all more root up=>h all (fun _ x=>more (extend x)) root up

end CommitGolfCandidate.Reconstruction.CheckRecordEvidence
