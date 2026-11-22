import CommitGolfCandidate.CapBStream
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening.CapB (carryBits flushBytes)

/-- The cap returned for an arbitrary trapdoor, including digests with nonzero padding. -/
def capRaw (ds : List D) := capBytes 0 ds

private theorem push_first (z : Word) (d : D) : push (emptyStream z) d=push (emptyStream 0) d := by
  have same : emittedWords 0 z d=emittedWords 0 0 d := by
    unfold emittedWords
    congr 1;funext i
    have h : i.val<3 := i.isLt
    simp only [nextWord,if_pos h]
  change Stream.mk 1 ([]++emittedWords 0 z d) _=Stream.mk 1 ([]++emittedWords 0 0 d) _
  rw [same];rfl

theorem capRaw_seed (z : Word) (ds : List D) : capBytes z ds=capRaw ds := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    have eq : stream z (d::ds)=stream 0 (d::ds) := by simp only [stream,List.foldl_cons,push_first z]
    simp only [capRaw,capBytes,eq]

theorem capRaw_length (ds : List D) : (capRaw ds).length=Layout2.Cap.size ds.length := byte_count _ _
end CommitGolfCandidate.CapB
