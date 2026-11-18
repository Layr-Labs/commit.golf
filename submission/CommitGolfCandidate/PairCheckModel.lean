import CommitGolfCandidate.PairLeafModel
import CommitGolfCandidate.QuartetCertificate
import CommitGolfCandidate.QuartetConcrete

/-!
# Pair-heads checker interface

`PairCheckerFacts` is `QuartetCertificate.CheckerFacts` with the honest check input built from the pair-heads leaf
digests (`pairHonestView`). Target for the checker lane (see `stack/PAIRHEADS-CHECK.md`):
`pair_checker_facts (bound : Sampling.PairReplayBound) : PairCheckerFacts s` for the submission(s) carrying the frozen
pair-heads check image (`stack/image/programs-ph-frozen.json`, `images.check`, 543 words).
-/

namespace TwoPermutationPrototype.PairCertificate
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp TwoPermutationPrototype.Sampling

def pairHonestCheckInput (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) : CheckInput :=
  let view := Quartet.pairHonestView Quartet.builder oracle.compression
    (BiPermutation.equiv Block oracle.permutation) message positions salts
  ⟨view.1, positions, message.restrict positions, view.2⟩

structure PairCheckerFacts (s : Submission) : Prop where
  terminates : ∀ oracle input, (Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished
  queryBudget : ∀ oracle input, (Checker.checkObservation s oracle input).2 ≤ 100*input.positions.card
  binding : s.scheme.Binding
  honestAccepted : ∀ oracle message positions salts,
    (Checker.checkObservation s oracle (pairHonestCheckInput oracle message positions salts)).1.1.exit = .success

end TwoPermutationPrototype.PairCertificate
