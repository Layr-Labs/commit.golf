import CommitGolf
import CommitGolf.Oracle.Tests
import CommitGolfCandidate.Permutation.MerkleProof.Certificate
import CommitGolfCandidate.Compression.CompressionProof.Certificate
import Std.Tactic.BVDecide

/-! # Regression tests

The constants' values; runs of the Merkle baseline on an 8-leaf tree and of its `check` at full
depth; the fact, assumed by the statements, that VCVio computations never fail; and the axioms of
the baseline's certificate. -/

namespace CommitGolf.Tests
open OracleComp OracleSpec Baseline

/-! ### Constants -/

example : LENGTH = 16777216 := by decide
-- A Merkle compression leaves 1088 bits of capacity once two digests fill the state.
example : WIDTH - 2 * DIGEST_BITS = 1088 := by decide
example : COMMIT_BUDGET = 1677721600 ∧ OPEN_BUDGET BATCH = 10000 ∧ CHECK_BUDGET BATCH = 10000 := by
  decide
-- The baseline's scores: unpruned Merkle paths for `BATCH` positions.
example : BATCH * LOG_LENGTH * DIGEST_BYTES = 76800 ∧ BATCH * LOG_LENGTH = 2400 := by decide

/-! ### The baseline on a small tree -/

/-- A toy permutation, only for running code: XOR bits 256–511, rotated by one, into bits 0–255.
It leaves bits 256–511 unchanged, so it is an involution. It gives `C(L, R) = R ⊕ rotl₁ L`, which
depends on the order of the children. -/
private def mix (x : BitVec 1600) : BitVec 1600 :=
  x ^^^ (((x >>> 256).setWidth 256).rotateLeft 1).setWidth 1600

private theorem mix_mix (x : BitVec 1600) : mix (mix x) = x := by
  simp only [mix]; bv_decide

private def toyPerm : Perm := Function.Involutive.toPerm mix mix_mix

private def toyLeaves : List Digest := (List.range 8).map fun i => BitVec.ofNat DIGEST_BITS (i + 1)
private def toyTree : List (List Digest) := (toyPerm.eval (layers 3 toyLeaves)).1

-- The compression depends on the order of the children.
#guard (toyPerm.eval (compress 3 5)).1 != (toyPerm.eval (compress 5 3)).1

-- An 8-leaf tree has layers of sizes 8, 4, 2, 1, built with 7 compressions.
#guard toyTree.map List.length == [8, 4, 2, 1]
#guard (toyPerm.eval (layers 3 toyLeaves)).2 == 7

-- Every honest path climbs back to the root, with one compression per level.
#guard (List.range 8).all fun i =>
  let (root, calls) := toyPerm.eval (climb i (toyLeaves.getD i 0) (copath toyTree 3 i))
  root == rootOf toyTree && calls == 3

-- A wrong leaf value does not climb to the root.
#guard (List.range 8).all fun i =>
  (toyPerm.eval (climb i (toyLeaves.getD i 0 + 1) (copath toyTree 3 i))).1 != rootOf toyTree

-- Digests round-trip through their byte encoding.
#guard (Digest.ofBytes (Digest.toBytes (BitVec.ofNat DIGEST_BITS 0xdeadbeef))) ==
  BitVec.ofNat DIGEST_BITS 0xdeadbeef
#guard (Digest.toBytes (BitVec.ofNat DIGEST_BITS 0xdeadbeef)).length == DIGEST_BYTES

/-! ### `check` at full depth -/

private def sibs : List Digest := (List.range LOG_LENGTH).map fun k => BitVec.ofNat _ (1000 + k)
private def leaf : Digest := 7
private def rt : Commitment := (toyPerm.eval (climb 5 leaf sibs)).1
private def pf : Proof := sibs.flatMap Digest.toBytes
private def I : Positions := {⟨5, by decide⟩}

-- `check` accepts a valid path with `LOG_LENGTH` calls, and rejects a wrong length or value.
#guard toyPerm.eval (merkle.check rt I (fun _ => leaf) pf) == (true, LOG_LENGTH)
#guard toyPerm.eval (merkle.check rt I (fun _ => leaf) (pf ++ [0])) == (false, 0)
#guard !(toyPerm.eval (merkle.check rt I (fun _ => leaf + 1) pf)).1

/-! ### VCVio computations never fail

Statements 1–4 are stated as probability `1`. That reads as "always" only because
computations in the pinned VCVio cannot fail: no probability mass is lost to failure. A VCVio update
that added failure to `OracleComp` would break these checks. -/

example {α : Type} (c : ProbComp α) : Pr[⊥ | c] = 0 := probFailure_eq_zero
example (scheme : Scheme) (π : scheme.oracles.Realization) (m : Message) (I : Positions) :
    Pr[⊥ | scheme.honest π m I] = 0 := probFailure_eq_zero
example (adversary : Scheme.Adversary) : Pr[⊥ | Scheme.bindingGame adversary] = 0 :=
  probFailure_eq_zero

/-! ### The baseline's certificate

`merkle_certificate` proves `Certificate merkle 76800 2400`. Its transitive axioms must be exactly
the three the rules allow; `#guard_msgs` fails the build otherwise (in particular on `sorryAx`). -/

/-- info: 'CommitGolf.Baseline.merkle_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms merkle_certificate

/-! ### Compression baseline execution -/

private def toyHash (x : CompressionBaseline.Input) : CompressionBaseline.Digest :=
  x.setWidth DIGEST_BITS ^^^ ((x >>> DIGEST_BITS).setWidth DIGEST_BITS).rotateLeft 1
private def compressionTree :=
  (CompressionBaseline.Hash.eval toyHash (CompressionBaseline.layers 3 toyLeaves)).1

#guard compressionTree.map List.length == [8, 4, 2, 1]
#guard (CompressionBaseline.Hash.eval toyHash (CompressionBaseline.layers 3 toyLeaves)).2 == 7
#guard (List.range 8).all fun i =>
  let (root, calls) := CompressionBaseline.Hash.eval toyHash
    (CompressionBaseline.climb i (toyLeaves.getD i 0) (CompressionBaseline.copath compressionTree 3 i))
  root == CompressionBaseline.rootOf compressionTree && calls == 3
#guard (List.range 8).all fun i =>
  (CompressionBaseline.Hash.eval toyHash
    (CompressionBaseline.climb i (toyLeaves.getD i 0 + 1)
      (CompressionBaseline.copath compressionTree 3 i))).1 != CompressionBaseline.rootOf compressionTree

/-- info: 'CommitGolf.CompressionBaseline.merkle_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompressionBaseline.merkle_certificate

end CommitGolf.Tests

-- The unified game preserves finite-domain binding without additional axioms.
/-- info: 'CommitGolf.Scheme.bindingProbability_eq_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CommitGolf.Scheme.bindingProbability_eq_finite
