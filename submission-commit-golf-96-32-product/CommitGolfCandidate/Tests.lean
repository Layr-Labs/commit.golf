import CommitGolfCandidate.Model

/-! Executable small-tree regression tests. Fixed coins and a toy compression function
make these deterministic; they are not a statistical-security proof. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec Riscv

private def testCompression (x : BitVec COMPRESSION_INPUT_LENGTH) : BitVec 256 :=
  x.extractLsb' 0 256 * 5 + x.extractLsb' 256 256 + 1
private def testOracle : Oracle := ⟨testCompression, Equiv.refl _⟩
private def fixedCoins : QueryImpl World Id
  | .inl n => pure (⟨n / 2, by omega⟩ : Fin (n + 1))
  | .inr q => testOracle.answer q
private def run {α : Type} (computation : OracleComp World α) : α :=
  Id.run (simulateQ fixedCoins computation)
private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

#eval do
  for depth in [1, 2, 3] do
    let s := candidate depth
    let message : Message := fun i => BitVec.ofNat LEAF_SIZE (∑ j ∈ Finset.range 8, (123 + i.val + j * 17) * 2^(256*j))
    let committed := run (s.run .commit message)
    ensure "commit must halt successfully" (committed.exit == Exit.success)
    let c := capLog depth
    let k := capCount depth
    ensure "commit query count" (committed.oracleCalls == 4 * 2^depth + (2^depth - k) + k / 2)
    let (root, trapdoor) := s.readCommit committed
    let salt := fun i => trapdoor.extractLsb' (8 * (96 * 2^depth + 32*i)) 256
    let leaves := (List.range (2^depth)).map fun i =>
      leafDigest testOracle.compression (salt i) (message ⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩)
    let tree := layers testOracle.compression depth leaves
    let cap : Nat → Digest := fun m => (tree[depth - c]?.getD [])[m]?.getD 0
    let chained := (List.range (k / 2)).foldl
      (fun state pair => absorb testOracle.compression state (capBlock cap pair)) 0
    ensure "machine commitment is the chain over the reference cap" (root == chained)
    let choices : List Positions := [∅, {(⟨0, by decide⟩ : Index)},
      (Finset.range (2^depth)).filter (fun i => i % 2 = 1) |>.image
        (fun i => (⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩ : Index)),
      (Finset.range (2^depth)).image (fun i => (⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩ : Index))]
    for positions in choices do
      let opened := run (s.run .opening (trapdoor, positions))
      ensure "opening must halt successfully" (s.openingSucceeded opened)
      ensure "opening makes no public queries" (opened.oracleCalls == 0)
      let proof := s.readProof opened
      let records := (positions.sort (· ≤ ·)).flatMap fun (i : Index) =>
        referenceProof tree (depth - c) i.val (salt i.val)
      let expected := ((List.range k).flatMap fun m => digestBytes (cap m)) ++ records
      ensure "machine proof agrees with pure reference" (proof == expected)
      ensure "opening length" (proof.length == proofBytes depth positions.card)
      let checked := run (s.run .check ⟨root, positions, message.restrict positions, proof⟩)
      ensure "honest proof must verify" (checked.exit == Exit.success)
      ensure "checker query count" (checked.oracleCalls ==
        positions.card * (4 + depth - c) + (if positions.card > 0 then k / 2 else 0))
      if positions.card > 0 then
        let badValues : Values positions := fun i => message i + 1
        ensure "changed values must reject"
          ((run (s.run .check ⟨root, positions, badValues, proof⟩)).exit == Exit.failure)
        ensure "short proof must reject"
          ((run (s.run .check ⟨root, positions, message.restrict positions, proof.drop 1⟩)).exit == Exit.failure)
        let altered := match proof with
          | [] => []
          | byte :: rest => (byte ^^^ 1) :: rest
        ensure "altered cap must reject"
          ((run (s.run .check ⟨root, positions, message.restrict positions, altered⟩)).exit == Exit.failure)
        ensure "changed root must reject"
          ((run (s.run .check ⟨root + 1, positions, message.restrict positions, proof⟩)).exit == Exit.failure)
    let empty : Positions := ∅
    ensure "checker rejects truncated fuel"
      ((run ({ s with steps := fun _ => 1 }.run .check ⟨root, empty, message.restrict empty, []⟩)).exit == Exit.unfinished)
    IO.println s!"depth {depth}: commit cycles={committed.cycles}, queries={committed.oracleCalls}"

end CommitGolfCandidate
