import CommitGolfCandidate.Model

/-! Executable small-tree regression tests. Fixed coins and a toy compression function
make these deterministic; they are not a statistical-security proof. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec Riscv

private def testCompression (x : BitVec 512) : BitVec 256 :=
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
  for depth in [0, 1, 2, 3] do
    let s := candidate depth
    let message : Message := fun i => BitVec.ofNat LEAF_SIZE (∑ j ∈ Finset.range 8, (123 + i.val + j * 17) * 2^(256*j))
    let committed := run (s.run .commit message)
    ensure "commit must halt successfully" (committed.exit == Exit.success)
    ensure "commit query count" (committed.oracleCalls == 9 * 2^depth - 1)
    let (root, trapdoor) := s.readCommit committed
    let salt := fun i => trapdoor.extractLsb' (8 * (64 * 2^depth + 32*i)) 256
    let leaves := (List.range (2^depth)).map fun i =>
      leafDigest testOracle.compression (salt i) (message ⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩)
    let tree := layers testOracle.compression depth leaves
    ensure "machine root agrees with pure reference"
      (root == (tree.getLast?.getD []).head?.getD 0)
    let choices : List Positions := [∅, {(⟨0, by decide⟩ : Index)},
      (Finset.range (2^depth)).filter (fun i => i % 2 = 1) |>.image
        (fun i => (⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩ : Index)),
      (Finset.range (2^depth)).image (fun i => (⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩ : Index))]
    for positions in choices do
      let opened := run (s.run .opening (trapdoor, positions))
      ensure "opening must halt successfully" (s.openingSucceeded opened)
      ensure "opening makes no public queries" (opened.oracleCalls == 0)
      let proof := s.readProof opened
      let expected := (positions.sort (· ≤ ·)).flatMap fun (i : Index) => referenceProof tree depth i.val (salt i.val)
      ensure "machine proof agrees with pure reference" (proof == expected)
      ensure "opening length" (proof.length == positions.card * openingBytes depth)
      let checked := run (s.run .check ⟨root, positions, message.restrict positions, proof⟩)
      ensure "honest proof must verify" (checked.exit == Exit.success)
      ensure "checker query count" (checked.oracleCalls == positions.card * (8 + depth))
      if positions.card > 0 then
        let badValues : Values positions := fun i => message i + 1
        ensure "changed values must reject"
          ((run (s.run .check ⟨root, positions, badValues, proof⟩)).exit == Exit.failure)
        ensure "short proof must reject"
          ((run (s.run .check ⟨root, positions, message.restrict positions, proof.drop 1⟩)).exit == Exit.failure)
        let altered := match proof with
          | [] => []
          | byte :: rest => (byte ^^^ 1) :: rest
        ensure "altered salt must reject"
          ((run (s.run .check ⟨root, positions, message.restrict positions, altered⟩)).exit == Exit.failure)
        ensure "changed root must reject"
          ((run (s.run .check ⟨root + 1, positions, message.restrict positions, proof⟩)).exit == Exit.failure)
    let empty : Positions := ∅
    ensure "checker rejects truncated fuel"
      ((run ({ s with steps := fun _ => 1 }.run .check ⟨root, empty, message.restrict empty, []⟩)).exit == Exit.unfinished)
    IO.println s!"depth {depth}: commit cycles={committed.cycles}, queries={committed.oracleCalls}"

end CommitGolfCandidate
