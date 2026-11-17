import CommitGolfCandidate.CapQueries

/-! Fixed-oracle outcomes and paid query counts for arbitrary cap transcripts,
including missing boundary hashes. No machine or security conclusions are assumed. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

/-- Failure retains the calls already spent, rather than refunding them. -/
def capCounted (compress : Compression) : {height : Nat} → CapView height → List Digest →
    Option (Digest × List Digest) × Nat
  | _, view, proof =>
      if capOccupied view then
        match view with
        | .leaf known => (known.map (fun value => (value, proof)), 0)
        | .node left right =>
            let (leftResult, leftCalls) := capCounted compress left proof
            match leftResult with
            | none => (none, leftCalls)
            | some (lroot, rest) =>
                let (rightResult, rightCalls) := capCounted compress right rest
                match rightResult with
                | none => (none, leftCalls + rightCalls)
                | some (rroot, rest') => (some (combine compress lroot rroot, rest'), leftCalls + rightCalls + 1)
      else (match proof with
        | [] => none
        | value :: rest => some (value, rest), 0)

/-- Explicit query reconstruction agrees with the paid deterministic interpreter. -/
theorem cap_counted_run (oracle : Oracle) {height : Nat} (view : CapView height)
    (proof : List Digest) :
    oracle.run (capDecodeQ view proof) = pure (capCounted oracle.compression view proof) := by
  induction view generalizing proof with
  | leaf known =>
      by_cases h : known.isSome = true <;>
        simp [capDecodeQ, capCounted, capOccupied, h, oracle_run_pure] <;> rfl
  | node left right ihLeft ihRight =>
      by_cases h : capOccupied (.node left right) = true
      · simp only [capDecodeQ, capCounted, h, ↓reduceIte]
        erw [oracle_run_bind, ihLeft]
        rcases hl : capCounted oracle.compression left proof with ⟨leftResult, leftCalls⟩
        simp only [pure_bind]
        cases leftResult with
        | none => simp [oracle_run_pure]
        | some pair =>
          rcases pair with ⟨lroot, rest⟩
          erw [oracle_run_bind, ihRight]
          rcases hr : capCounted oracle.compression right rest with ⟨rightResult, rightCalls⟩
          simp only [hr, pure_bind]
          cases rightResult with
          | none => simp [oracle_run_pure]
          | some pair =>
            rcases pair with ⟨rroot, rest'⟩
            erw [oracle_run_public_bind oracle (.inl _)]
            simp only [oracle_run_pure, pure_bind]
            simp [combine, Oracle.answer]
            exact ⟨rfl, by omega⟩
      · simp [capDecodeQ, capCounted, h, oracle_run_pure]
        rfl

/-- The paid interpreter returns exactly the canonical parser outcome on every proof. -/
theorem cap_counted_value (compress : Compression) {height : Nat} (view : CapView height)
    (proof : List Digest) :
    (capCounted compress view proof).1 = capDecode compress view proof := by
  induction view generalizing proof with
  | leaf known => by_cases h : known.isSome = true <;> simp [capCounted, capDecode, capOccupied, h] <;> rfl
  | node left right ihLeft ihRight =>
      by_cases h : capOccupied (.node left right) = true
      · simp only [capCounted, capDecode, h, ↓reduceIte]
        rw [← ihLeft proof]
        rcases capCounted compress left proof with ⟨leftResult, leftCalls⟩
        cases leftResult with
        | none => rfl
        | some pair =>
          rcases pair with ⟨lroot, rest⟩
          dsimp only
          change _ = (do
            let result ← capDecode compress right rest
            return (combine compress lroot result.1, result.2))
          rw [← ihRight rest]
          rcases capCounted compress right rest with ⟨rightResult, rightCalls⟩
          cases rightResult <;> rfl
      · simp [capCounted, capDecode, h]
        rfl

/-- Malformed proofs cannot exceed the complete shape's query ceiling. -/
theorem cap_counted_bound (compress : Compression) {height : Nat} (view : CapView height)
    (proof : List Digest) : (capCounted compress view proof).2 ≤ capCalls view := by
  induction view generalizing proof with
  | leaf known => by_cases h : known.isSome = true <;> simp [capCounted, capOccupied, h, capCalls]
  | node left right ihLeft ihRight =>
      by_cases h : capOccupied (.node left right) = true
      · have leftBound := ihLeft proof
        simp only [capCounted, capCalls, h, ↓reduceIte]
        rcases hl : capCounted compress left proof with ⟨leftResult, leftCalls⟩
        rw [hl] at leftBound
        cases leftResult with
        | none => simp only; omega
        | some pair =>
          rcases pair with ⟨lroot, rest⟩
          simp only [Prod.fst, Prod.snd]
          have rightBound := ihRight rest
          rcases hr : capCounted compress right rest with ⟨rightResult, rightCalls⟩
          rw [hr] at rightBound
          simp only [hr]
          cases rightResult <;> simp only <;> omega
      · simp [capCounted, capCalls, h]
end CommitGolfCandidate
