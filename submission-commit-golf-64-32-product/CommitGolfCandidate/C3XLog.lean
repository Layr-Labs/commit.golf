import CommitGolfCandidate.C3WitnessCore
import CommitGolfCandidate.S3PermBridge

/-! # The marked run of a program, for the cross-oracle permutation event

`C3PermWitness` ties a permutation row to a compression reply (the `c3T3Field` of the
permutation input). `markedRows program` follows every compression call with reply `c` by one
forward permutation call on `c3Marker c`, and `scan` scans the log oldest-first while tracking
the inverse-target collision flag. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

set_option autoImplicit false
set_option exponentiation.threshold 2100

/-- The marker input of a compression reply: the reply in the low 256 bits. -/
def c3Marker (reply : BitVec 256) : Block := BitVec.ofNat PERMUTATION_WIDTH reply.toNat

theorem c3_marker_injective : Function.Injective c3Marker := by
  intro a b same
  have ha := a.isLt
  have hb := b.isLt
  have h := congrArg BitVec.toNat same
  simp only [c3Marker, BitVec.toNat_ofNat, PERMUTATION_WIDTH] at h
  apply BitVec.eq_of_toNat_eq
  omega

/-- One call of the marked run. A compression row also carries the reply of the marker call that
follows it. An inverse row lists the returned input first, like `PublicRow.permutation`. -/
inductive MarkedRow where
  | compression (input : BitVec COMPRESSION_INPUT_LENGTH) (reply : BitVec 256) (mark : Block)
  | forward (input reply : Block)
  | inverse (input output : Block)

/-- The row `recordRows` records for the same call. -/
def MarkedRow.erase : MarkedRow → PublicRow
  | .compression input reply _ => .compression input reply
  | .forward input reply => .permutation input reply
  | .inverse input output => .permutation input output

/-- Run `program`, calling the permutation on `c3Marker c` after every compression reply `c`, and
return the calls in order. -/
def markedRows {α : Type} (program : OracleComp World α) : OracleComp World (α × List MarkedRow) :=
  OracleComp.recOn (motive := fun _ => OracleComp World (α × List MarkedRow)) program
    (fun value => pure (value, []))
    (fun query _ next =>
      match query, next with
      | .inl coins, next =>
          (liftM (World.query (.inl coins)) : OracleComp World _) >>= next
      | .inr (.inl input), next =>
          (liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= fun reply =>
            (liftM (World.query (.inr (.inr (.inl (c3Marker reply))))) : OracleComp World _) >>=
              fun mark => (fun result : α × List MarkedRow =>
                (result.1, MarkedRow.compression input reply mark :: result.2)) <$> next reply
      | .inr (.inr (.inl input)), next =>
          (liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World _) >>= fun reply =>
            (fun result : α × List MarkedRow =>
              (result.1, MarkedRow.forward input reply :: result.2)) <$> next reply
      | .inr (.inr (.inr output)), next =>
          (liftM (World.query (.inr (.inr (.inr output)))) : OracleComp World _) >>= fun answer =>
            (fun result : α × List MarkedRow =>
              (result.1, MarkedRow.inverse answer output :: result.2)) <$> next answer)

theorem marked_rows_pure {α : Type} (value : α) :
    markedRows (pure value : OracleComp World α) = pure (value, []) := rfl

theorem marked_rows_coins {α : Type} (coins : unifSpec.Domain)
    (next : unifSpec.Range coins → OracleComp World α) :
    markedRows ((liftM (World.query (.inl coins)) : OracleComp World _) >>= next) =
      ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun answer =>
        markedRows (next answer)) := rfl

theorem marked_rows_compress {α : Type} (input : BitVec COMPRESSION_INPUT_LENGTH)
    (next : BitVec COMPRESSION_OUTPUT_LENGTH → OracleComp World α) :
    markedRows ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= next) =
      ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= fun reply =>
        (liftM (World.query (.inr (.inr (.inl (c3Marker reply))))) : OracleComp World _) >>=
          fun mark => (fun result : α × List MarkedRow =>
            (result.1, MarkedRow.compression input reply mark :: result.2)) <$>
              markedRows (next reply)) := rfl

theorem marked_rows_permute {α : Type} (input : Block) (next : Block → OracleComp World α) :
    markedRows ((liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World _) >>= next) =
      ((liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World _) >>= fun reply =>
        (fun result : α × List MarkedRow =>
          (result.1, MarkedRow.forward input reply :: result.2)) <$> markedRows (next reply)) := rfl

theorem marked_rows_inverse {α : Type} (output : Block) (next : Block → OracleComp World α) :
    markedRows ((liftM (World.query (.inr (.inr (.inr output)))) : OracleComp World _) >>= next) =
      ((liftM (World.query (.inr (.inr (.inr output)))) : OracleComp World _) >>= fun answer =>
        (fun result : α × List MarkedRow =>
          (result.1, MarkedRow.inverse answer output :: result.2)) <$> markedRows (next answer)) := rfl

/-- For one fixed oracle the marked run records the rows of the plain run. -/
theorem marked_rows_erase (oracle : Oracle) {α : Type} (program : OracleComp World α) :
    (fun result : α × List MarkedRow => (result.1, result.2.map MarkedRow.erase)) <$>
        fixedOracleRun oracle (markedRows program) =
      fixedOracleRun oracle (recordRows program) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
    rw [marked_rows_pure, record_rows_pure, fixed_oracle_run_pure, fixed_oracle_run_pure]
    rfl
  | query_bind query next ih =>
    rw [record_rows_query]
    rcases query with coins | input | input | output
    · rw [marked_rows_coins, fixed_oracle_run_private, fixed_oracle_run_private, map_bind]
      refine bind_congr fun answer => ?_
      rw [fixed_oracle_run_map, ← ih answer, Functor.map_map]
      rfl
    · rw [marked_rows_compress, fixed_oracle_run_public, fixed_oracle_run_public,
        fixed_oracle_run_public, fixed_oracle_run_map, fixed_oracle_run_map, ← ih, Functor.map_map,
        Functor.map_map]
      rfl
    · rw [marked_rows_permute, fixed_oracle_run_public, fixed_oracle_run_public,
        fixed_oracle_run_map, fixed_oracle_run_map, ← ih, Functor.map_map, Functor.map_map]
      rfl
    · rw [marked_rows_inverse, fixed_oracle_run_public, fixed_oracle_run_public,
        fixed_oracle_run_map, fixed_oracle_run_map, ← ih, Functor.map_map, Functor.map_map]
      rfl

/-- A bound on the public calls of the recorded program is a bound for the program. -/
theorem public_bound_of_record_rows {α : Type} {program : OracleComp World α} {budget : Nat}
    (bounded : PublicQueryBound (recordRows program) budget) : PublicQueryBound program budget := by
  have erased := (isQueryBound_map_iff (recordRows program) Prod.fst budget _ _).mpr bounded
  rwa [record_rows_erase] at erased

/-! ### Reading a marked log -/

structure ScanState where
  rows : List PublicRow
  seen : List (BitVec 256)
  targets : List (BitVec 256)
  flag : Prop

def ScanState.init : ScanState := ⟨[], [], [], False⟩

def scanStep (state : ScanState) : MarkedRow → ScanState
  | .compression input reply _ =>
      ⟨.compression input reply :: state.rows, reply :: state.seen, state.targets,
        state.flag ∨ (reply ∉ state.seen ∧ reply ∈ state.targets)⟩
  | .forward input reply =>
      ⟨.permutation input reply :: state.rows, state.seen, state.targets, state.flag⟩
  | .inverse input output =>
      ⟨.permutation input output :: state.rows, state.seen, c3T3Field input :: state.targets,
        state.flag⟩

def scan (state : ScanState) (log : List MarkedRow) : ScanState := log.foldl scanStep state

theorem scan_nil (state : ScanState) : scan state [] = state := rfl

theorem scan_cons (state : ScanState) (row : MarkedRow) (log : List MarkedRow) :
    scan state (row :: log) = scan (scanStep state row) log := rfl

theorem scan_step_rows (state : ScanState) (row : MarkedRow) :
    (scanStep state row).rows = row.erase :: state.rows := by
  cases row <;> rfl

theorem scan_rows_mem (state : ScanState) (log : List MarkedRow) (row : PublicRow)
    (present : row ∈ log.map MarkedRow.erase) : row ∈ (scan state log).rows := by
  have general : ∀ (log : List MarkedRow) (state : ScanState),
      (row ∈ state.rows ∨ row ∈ log.map MarkedRow.erase) → row ∈ (scan state log).rows := by
    intro log
    induction log with
    | nil =>
      intro state h
      rcases h with h | h
      · exact h
      · simp at h
    | cons head tail ih =>
      intro state h
      rw [scan_cons]
      apply ih
      rw [scan_step_rows]
      rcases h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rw [List.map_cons] at h
        rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h
  exact general log state (Or.inr present)

theorem scan_witness (log : List MarkedRow) (witness : C3PermWitness (log.map MarkedRow.erase)) :
    C3PermWitness (scan ScanState.init log).rows :=
  witness.mono fun row present => scan_rows_mem ScanState.init log row present

end CommitGolfCandidate
