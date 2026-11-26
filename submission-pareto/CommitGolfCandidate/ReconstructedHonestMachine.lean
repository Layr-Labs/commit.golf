import CommitGolfCandidate.Execution
import CommitGolfCandidate.ReconstructedFetch

namespace CommitGolfCandidate.Reconstruction.HonestMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- A list of (instruction-word index, decoded ordinary instruction) pairs. -/
abbrev Trace := List (Nat × Instr)

/-- Guard against system calls and pseudo-instructions rejected by ordinaryStep. -/
private def ordinary : Instr → Bool
  | .ECALL | .EBREAK | .CSRS .. | .LI .. | .MV .. | .NOP => false
  | _ => true

def valid : Trace → MachineState → Bool
  | [], _ => true
  | (i, op) :: rest, s =>
    s.pc == BitVec.ofNat 64 (4096+4*i) && ordinary op &&
      memoryArgumentsValid s op && valid rest (execInstrBr s op)

def finish : Trace → MachineState → MachineState
  | [], s => s
  | (_, op) :: rest, s => finish rest (execInstrBr s op)

def cost : Trace → Nat
  | [] => 0
  | (_, op) :: rest => instructionCycles (.base op) + cost rest

def Fetched (image : Image) (trace : Trace) : Prop :=
  ∀ i op, (i,op) ∈ trace → ∀ s : MachineState,
    s.pc = BitVec.ofNat 64 (4096+4*i) → fetch image s = some (.base op)

private theorem valid_step (s : MachineState) (op : Instr) (plain : ordinary op = true)
    (memory : memoryArgumentsValid s op = true) :
    ordinaryStep s (.base op) = some (execInstrBr s op) := by
  cases op <;> simp_all [ordinary, ordinaryStep]

/-- For all initial machine memory and registers, the trace certificate checks
the real fetch position, memory bounds/alignment and ALU semantics of every step. -/
theorem execute_trace (image : Image) (trace : Trace) (s : MachineState) (fuel : Nat) (coins : Bool)
    (fetches : Fetched image trace) (ok : valid trace s = true) :
    execute image (trace.length+fuel) s coins =
      (do let r ← execute image fuel (finish trace s) coins; return r.charge (cost trace) 0) := by
  induction trace generalizing s with
  | nil => simp [finish, cost, Execution.charge]
  | cons pair rest ih =>
    rcases pair with ⟨i,op⟩
    simp only [valid, Bool.and_eq_true, beq_iff_eq] at ok
    obtain ⟨⟨⟨pc,plain⟩,mem⟩,tail⟩ := ok
    have first := fetches i op (by simp) s pc
    have fetchedTail : Fetched image rest := fun j next h => fetches _ _ (List.mem_cons_of_mem _ h)
    rw [List.length_cons, show rest.length+1+fuel = (rest.length+fuel)+1 by omega,
      execute_ordinary_step _ _ _ _ _ _ first (valid_step s op plain mem), ih _ fetchedTail tail]
    simp [finish, cost, Execution.charge, Nat.add_assoc]

/-- Build a valid trace-fetch witness from a per-index table of decoded words
in order. It suffices to check a bounded integer index, including across jumps. -/
theorem fetched_of_index (image : Image) (path : Trace)
    (table : ∀ k : Fin path.length,
      (image.code[path[k].1]?).bind decodeInstruction = some (.base path[k].2))
    (fits : ∀ k : Fin path.length, 4096 + 4*path[k].1 < 2^64) : Fetched image path := by
  intro i op mem s loc
  obtain ⟨i',bound, same⟩ := List.getElem_of_mem mem
  have decoded := table ⟨i',bound⟩
  have small := fits ⟨i',bound⟩
  change (image.code[path[i'].1]?).bind decodeInstruction = some (.base path[i'].2) at decoded
  change 4096+4*path[i'].1 < 2^64 at small
  simp only [same] at decoded small
  have index : s.pc.toNat = 4096+4*i := by
    rw [loc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  rw [fetch, index, ite_eq_left (by omega), show (4096+4*i-4096)/4=i by omega]
  cases w : image.code[i]? <;> simp_all

/-- Fetch a checked list directly from the verifier's packed binary. This avoids
materializing the instruction list for larger code images. -/
theorem fetched_of_packed (image : Image) (path : Trace) {n : Nat}
    (packed : ArtifactEncoding.Packed n) (image_eq : image.code = ArtifactEncoding.decode 32 packed)
    (len : 4096+4*n < 2^64) (bounds : ∀ k : Fin path.length, path[k].1 < n)
    (table : ∀ k : Fin path.length, decodeInstruction (packed.get 32 ⟨path[k].1, bounds k⟩) =
      some (.base path[k].2)) : Fetched image path := by
  intro i op mem s loc
  obtain ⟨j,hj,eq⟩ := List.getElem_of_mem mem
  have idx := bounds ⟨j,hj⟩
  change path[j].1 < n at idx
  have bound : i < n := by simpa only [eq] using idx
  rw [fetch_packed image packed image_eq i bound (by omega) s loc]
  have result := table ⟨j,hj⟩
  change decodeInstruction (packed.get 32 ⟨path[j].1,idx⟩) = some (.base path[j].2) at result
  have indexEq : (⟨path[j].1,idx⟩ : Fin n) = ⟨i,bound⟩ := Fin.ext (congrArg Prod.fst eq)
  have opEq : path[j].2 = op := congrArg Prod.snd eq
  rw [indexEq,opEq] at result
  exact result

end CommitGolfCandidate.Reconstruction.HonestMachine
