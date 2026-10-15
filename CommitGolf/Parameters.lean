import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Basic

/-! Benchmark constants, byte representations, programs, and declared buffer layouts. -/
namespace CommitGolf.VectorCommit

/-- One byte, represented as an 8-bit vector. -/
abbrev Byte := BitVec 8

/-- A fixed-width byte string, represented as a bit vector. -/
abbrev Bytes (n : Nat) := BitVec (8 * n)

/-- Size in bytes of each entry in the committed vector. -/
def MESSAGE_BYTES : Nat := 32

/-- Size in bytes of the commitment to the entire vector. -/
def COMMITMENT_BYTES : Nat := 32

/-- One entry of the committed vector. -/
abbrev Message := Bytes MESSAGE_BYTES

/-- The fixed-size public commitment produced by the commit program. -/
abbrev Commitment := Bytes COMMITMENT_BYTES

/-! ## Security parameters -/

/-- Base-two exponent of the adversary's allowed number of hash queries. -/
def QUERY_BITS : Nat := 100

/-- Minimum declared binding parameter; at this floor the allowed forgery probability is one half. -/
def MIN_BINDING_BITS : Nat := QUERY_BITS + 1

/-- Maximum number of hash-oracle calls allowed to the binding adversary. -/
def QUERY_BUDGET : Nat := 2 ^ QUERY_BITS

/-- Allowed forgery probability: the query budget divided by two to the declared binding parameter. -/
noncomputable def bindingError (bits : Nat) : ENNReal :=
  (QUERY_BUDGET : ENNReal) / 2 ^ bits

/-! ## Vector dimensions and opening samples -/

/-- Base-two logarithm of the number of entries in the vector. -/
def VECTOR_LOG_LENGTH : Nat := 24

/-- Number of entries in the committed vector. -/
def VECTOR_LENGTH : Nat := 2 ^ VECTOR_LOG_LENGTH

/-- Number of uniformly sampled single-position openings averaged by the size experiment. -/
def OPENING_SAMPLES : Nat := 100

/-- A message at every valid vector position. -/
abbrev MessageVector := Fin VECTOR_LENGTH → Message

/-- A finite set of vector positions to open or check. -/
abbrev Positions := Finset (Fin VECTOR_LENGTH)

/-! ## Programs and storage layout -/

/-- The three submitted machine programs: commit a vector, produce an opening, and check it. -/
inductive Program where
  | commit
  | opening
  | check
  deriving DecidableEq

/-- Enumerates all three programs for statements that quantify over every program. -/
instance : Fintype Program :=
  ⟨{.commit, .opening, .check}, fun p => by cases p <;> simp⟩

/-- Solver-declared storage capacities. Commitment and message widths are organizer constants. -/
structure Sizes where
  trapDoor : Nat
  openingProof : Nat
  deriving DecidableEq

/-- Fixed-size private state produced by commit and supplied to the opening program. -/
abbrev TrapDoor (sizes : Sizes) := Bytes sizes.trapDoor

/-- Byte addresses of the input and output buffers used by the machine programs. -/
structure Layout where
  message : Nat
  commitment : Nat
  trapDoor : Nat
  indices : Nat
  claimedValues : Nat
  openingProof : Nat
  deriving DecidableEq

/-- Reserved buffer ranges as address and byte-length pairs, used to check memory layout validity. -/
def Layout.buffers (layout : Layout) (sizes : Sizes) : List (Nat × Nat) :=
  [(layout.message, VECTOR_LENGTH * MESSAGE_BYTES),
   (layout.commitment, COMMITMENT_BYTES),
   (layout.trapDoor, sizes.trapDoor),
   (layout.indices, VECTOR_LENGTH * 8),
   (layout.claimedValues, VECTOR_LENGTH * MESSAGE_BYTES),
   (layout.openingProof, sizes.openingProof)]

/-! ## Program inputs and outputs -/

/-- A commitment, selected positions, claimed values, and proof supplied to the check program. -/
structure CheckInput where
  commitment : Commitment
  indices : Positions
  claimedValues : ∀ _ : indices, Message
  proof : List Byte

/-- Typed inputs for each program before serialization into machine memory. -/
abbrev Input (sizes : Sizes) : Program → Type
  | .commit => MessageVector
  | .opening => TrapDoor sizes × Positions
  | .check => CheckInput

/-- Decoded successful outputs; the check program signals acceptance without returning data. -/
abbrev Output (sizes : Sizes) : Program → Type
  | .commit => Commitment × TrapDoor sizes
  | .opening => List Byte
  | .check => Unit

end CommitGolf.VectorCommit

namespace CommitGolf.Riscv

/-- Execution-cycle ceiling; the termination certificate requires every execution to finish below it. -/
def CYCLE_LIMIT : Nat := 2 ^ 32

/-- Four GiB accommodates the default 512 MiB vector and arbitrary-subset buffers.
Memory is modeled as a function; loading does not allocate the entire address space. -/
def MEMORY_BYTES : Nat := 2 ^ 32

/-- Maximum size in bytes of each submitted program image, including embedded data. -/
def MAX_PROGRAM_BYTES : Nat := 2 ^ 20

end CommitGolf.Riscv
