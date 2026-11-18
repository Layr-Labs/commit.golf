import CommitGolfCandidate.NoncePairGame
import CommitGolfCandidate.NonceChainLayout

/-! Alternating full-reply and zero-padded-key permutation inputs. Every reply
still emits eleven salts followed by a hidden192-bit key. The first input is
the low192-bit seed itself, not a high-bit extraction from that seed. -/
namespace CommitGolfCandidate.Permutation.NoncePair
open CommitGolf Finset
set_option exponentiation.threshold 2048
set_option maxRecDepth 8000

abbrev Word1600 := NonceChain.Word1600
abbrev Key := NonceChain.Key
abbrev Nonce := NonceChain.Nonce
abbrev Block := NonceChain.Block
abbrev blocks := NonceChain.blocks
abbrev seedState := NonceChain.seedState
noncomputable abbrev blockEquiv := NonceChain.blockEquiv
abbrev nonceAt := NonceChain.nonceAt

def hiddenKey (y : Word1600) : Key := y.extractLsb' 1408 192

/-- Input following zero-based call j: retain its full reply after even j,
or keep only its private key after odd j. -/
def nextInput (j : Nat) (y : Word1600) : Word1600 :=
  if j % 2 = 0 then y else seedState (hiddenKey y)

/-- Transform output-vertex j into the input of call j. Vertex0 is the
initial seed and is deliberately not treated as a permutation reply. -/
def inputTransform (j : Nat) (y : Word1600) : Word1600 :=
  if j = 0 then y else nextInput (j-1) y

@[simp] theorem inputTransform_zero (y : Word1600) : inputTransform 0 y = y := rfl

@[simp] theorem inputTransform_succ (j : Nat) (y : Word1600) :
    inputTransform (j+1) y = nextInput j y := by simp [inputTransform]

def pairedInput (π : Equiv.Perm Word1600) (k : Key) (j : Nat) : Word1600 :=
  inputTransform j (orbit π inputTransform (seedState k) j)

def pairedReply (π : Equiv.Perm Word1600) (k : Key) (j : Nat) : Word1600 :=
  π (pairedInput π k j)

@[simp] theorem pairedInput_zero (π : Equiv.Perm Word1600) (k : Key) :
    pairedInput π k 0 = seedState k := rfl

theorem pairedReply_eq_orbit (π : Equiv.Perm Word1600) (k : Key) (j : Nat) :
    pairedReply π k j = orbit π inputTransform (seedState k) (j+1) := rfl

@[simp] theorem pairedInput_succ (π : Equiv.Perm Word1600) (k : Key) (j : Nat) :
    pairedInput π k (j+1) = nextInput j (π (pairedInput π k j)) := by
  change inputTransform (j+1) (π (pairedInput π k j)) = _
  exact inputTransform_succ j _

@[simp] theorem hiddenKey_full (p : Block) (k : Key) :
    hiddenKey (blockEquiv.symm (p,k)) = k := by
  change (blockEquiv (blockEquiv.symm (p,k))).2 = k
  rw [blockEquiv.apply_symm_apply]

theorem seed_injective : Function.Injective seedState := NonceChain.seed_injective

/-- Conditional on all public prefixes, every input endpoint remains an
injective encoding of its own independent private key coordinate. -/
theorem input_encoder_injective (p : Fin blocks → Block) (i : Fin (blocks+1)) :
    Function.Injective (fun k => inputTransform i.val
      (NonceChain.encodeAt blockEquiv seedState p i k)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [NonceChain.encodeAt] using seed_injective
  · change Function.Injective (fun k => nextInput j.val (blockEquiv.symm (p j,k)))
    intro a b h
    by_cases even : j.val % 2 = 0
    · have images : blockEquiv.symm (p j,a) = blockEquiv.symm (p j,b) := by
        simpa only [nextInput,if_pos even] using h
      exact congrArg Prod.snd (blockEquiv.symm.injective images)
    · have seeds : seedState a = seedState b := by
        simpa only [nextInput,if_neg even,hiddenKey_full] using h
      exact seed_injective seeds

noncomputable def actualNonces (π : Equiv.Perm Word1600) (k : Key) :=
  nonceAt (fun i => (blockEquiv (pairedReply π k i.val)).1)

/-- The conservative role-separated endpoint error, including one harmless
unused endpoint in each role. -/
noncomputable def chainError (q : Nat) : ℝ :=
  2 * ((blocks+1 : Nat) : ℝ) * ((q+(blocks+1) : ℝ) / 2^192)

/-- This allowance covers both message-side generator replacements. -/
theorem replacement_budget (t : Nat) :
    2 * chainError (t + (2*LENGTH + (4194304+t))) ≤ ((t:ℝ)+1)/2^143 := by
  norm_num [chainError,blocks,NonceChain.blocks,LENGTH,LOG_LENGTH,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

/-- The unchanged quartet middle hybrid and both generator replacements
fit the original hiding allowance. -/
theorem quartet_budget (t : Nat) :
    ((t:ℝ)+1)/2^121 + 2 * chainError (t + (2*LENGTH + (4194304+t))) ≤
      ((t:ℝ)+1)/2^120 := by
  norm_num [chainError,blocks,NonceChain.blocks,LENGTH,LOG_LENGTH,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

end CommitGolfCandidate.Permutation.NoncePair
