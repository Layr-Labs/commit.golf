import CommitGolfCandidate.ParentRefinement

/-! Contents of the 64-call chain over the cap. Cap node `m` is heap slot `128+m`; the
chain state after `k` pairs lives in the gap of pair `63+k`, directly below cap pair
`k` (slots `128+2k`, `129+2k`). Each call reads the contiguous 96 bytes
`[h_k | cap 2k | cap 2k+1]`, exactly the reference chain input, and writes `h_(k+1)`
into the next gap. No node slot is ever written. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- The cap of a machine heap: slots 128..255 (zero outside the 128 cap nodes, which
the cap root never reads). -/
def heapCap (state : MachineState) (base : Nat) : Nat → Digest :=
  fun node => if node < 128 then heapDigest state base (128+node) else 0

/-- The reference chain state after the first `k` cap pairs. -/
def chainPrefix (compress : Compression) (cap : Nat → Digest) (k : Nat) : Digest :=
  (List.range k).foldl (fun state pair => absorb compress state (capBlock cap pair)) 0

theorem chain_prefix_succ (compress : Compression) (cap : Nat → Digest) (k : Nat) :
    chainPrefix compress cap (k+1) = absorb compress (chainPrefix compress cap k) (capBlock cap k) := by
  simp [chainPrefix, List.range_succ, List.foldl_append]

theorem chain_prefix_zero (compress : Compression) (cap : Nat → Digest) :
    chainPrefix compress cap 0 = 0 := rfl

theorem chain_prefix_root (compress : Compression) (cap : Nat → Digest) :
    chainPrefix compress cap CAP_PAIRS = capRoot compress cap := by
  simp [chainPrefix, capRoot, capBlocks, List.foldl_map]

theorem cap_congr (compress : Compression) (cap cap' : Nat → Digest)
    (same : ∀ node < 2*CAP_PAIRS, cap node = cap' node) :
    capRoot compress cap = capRoot compress cap' := by
  have blocks : capBlocks cap = capBlocks cap' := by
    unfold capBlocks
    apply List.map_congr_left
    intro pair member
    have := List.mem_range.mp member
    unfold capBlock
    rw [same (2*pair+1) (by omega), same (2*pair) (by omega)]
  rw [capRoot, capRoot, blocks]

theorem chain_iteration_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (chainIterationRun state) =
      (chainNextState (parentStep oracle state 2), 1) := by
  simp only [chainIterationRun, check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem commit_chain_evaluation_zero (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (commitChain state 0) = (state, 0) := by
  simp only [commitChain, check_evaluation_pure]

theorem commit_chain_evaluation (oracle : Oracle) (state : MachineState) (remaining : Nat) :
    checkEvaluation oracle (commitChain state (remaining+1)) =
      let next := chainNextState (parentStep oracle state 2)
      let result := checkEvaluation oracle (commitChain next remaining)
      (result.1, 1+result.2) := by
  rw [commitChain, check_evaluation_bind, chain_iteration_evaluation]

/-- The chain pointer after one deterministic iteration. -/
theorem chain_next_pointer (oracle : Oracle) (state : MachineState) (address : Nat)
    (pointer : state.getReg .x21 = BitVec.ofNat 64 address) :
    (chainNextState (parentStep oracle state 2)).getReg .x21 = BitVec.ofNat 64 (address + 96) := by
  rw [(chain_next_registers _).1, parent_step_register oracle state 2 (by decide) .x21 (by decide)
    (by decide), pointer]
  exact BitVec.ofNat_add_ofNat (n := 64) address 96

/-- The chain changes only gaps of pairs 64..127. -/
theorem commit_chain_preserves (oracle : Oracle) (state : MachineState) (base remaining : Nat)
    (pointer : state.getReg .x21 = BitVec.ofNat 64 (base + 12256 - 96*remaining))
    (inside : remaining ≤ 64) (bounded : base + 12288 ≤ MEMORY_BYTES)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (outside : ∀ q, 64 ≤ q → q < 128 →
      address + count ≤ base + 96*q + 64 ∨ base + 96*q + 96 ≤ address) :
    readBuffer (checkEvaluation oracle (commitChain state remaining)).1 address count =
      readBuffer state address count := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction remaining generalizing state with
  | zero => rw [commit_chain_evaluation_zero]
  | succ remaining ih =>
    rw [commit_chain_evaluation]
    dsimp only
    have nextPointer := chain_next_pointer oracle state _ pointer
    rw [show base + 12256 - 96*(remaining+1) + 96 = base + 12256 - 96*remaining by omega] at nextPointer
    rw [ih _ nextPointer (by omega)]
    change readBuffer (parentStep oracle state 2) address count = _
    have out : (parentOutput state 2).toNat = base + 96*(127-remaining) + 64 := by
      show (state.getReg .x21 + BitVec.ofNat 64 96).toNat = _
      rw [pointer, pointer_offset_nat _ 96 (by omega)]
      omega
    exact parent_step_outside oracle state 2 _ out (by omega) address count readBound
      (by have := outside (127-remaining) (by omega) (by omega); omega)

/-- The chain never writes a node slot. -/
theorem commit_chain_preserves_digest (oracle : Oracle) (state : MachineState) (base remaining : Nat)
    (pointer : state.getReg .x21 = BitVec.ofNat 64 (base + 12256 - 96*remaining))
    (inside : remaining ≤ 64) (bounded : base + 12288 ≤ MEMORY_BYTES)
    (node : Nat) (readBound : base + heapOffset node + 32 ≤ 2^64) :
    heapDigest (checkEvaluation oracle (commitChain state remaining)).1 base node =
      heapDigest state base node := by
  unfold heapDigest
  apply commit_chain_preserves oracle state base remaining pointer inside bounded _ 32 readBound
  intro q _ _
  have := heap_offset_gap node q
  omega

/-- The final chain state, in the gap of pair 127, is the reference chain over the
cap supplied by the heap's node slots 128..255. -/
theorem commit_chain_root (oracle : Oracle) (state : MachineState) (base remaining : Nat)
    (pointer : state.getReg .x21 = BitVec.ofNat 64 (base + 12256 - 96*remaining))
    (inside : remaining ≤ 64) (aligned : base % 8 = 0) (bounded : base + 12288 ≤ MEMORY_BYTES)
    (current : readBuffer state (base + 12256 - 96*remaining) 32 =
      chainPrefix oracle.compression (heapCap state base) (64 - remaining)) :
    readBuffer (checkEvaluation oracle (commitChain state remaining)).1 (base + 12256) 32 =
      capRoot oracle.compression (heapCap state base) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction remaining generalizing state with
  | zero =>
    rw [commit_chain_evaluation_zero]
    simpa [chain_prefix_root] using current
  | succ remaining ih =>
    rw [commit_chain_evaluation]
    dsimp only
    obtain ⟨k, hk⟩ : ∃ k, k + remaining = 63 := ⟨63 - remaining, by omega⟩
    let next := chainNextState (parentStep oracle state 2)
    have nextPointer := chain_next_pointer oracle state _ pointer
    rw [show base + 12256 - 96*(remaining+1) + 96 = base + 12256 - 96*remaining by omega] at nextPointer
    have src : (parentSource state 2).toNat = base + 96*(63+k) + 64 := by
      show (state.getReg .x21 + BitVec.ofNat 64 0).toNat = _
      rw [pointer, pointer_offset_nat _ 0 (by omega)]
      omega
    have out : (parentOutput state 2).toNat = base + 96*(64+k) + 64 := by
      show (state.getReg .x21 + BitVec.ofNat 64 96).toNat = _
      rw [pointer, pointer_offset_nat _ 96 (by omega)]
      omega
    -- the written gap holds no node, so the cap is unchanged by this call
    have capSame : heapCap next base = heapCap state base := by
      funext node
      unfold heapCap
      split
      · rename_i small
        change heapDigest (parentStep oracle state 2) base (128+node) = heapDigest state base (128+node)
        unfold heapDigest
        have := heap_offset_gap (128+node) (64+k)
        exact parent_step_outside oracle state 2 _ out (by omega) _ 32 (by unfold heapOffset; omega)
          (by omega)
      · rfl
    -- the call input is [h_k | cap 2k | cap 2k+1]
    have input : readBuffer state (parentSource state 2).toNat 96 =
        leafInput (chainPrefix oracle.compression (heapCap state base) k)
          (capBlock (heapCap state base) k) := by
      have alignedMid : (base + 96*(63+k) + 64 + 32) % 8 = 0 := by omega
      rw [src, read_leaf_query, read_compression_halves _ _ alignedMid]
      have even : base + 96*(63+k) + 64 + 32 = base + heapOffset (128 + 2*k) := by
        rw [show 128 + 2*k = 2*(64+k) by omega, heap_offset_even]; omega
      have odd : base + 96*(63+k) + 64 + 32 + 32 = base + heapOffset (128 + (2*k+1)) := by
        rw [show 128 + (2*k+1) = 2*(64+k)+1 by omega, heap_offset_odd]; omega
      have state0 : base + 96*(63+k) + 64 = base + 12256 - 96*(remaining+1) := by omega
      rw [odd, even, state0, current, show 64 - (remaining+1) = k by omega]
      have c0 : heapCap state base (2*k) = heapDigest state base (128+2*k) := if_pos (by omega)
      have c1 : heapCap state base (2*k+1) = heapDigest state base (128+(2*k+1)) := if_pos (by omega)
      rw [capBlock, c0, c1]
      rfl
    have written : readBuffer next (base + 12256 - 96*remaining) 32 =
        chainPrefix oracle.compression (heapCap next base) (64 - remaining) := by
      change readBuffer (parentStep oracle state 2) _ 32 = _
      rw [show base + 12256 - 96*remaining = base + 96*(64+k) + 64 by omega,
        parent_step_written oracle state 2 _ out, capSame,
        show 64 - remaining = k + 1 by omega, chain_prefix_succ]
      unfold parentAnswer absorb
      rw [input]
    rw [ih next nextPointer (by omega) written, capSame]

end CommitGolfCandidate
