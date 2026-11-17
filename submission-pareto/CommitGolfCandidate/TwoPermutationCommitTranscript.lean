import CommitGolfCandidate.TwoPermutationCommittedHeap
import CommitGolfCandidate.TwoPermutationOpeningTranscript

/-! The final representation is the exact machine memory returned by the trusted
ABI. Independent nonces reindex the machine's single packed 128·LENGTH-bit draw. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (fixedOracleRun fixed_oracle_run_map splitBlocks split_blocks_bijective)
set_option maxRecDepth 32768
set_option maxHeartbeats 1500000
attribute [local irreducible] packedOutput commitTrace transcriptHeap

noncomputable def packSaltTape : CompleteSaltTape → BitVec (128*LENGTH) :=
  (Equiv.ofBijective (splitBlocks 128 LENGTH) (split_blocks_bijective 128 LENGTH (by decide))).symm

theorem split_pack_salt (salts : CompleteSaltTape) : splitBlocks 128 LENGTH (packSaltTape salts)=salts :=
  (Equiv.ofBijective _ (split_blocks_bijective 128 LENGTH (by decide))).apply_symm_apply salts

theorem pack_split_salt (packed : BitVec (128*LENGTH)) : packSaltTape (splitBlocks 128 LENGTH packed)=packed :=
  (Equiv.ofBijective _ (split_blocks_bijective 128 LENGTH (by decide))).symm_apply_apply packed

noncomputable def trapdoorOf (candidate : Submission) (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) :
    BitVec (8*candidate.sizes.trapdoor) :=
  (candidate.readCommit (packedOutput (candidate.initialState .commit msg) oracle (packSaltTape salts))).2

private theorem normalize_draw {α : Type} (bits : Nat) (width : bits=128*LENGTH) (f : {n : Nat} → BitVec n → α) :
    (do let packed ← $ᵗ BitVec bits; pure (f packed) : ProbComp α) =
      (do let packed ← $ᵗ BitVec (128*LENGTH); pure (f packed)) := by subst bits;rfl

theorem packed_commit_distribution (candidate : Submission) (abi : CommitABI candidate)
    (oracle : Oracle) (msg : Message) :
    fixedOracleRun oracle (candidate.scheme.commit msg) =
      (do let packed ← $ᵗ BitVec (128*LENGTH)
          let salts := splitBlocks 128 LENGTH packed
          pure (publicTree oracle msg salts 1,trapdoorOf candidate oracle msg salts)) := by
  let s := candidate.initialState .commit msg
  have entry := abi_commit_entry candidate abi msg
  have width : 8*((initialPrefix s 11).getReg .x11).toNat=128*LENGTH := by
    rw [(setup_registers s entry).size];rfl
  change fixedOracleRun oracle (candidate.readCommit <$> candidate.run .commit msg)=_
  rw [submission_commit_run candidate abi msg,fixed_oracle_run_map]
  unfold fixedOracleRun
  rw [counted_commit_trace]
  simp only [map_bind,map_pure]
  change (do let packed ← $ᵗ BitVec (8*((initialPrefix s 11).getReg .x11).toNat)
             pure (candidate.readCommit (packedOutput s oracle packed)))=_
  rw [normalize_draw _ width (fun {_} packed => candidate.readCommit (packedOutput s oracle packed))]
  apply bind_congr_of_forall_mem_support
  intro packed _
  have physical := physical_results candidate abi oracle msg packed
  dsimp only [trapdoorOf]
  rw [pack_split_salt]
  exact congrArg pure (Prod.ext physical.1 rfl)

noncomputable def verifiedCommitTranscript (candidate : Submission) (abi : CommitABI candidate) :
    Opening.CommitTranscript candidate :=
  Opening.CommitTranscript.ofPacked candidate (trapdoorOf candidate)
    (by intro oracle msg; rw [packed_commit_distribution candidate abi oracle msg];rfl)
    (by
      intro oracle msg salts i
      have eq := (physical_results candidate abi oracle msg (packSaltTape salts)).2.2 i
      simpa only [Opening.trapdoorSalt,trapdoorOf,split_pack_salt] using eq)
    (by
      intro oracle msg salts n pos hi
      have eq := (physical_results candidate abi oracle msg (packSaltTape salts)).2.1 n pos hi
      simpa only [Opening.trapdoorHeap,trapdoorOf,split_pack_salt,publicTree] using eq)

end TwoPermutationPrototype.RV64
