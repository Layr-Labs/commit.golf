import CommitGolfCandidate.MoonOpenExec
import CommitGolfCandidate.MoonCommitRef
import CommitGolfCandidate.MoonHiding

/-! End-to-end refinement of the deterministic 64-32 opening program against `CommittedTrapdoor`
and `referenceProof`, plus exact transcript refinement `HonestTranscriptRefines` for `MoonHiding`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem opening_run_deterministic (oracle : Oracle)
    (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (positions : Positions) :
    ∃ exec : Execution,
      oracle.run (submission.run .opening (trapdoor, positions)) = pure (exec, 0) ∧
      exec.exit = Riscv.Exit.success ∧
      exec.oracleCalls = 0 ∧
      (exec.state.getReg .x11).toNat ≤ submission.sizes.proof ∧
      (positions.card = BATCH → exec.cycles ≤ 110258) := by
  obtain ⟨exec, hrun, hexit, hcalls, hlen, _, hcyc⟩ := opening_exec_spec trapdoor positions
  refine ⟨exec, ?_, hexit, hcalls, ?_, hcyc⟩
  · rw [hrun, oracle_run_pure]
  · rw [hlen]
    exact referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions

theorem opening_honest_proof (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (message : Message) (salts : Index → Salt192)
    (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (htd : CommittedTrapdoor h512 oracle.compression oracle.permutation message salts trapdoor)
    (positions : Positions) (exec : Execution)
    (hrun : oracle.run (submission.run .opening (trapdoor, positions)) = pure (exec, 0)) :
    submission.readProof exec =
      referenceProof
        (nodeVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation message salts)
        salts positions := by
  obtain ⟨exec0, hdet, hexit, _, hlen, hbytes, _⟩ := opening_exec_spec trapdoor positions
  have hrun0 : oracle.run (submission.run .opening (trapdoor, positions)) = pure (exec0, 0) := by
    rw [hdet, oracle_run_pure]
  have hmem : (exec, 0) ∈ support (pure (exec0, 0) : ProbComp (Execution × Nat)) := by
    rw [← hrun0, hrun, support_pure]
    exact Set.mem_singleton _
  rw [support_pure, Set.mem_singleton_iff] at hmem
  have heq : exec = exec0 := (Prod.mk.inj hmem).1
  rw [heq]
  have hlen_le : (exec0.state.getReg .x11).toNat ≤ submission.sizes.proof := by
    rw [hlen]
    exact referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions
  have hsuc : submission.openingSucceeded exec0 = true := by
    unfold Submission.openingSucceeded
    rw [hexit, show (Exit.success == Exit.success) = true from rfl, Bool.true_and, decide_eq_true_eq]
    exact hlen_le
  have hread : submission.readProof exec0 =
      referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions := by
    unfold Submission.readProof
    rw [if_pos hsuc]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, hlen]
    · intro j hj1 hj2
      simp only [List.getElem_map, List.getElem_range]
      have hproof_base : submission.layout.proof = 10804531232 := rfl
      rw [hproof_base]
      exact hbytes j hj2
  rw [hread]
  have hsalts : tdSalt trapdoor = salts := funext htd.2
  rw [hsalts]
  exact referenceProof_congr_nodes (tdNode trapdoor)
    (nodeVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation message salts)
    htd.1 salts positions

private theorem o_evalDistEq_of_eq {α : Type} {a b : ProbComp α} (h : a = b) :
    EvalDistEq a b :=
  h ▸ EvalDistEq.refl a

theorem honest_transcript_refines (h512 : COMPRESSION_INPUT_LENGTH = 512) :
    HonestTranscriptRefines h512 := by
  intro oracle message positions
  unfold honestTranscript
  obtain ⟨trapdoorOf, hcommit_run, htd⟩ := commit_oracle_run_exact h512 oracle message
  rw [fixed_oracle_run_bind]
  refine (hcommit_run.bind_left _).trans ?_
  refine o_evalDistEq_of_eq ?_
  refine (bind_assoc _ _ _).trans ?_
  apply bind_congr; intro rand
  refine (pure_bind _ _).trans ?_
  dsimp only
  rw [fixed_oracle_run_bind]
  obtain ⟨oExec, ho_run, _, _, _, _⟩ := opening_run_deterministic oracle (trapdoorOf rand) positions
  have hpf := opening_honest_proof h512 oracle message (pairSalts rand)
    (trapdoorOf rand) (htd rand) positions oExec ho_run
  have hopen : fixedOracleRun oracle (submission.scheme.opening (trapdoorOf rand) positions) =
      pure (referenceProof
        (nodeVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation message (pairSalts rand))
        (pairSalts rand) positions) := by
    simp only [fixedOracleRun, Submission.scheme, oracle_run_map, ho_run, map_pure, hpf]
  rw [hopen, pure_bind, fixed_oracle_run_pure]
  rfl

end CommitGolfCandidate
