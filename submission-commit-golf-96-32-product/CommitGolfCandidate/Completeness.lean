import CommitGolfCandidate.HonestRecords
import CommitGolfCandidate.CheckHonest
import CommitGolfCandidate.InputOrder

/-! Perfect completeness for the scheme derived from the submitted machine images,
covering both normal openings (`k ≠ 128`) and level-7 cap-table openings (`k = 128`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem initial_check_registers (program : Submission) (input : CheckInput) :
    (program.initialState .check input).getReg .x11 = BitVec.ofNat 64 program.layout.commitment ∧
    (program.initialState .check input).getReg .x13 = BitVec.ofNat 64 program.layout.indices ∧
    (program.initialState .check input).getReg .x14 = BitVec.ofNat 64 program.layout.values ∧
    (program.initialState .check input).getReg .x15 = BitVec.ofNat 64 program.layout.proof := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem ready_memory (state : MachineState) :
    (checkReadyState (checkLengthState state)).mem = state.mem := rfl

attribute [local irreducible] checkReadyState checkLengthState checkCapHash checkEvaluation
  checkRootWordsState

set_option maxHeartbeats 600000 in
/-- The actual checker accepts the bytes produced by opening any correctly
constructed commitment state, for every requested position set. -/
theorem honest_check_accepts (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) :
    let root := readBuffer committed submission.layout.commitment 32
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    (oracle.eval (submission.scheme.check root positions (message.restrict positions)
      (submission.readProof (openingResult trapdoor positions)))).1 = true := by
  let root := readBuffer committed submission.layout.commitment 32
  let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
  let input : CheckInput :=
    ⟨root, positions, message.restrict positions, submission.readProof (openingResult trapdoor positions)⟩
  let initial := submission.initialState .check input
  let indices : Nat → Index := fun ordinal =>
    ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  let heap : Nat → Digest := fun slot => readBuffer committed (4294971424 + heapOffset slot) 32
  let salts : Index → Salt := fun index => readBuffer committed (5905584160 + 16 * index.val) 16
  have proofLen : input.proof.length = openingProofBytes positions.card :=
    opening_proof_length trapdoor positions
  apply (scheme_check_acceptance oracle input).mpr
  by_cases batch : positions.card = BATCH
  · rw [if_pos batch]
    have lenOk : input.proof.length = 75776 := by
      rw [proofLen]; simp only [openingProofBytes, if_pos batch]
    have bytesEq : openingProofBytes positions.card = 75776 := by
      simp only [openingProofBytes, if_pos batch]
    have capRecs := opening_output_records_cap committed positions batch
    have capEq (slot : Nat) (hs : slot < 128) : capTableOf initial slot = heap (128 + slot) := by
      have copied := check_opening_proof_digest trapdoor positions root (message.restrict positions)
        (71680 + 32 * slot) (by rw [bytesEq]; omega)
      have hRec := capRecs.2 slot hs
      change readBuffer initial (submission.layout.proof + (71680 + 32 * slot)) 32 = _ at copied
      rw [capTableOf, Nat.add_assoc]
      exact copied.trans (by simpa only [Nat.add_assoc] using hRec)
    have topRoot : referenceHeap oracle.compression 128 (capTableOf initial) 1 = input.commitment := by
      have hRef := heap_eq_reference oracle.compression 128 (capTableOf initial) heap
        (fun p pos hi => correct.2.1 p pos (by change p < 16777216; omega))
        (fun s hs => (capEq s hs).symm) 1 (by decide) (by decide)
      exact hRef.symm.trans correct.1.symm
    let hashed := (checkEvaluation oracle (checkCapHash initial)).1
    have capMatch : rootWordsMatch hashed = true :=
      (root_words_match_iff hashed).mpr ((check_cap_comparison oracle input batch lenOk).mpr topRoot)
    let compared := checkRootWordsState hashed 138 4
    let entered := checkCapEnterLoopState compared
    have is128 : initial.getReg .x16 = 128 := by
      change BitVec.ofNat 64 positions.card = 128; rw [batch]; rfl
    have isLen : initial.getReg .x17 = 75776 := by
      change BitVec.ofNat 64 input.proof.length = 75776; rw [lenOk]; rfl
    have reached : hashed ∈ support (checkCapHash initial) := check_evaluation_support oracle _
    have hRegs := check_cap_hash_registers initial hashed is128 isLen reached
    have cKeep (reg : Reg) (n6 : reg ≠ .x6) (n7 : reg ≠ .x7) : compared.getReg reg = hashed.getReg reg :=
      (check_root_words_preserves hashed 138 4 reg n6 n7).1
    have eMem : entered.mem = hashed.mem :=
      (check_root_words_preserves hashed 138 4 .x21 (by decide) (by decide)).2
    have eAbove (addr : Nat) (hi : 8704 ≤ addr) (lt64 : addr < 2 ^ 64) :
        entered.getMem (BitVec.ofNat 64 addr) = initial.getMem (BitVec.ofNat 64 addr) := by
      change entered.mem _ = _
      rw [eMem]
      exact check_cap_hash_support_outside initial hashed isLen reached (BitVec.ofNat 64 addr)
        (Or.inr (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt64]; exact hi))
    have eDigest (addr : Nat) (aligned : addr % 8 = 0) (hi : 8704 ≤ addr) (lt64 : addr + 32 < 2 ^ 64) :
        readBuffer entered addr 32 = readBuffer initial addr 32 := by
      apply read_digest_congr _ _ _ aligned
      intro w hw
      exact eAbove (addr + 8 * w) (by omega) (by omega)
    have eSalt (addr : Nat) (aligned : addr % 8 = 0) (hi : 8704 ≤ addr) (lt64 : addr + 16 < 2 ^ 64) :
        readBuffer entered addr 16 = readBuffer initial addr 16 := by
      apply read_salt_congr _ _ _ aligned
      intro w hw
      exact eAbove (addr + 8 * w) (by omega) (by omega)
    have enterKeep (reg : Reg) (n21 : reg ≠ .x21) (n26 : reg ≠ .x26) (n30 : reg ≠ .x30) :
        entered.getReg reg = compared.getReg reg := by
      simp only [entered, checkCapEnterLoopState, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n30),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n26)]
    have targetPtr : entered.getReg .x26 = BitVec.ofNat 64 (10871640096 + 71680) := by
      simp only [entered, checkCapEnterLoopState, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x21 ≠ .x26),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x30 ≠ .x26),
        MachineState.getReg_setReg_eq (by decide : Reg.x26 ≠ .x0),
        cKeep .x19 (by decide) (by decide), hRegs.2.2.2.1]; rfl
    have valuePtr : entered.getReg .x8 = BitVec.ofNat 64 6576672800 := by
      rw [enterKeep .x8 (by decide) (by decide) (by decide), cKeep .x8 (by decide) (by decide),
        hRegs.2.2.2.2.1]; rfl
    have proofPtr : entered.getReg .x25 = BitVec.ofNat 64 10871640096 := by
      rw [enterKeep .x25 (by decide) (by decide) (by decide), cKeep .x25 (by decide) (by decide),
        hRegs.2.2.2.2.2.2.1]; rfl
    have indexPtr : entered.getReg .x24 = BitVec.ofNat 64 6442455072 := by
      rw [enterKeep .x24 (by decide) (by decide) (by decide), cKeep .x24 (by decide) (by decide),
        hRegs.2.2.2.2.2.1]; rfl
    have targetData (slot : Nat) (hs : slot < 2 ^ (24 - 17)) :
        readBuffer entered (10871640096 + 71680 + 32 * slot) 32 = heap (2 ^ (24 - 17) + slot) := by
      have hs128 : slot < 128 := hs
      rw [eDigest _ (by omega) (by omega) (by omega)]
      exact capEq slot hs128
    have indexData (ordinal : Nat) (present : ordinal < BATCH) :
        entered.getMem (BitVec.ofNat 64 (6442455072 + 8 * ordinal)) =
          BitVec.ofNat 64 (indices ordinal).val := by
      rw [eAbove _ (by omega) (by change ordinal < 128 at present; omega)]
      exact check_input_position input ordinal (by rw [batch]; exact present)
    have valueData (ordinal : Nat) (present : ordinal < BATCH) (block : Nat) (inside : block < 4) :
        readBuffer entered (6576672800 + 256 * ordinal + 64 * block) 64 =
          (message (indices ordinal)).extractLsb' (512 * block) 512 := by
      have ordLt : ordinal < positions.card := by rw [batch]; exact present
      rw [read_compression_halves _ _ (by omega),
        eDigest (6576672800 + 256 * ordinal + 64 * block + 32) (by omega) (by omega) (by change ordinal < 128 at present; omega),
        eDigest (6576672800 + 256 * ordinal + 64 * block) (by omega) (by omega) (by change ordinal < 128 at present; omega),
        ← read_compression_halves _ _ (by omega)]
      have value := check_input_value_block input ordinal block ordLt inside
      have indexSame :
          ((positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using ordLt)).val =
            indices ordinal := Fin.ext (sorted_value_index positions ordinal ordLt)
      change readBuffer initial (6576672800 + 256 * ordinal + 64 * block) 64 =
        (message (((positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using ordLt)).val)).extractLsb'
          (512 * block) 512 at value
      rw [indexSame] at value
      exact value
    have saltData (ordinal : Nat) (present : ordinal < BATCH) :
        readBuffer entered (10871640096 + (16 + 32 * 17) * ordinal) 16 = salts (indices ordinal) := by
      rw [eSalt _ (by omega) (by omega) (by change ordinal < 128 at present; omega)]
      have copied := check_opening_proof_salt trapdoor positions root (message.restrict positions)
        (560 * ordinal) (by rw [bytesEq]; change ordinal < 128 at present; omega)
      exact copied.trans (capRecs.1 ordinal present).1
    have pathData (ordinal : Nat) (present : ordinal < BATCH) (level : Nat) (inside : level < 17) :
        readBuffer entered (10871640096 + (16 + 32 * 17) * ordinal + 16 + 32 * level) 32 =
          heap (((LENGTH + (indices ordinal).val) / 2 ^ level) ^^^ 1) := by
      rw [eDigest _ (by omega) (by omega) (by change ordinal < 128 at present; omega)]
      have copied := check_opening_proof_digest trapdoor positions root (message.restrict positions)
        (560 * ordinal + 16 + 32 * level) (by rw [bytesEq]; change ordinal < 128 at present; omega)
      have hRec := (capRecs.1 ordinal present).2 level inside
      have joined := copied.trans (by simpa only [Nat.add_assoc] using hRec)
      change readBuffer initial (10871640096 + (560 * ordinal + 16 + 32 * level)) 32 =
        heap (((LENGTH + (indices ordinal).val) / 2 ^ level) ^^^ 1) at joined
      simpa only [Nat.add_assoc] using joined
    have loopAcc := check_loop_honest oracle entered message heap salts indices
      17 (10871640096 + 71680) 6576672800 10871640096 6442455072 BATCH
      (by decide) (by decide) rfl rfl targetPtr valuePtr proofPtr indexPtr
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      targetData indexData valueData saltData pathData correct.2.2 correct.2.1
    exact ⟨lenOk, capMatch, loopAcc⟩
  · rw [if_neg batch]
    have lenOk : input.proof.length = 784 * positions.card := by
      rw [proofLen]; simp only [openingProofBytes, if_neg batch]
    have bytesEq : openingProofBytes positions.card = 784 * positions.card := by
      simp only [openingProofBytes, if_neg batch]
    let ready := checkReadyState (checkLengthState initial)
    have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    have small : positions.card ≤ 16777216 := cardinal
    have registers := check_ready_registers initial
    have loaded := initial_check_registers submission input
    have rootPointer : ready.getReg .x26 = BitVec.ofNat 64 4294971392 := registers.2.2.2.2.1.trans loaded.1
    have valuePointer : ready.getReg .x8 = BitVec.ofNat 64 6576672800 := registers.2.2.1.trans loaded.2.2.1
    have proofPointer : ready.getReg .x25 = BitVec.ofNat 64 10871640096 := registers.2.2.2.1.trans loaded.2.2.2
    have indexPointer : ready.getReg .x24 = BitVec.ofNat 64 6442455072 := registers.2.1.trans loaded.2.1
    have memory : ready.mem = initial.mem := ready_memory initial
    have targetData (slot : Nat) (hs : slot < 2 ^ (24 - 24)) :
        readBuffer ready (4294971392 + 32 * slot) 32 = heap (2 ^ (24 - 24) + slot) := by
      have sz : slot = 0 := by change slot < 1 at hs; omega
      subst sz
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [read_buffer_memory_congr _ _ memory]
      exact (check_input_commitment input).trans correct.1
    have indexData (ordinal : Nat) (present : ordinal < positions.card) :
        ready.getMem (BitVec.ofNat 64 (6442455072 + 8 * ordinal)) = BitVec.ofNat 64 (indices ordinal).val := by
      rw [show ready.getMem = initial.getMem from congrArg (fun mem address => mem address) memory]
      exact check_input_position input ordinal present
    have valueData (ordinal : Nat) (present : ordinal < positions.card) (block : Nat) (inside : block < 4) :
        readBuffer ready (6576672800 + 256 * ordinal + 64 * block) 64 =
          (message (indices ordinal)).extractLsb' (512 * block) 512 := by
      rw [read_buffer_memory_congr _ _ memory]
      have value := check_input_value_block input ordinal block present inside
      have indexSame :
          ((positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present)).val =
            indices ordinal := Fin.ext (sorted_value_index positions ordinal present)
      change readBuffer initial (6576672800 + 256 * ordinal + 64 * block) 64 =
        (message (((positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present)).val)).extractLsb'
          (512 * block) 512 at value
      rw [indexSame] at value
      exact value
    have saltData (ordinal : Nat) (present : ordinal < positions.card) :
        readBuffer ready (10871640096 + (16 + 32 * 24) * ordinal) 16 = salts (indices ordinal) := by
      rw [read_buffer_memory_congr _ _ memory]
      have copied := check_opening_proof_salt trapdoor positions root (message.restrict positions)
        (784 * ordinal) (by rw [bytesEq]; omega)
      exact copied.trans (opening_output_records committed positions batch ordinal present).1
    have pathData (ordinal : Nat) (present : ordinal < positions.card) (level : Nat) (inside : level < 24) :
        readBuffer ready (10871640096 + (16 + 32 * 24) * ordinal + 16 + 32 * level) 32 =
          heap (((LENGTH + (indices ordinal).val) / 2 ^ level) ^^^ 1) := by
      rw [read_buffer_memory_congr _ _ memory]
      have copied := check_opening_proof_digest trapdoor positions root (message.restrict positions)
        (784 * ordinal + 16 + 32 * level) (by rw [bytesEq]; omega)
      have record := (opening_output_records committed positions batch ordinal present).2 level inside
      have joined := copied.trans (by simpa only [Nat.add_assoc] using record)
      change readBuffer initial (10871640096 + (784 * ordinal + 16 + 32 * level)) 32 =
        heap (((LENGTH + (indices ordinal).val) / 2 ^ level) ^^^ 1) at joined
      simpa only [Nat.add_assoc] using joined
    have accepted := check_loop_honest oracle ready message heap salts indices
      24 4294971392 6576672800 10871640096 6442455072 positions.card
      (by decide) (by decide) registers.2.2.2.2.2.2 registers.1
      rootPointer valuePointer proofPointer indexPointer
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega)
      targetData indexData valueData saltData pathData correct.2.2 correct.2.1
    exact ⟨lenOk, accepted⟩

private theorem scheme_commit (program : Submission) (message : Message) :
    program.scheme.commit message = program.readCommit <$> program.run .commit message := rfl

private theorem supported_commit_accepts (oracle : Oracle) (message : Message)
    (result : (Commitment × submission.scheme.Trapdoor) × Nat)
    (reachable : result ∈ support (oracle.run (submission.scheme.commit message)))
    (positions : Positions) :
    (oracle.eval (submission.scheme.check result.1.1 positions (message.restrict positions)
      (submission.readProof (openingResult result.1.2 positions)))).1 = true := by
  rw [scheme_commit] at reachable
  change result ∈ support (oracle.run (submission.readCommit <$>
    submission.run .commit (message : Input submission.sizes .commit))) at reachable
  rw [oracle_run_map] at reachable
  simp only [support_map] at reachable
  obtain ⟨execution, reached, rfl⟩ := reachable
  exact honest_check_accepts oracle message execution.1.state
    (commit_run_matches oracle message execution reached) positions

/-- Perfect completeness of the submitted machine-derived scheme, for every fixed
oracle, message, and opening set, with probability one over the actual private coins. -/
theorem submission_completeness : submission.scheme.Completeness := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root, trapdoor⟩, commitCalls⟩, committed, rest⟩ := reached
  rw [opening_scheme_execution trapdoor positions, oracle_run_pure] at rest
  simp only [support_pure, Set.mem_singleton_iff] at rest
  obtain ⟨opened, rfl, rfl⟩ := rest
  exact supported_commit_accepts oracle message ((root, trapdoor), commitCalls) committed positions

end CommitGolfCandidate
