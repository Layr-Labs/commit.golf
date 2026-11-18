import CommitGolfCandidate.TwoPermutationPackedUnpackFinish
import CommitGolfCandidate.TwoPermutationPackedCheckerExit

/-! The proof-unpacking wrapper, end to end. From the state after word 0 it either reaches
word 2 in the checker's measured state for the unpacked input (well-formed proofs), or
reaches the reject block at `0x15b0` (malformed proofs). -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

/-- The machine state the original checker had after words 0 and 1, up to memory words the
program never reads: equal registers and PC, and equal bytes. The memory function itself can
differ at unaligned addresses, which no instruction can write. The bytes are only claimed
for a nonempty position set: with no positions, a few packed remainder bytes beyond the
unpacked length may stay in memory, and the empty-set branch never reads memory. -/
structure UnpackedView (input : CheckInput) (t : MachineState) : Prop where
  pc : t.pc = 4104
  factor : t.getReg .x6 = (Assembly.submission.initialState .check input).getReg .x16 * 498
  regs : ∀ r, r ≠ .x6 → t.getReg r = (Assembly.submission.initialState .check input).getReg r
  bytes : input.positions.card ≠ 0 → ∀ a, t.getByte a = (Assembly.submission.initialState .check input).getByte a

def unpackSteps (k L : Nat) : Nat :=
  64 + 28*packedCount k L + 14*k + ∑ i ∈ Finset.range (48*k + 30*packedCount k L), iterSteps k i

def unpackCycles (k L : Nat) : Nat :=
  91 + 28*packedCount k L + 17*k + ∑ i ∈ Finset.range (48*k + 30*packedCount k L), iterCycles k i

theorem start_x6 (input : CheckInput) : startView input .x6 = 498 := rfl

theorem unpack_steps_bound (k L : Nat) (wf : WellFormed k L) : unpackSteps k L ≤ 2^39 := by
  have sum : ∑ i ∈ Finset.range (48*k + 30*packedCount k L), iterSteps k i ≤
      (48*k + 30*packedCount k L) * 33 := by
    have := Finset.sum_le_card_nsmul (Finset.range (48*k + 30*packedCount k L)) (iterSteps k) 33
      (fun i _ => iter_steps_le k i)
    simpa using this
  obtain ⟨l, _, _, e⟩ := wf
  simp only [packedLength, bodyLength] at e
  unfold unpackSteps
  omega

theorem unpack_input_length (input : CheckInput) (wf : WellFormed input.positions.card input.proof.length) :
    (unpackInput input).proof.length = lenOf input := by
  rw [unpack_input_proof input wf, List.length_ofFn]
  obtain ⟨_, _, r, _⟩ := wf
  unfold lenOf countOf unpackedLength
  omega

theorem start_reg (input : CheckInput) (r : Reg) (h6 : r ≠ .x6) :
    (unpackStart input).getReg r = (Assembly.submission.initialState .check input).getReg r := by
  unfold unpackStart
  rw [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6)]

theorem getReg_with_mem (s : MachineState) (m : Word → Word) (r : Reg) :
    ({ s with mem := m } : MachineState).getReg r = s.getReg r := by cases r <;> rfl

theorem init_reg_proof (X : CheckInput) (Q : Proof) (r : Reg) (h : r ≠ .x17) :
    (Assembly.submission.initialState .check { X with proof := Q }).getReg r =
      (Assembly.submission.initialState .check X).getReg r := by
  simp only [Submission.initialState, TwoPermutationPrototype.Opening.getReg_setReg, getReg_with_mem,
    inputCount, Ne.symm h, false_and, ite_false]

theorem unpack_regs_same (input : CheckInput) (r : Reg) (h6 : r ≠ .x6) (h17 : r ≠ .x17) :
    (Assembly.submission.initialState .check (unpackInput input)).getReg r = (unpackStart input).getReg r :=
  (init_reg_proof input _ r h17).trans (start_reg input r h6).symm

theorem final_bytes (input : CheckInput) (wf : WellFormed input.positions.card input.proof.length)
    (sz : Sizes input) (nonempty : input.positions.card ≠ 0) (a : Word) :
    zeroMem input (countOf input + input.positions.card) a = (Assembly.submission.initialState .check (unpackInput input)).getByte a := by
  have len := sz.len
  have recs := sz.records
  have plen := unpack_input_length input wf
  have bound := a.isLt
  have longer : input.proof.length ≤ lenOf input := by
    obtain ⟨_, _, _, e⟩ := wf
    simp only [packedLength, bodyLength] at e
    unfold lenOf
    unfold countOf at recs ⊢
    omega
  rw [initial_byte]
  unfold zeroMem mainMem
  by_cases sc : scratchBase ≤ a.toNat ∧ a.toNat < scratchBase + (countOf input + input.positions.card)
  · rw [if_pos sc, input_byte_high _ _ (by unfold scratchBase proofBase at *; omega),
      List.getElem?_eq_none (by rw [plen]; unfold scratchBase proofBase at *; omega)]
    rfl
  rw [if_neg sc, if_neg (by omega)]
  by_cases body : proofBase + 0 ≤ a.toNat ∧ a.toNat < proofBase + lenOf input
  · have hi : a.toNat - proofBase < unpackedLength input.positions.card
        (packedCount input.positions.card input.proof.length) := by
      unfold lenOf countOf at body; unfold unpackedLength; omega
    rw [if_pos body, input_byte_high _ _ (by omega), unpack_input_proof input wf, List.getElem?_ofFn,
      dif_pos hi, Option.getD_some]
    rfl
  rw [if_neg body, start_byte]
  by_cases low : a.toNat < proofBase
  · exact (input_byte_low input _ _ low).symm
  · rw [input_byte_high _ _ (by omega), input_byte_high _ _ (by omega),
      List.getElem?_eq_none (by omega), List.getElem?_eq_none (by rw [plen]; omega)]

/-- (B) A malformed proof reaches the reject block within 27 steps. -/
theorem unpack_reject (input : CheckInput) (fits : input.proof.length ≤ 8355061248)
    (malformed : ¬ WellFormed input.positions.card input.proof.length) :
    ∃ steps cycles t, steps ≤ 27 ∧ ∀ fuel,
      execute packedImage (steps + 3 + fuel) (unpackStart input) false =
        pure ⟨.failure, headerRejectState t, cycles + 3, 0⟩ := by
  obtain ⟨t, steps, cycles, le, hop, pc⟩ := (prefix_run input fits).1 malformed
  refine ⟨steps, cycles, t, le, fun fuel => ?_⟩
  rw [Nat.add_assoc, hop (3+fuel), execute_header_reject t pc fuel]
  simp [Execution.charge]

/-- (A) A well-formed proof is unpacked in place, and the wrapper returns to word 2 in the
measured state of the unpacked input. -/
theorem unpack_run (input : CheckInput) (fits : input.proof.length ≤ 8355061248)
    (wf : WellFormed input.positions.card input.proof.length) :
    ∃ t, Hop (unpackStart input) t (unpackSteps input.positions.card input.proof.length)
      (unpackCycles input.positions.card input.proof.length) ∧ UnpackedView (unpackInput input) t := by
  have sz := sizes_of input wf fits
  have kb := sz.k
  have nb := sz.n
  have len := sz.len
  obtain ⟨t1, v1, h1, w1, p1, m1, pv⟩ := (prefix_run input fits).2 wf
  have d0 : DecodeAt input v1 0 t1 := ⟨⟨v1, w1, pv.x22, fun _ _ => rfl⟩, p1, fun a => by
    rw [getByte_of_mem m1, decodeMem, if_neg (by omega)]⟩
  obtain ⟨t2, v2, h2, w2, fr2, p2, m2⟩ := decode_phase input v1 pv wf t1 d0
  obtain ⟨t2', vM, h2', w2', mv, e22, p2', m2'⟩ := head_phase input v1 pv wf t2 v2 w2 fr2 p2 m2
  have a2 : MainAt input vM (lenOf input) t2' :=
    ⟨⟨vM, w2', e22, fun _ _ => rfl⟩, p2', fun a => (m2' a).trans (head_main_mem input a)⟩
  obtain ⟨t3, h3, ⟨⟨v3, w3, e3, fr3⟩, p3, m3⟩⟩ := main_loop input vM mv sz (lenOf input) t2' le_rfl a2
  -- leave the copy loop
  have g3 := beq_step t3 v3 w3 445 .x22 .x0 276 (by decide) p3 rfl 514 rfl
  rw [if_pos (by rw [e3, view_x0 w3])] at g3
  have x8 : v3 .x8 = countOf input := (fr3 .x8 (by decide)).trans mv.x8
  have x16 : v3 .x16 = input.positions.card := (fr3 .x16 (by decide)).trans mv.x16
  obtain ⟨hC, wC, pC, mC⟩ := block_run _ 514 clearStart v3 (view_pc_only _ _ (BitVec.ofNat 64 (4096+4*514)) w3)
    (by decide) rfl
    (by intro i hi; simp only [clearStart, List.length] at hi; interval_cases i <;> rfl) rfl
  have z0 : ZeroAt input vM 0 (clearStart.foldl execInstrBr (t3.setPC (BitVec.ofNat 64 (4096+4*514)))) :=
    ⟨⟨_, wC, cs_x22 v3 (view_x0 w3), cs_x23 v3 _ _ x8 x16 (by omega) (by omega), fun r hr => by
        rw [foldl_stepV_within clearStart mainWrites (by decide) _ r hr]; exact fr3 r hr⟩, pC,
      fun a => (getByte_of_mem mC a).trans ((m3 a).trans (by rw [zeroMem, if_neg (by omega)]))⟩
  obtain ⟨t5, h5, ⟨⟨v5, w5, e5, e5', fr5⟩, p5, m5⟩⟩ :=
    zero_loop input vM mv sz (countOf input + input.positions.card) 0 _ (by omega) z0
  -- leave the clearing loop
  have g5 := beq_step t5 v5 w5 516 .x22 .x23 20 (by decide) p5 rfl 521 rfl
  rw [if_pos (by rw [e5, e5'])] at g5
  obtain ⟨hF, wF, pF, mF⟩ := block_run _ 521 finalBlock v5 (view_pc_only _ _ _ w5) (by decide) rfl
    (by intro i hi; rw [show finalBlock.length = 20 from rfl] at hi; interval_cases i <;> rfl) rfl
  have jF := jal_step _ 541 2094996 (by decide) pF rfl 2 rfl
  refine ⟨_, (((((((h1.thenDo h2).thenDo h2').thenDo h3).thenDo g3).thenDo hC).thenDo h5).thenDo g5).thenDo hF
    |>.thenDo jF |>.cast ?_ ?_, ?_⟩
  · have l1 : clearStart.length = 2 := rfl
    have l2 : finalBlock.length = 20 := rfl
    rw [l1, l2]
    simp only [unpackSteps]
    unfold lenOf countOf
    omega
  · have c1 : blockCycles clearStart = 2 := rfl
    have c2 : blockCycles finalBlock = 23 := rfl
    rw [c1, c2]
    simp only [unpackCycles]
    unfold lenOf countOf
    omega
  -- the final state
  have v50 : v5 .x0 = 0 := view_x0 w5
  have keep : ∀ r, r ∉ unpackTemps → v5 r = startView input r := fun r hr =>
    (fr5 r (notin_sub _ _ (by decide) hr)).trans (mv.other r hr)
  have k16 := (unpack_regs_same input .x16 (by decide) (by decide))
  refine ⟨rfl, ?_, ?_, ?_⟩
  · -- t1 := 498k
    rw [k16]
    apply BitVec.eq_of_toNat_eq
    rw [MachineState.getReg_setPC, wF .x6, final_fold v5 v50, if_pos rfl, keep .x16 (by decide),
      keep .x6 (by decide), BitVec.toNat_mul, start_x6]
    rfl
  · intro r h6
    apply BitVec.eq_of_toNat_eq
    rw [MachineState.getReg_setPC, wF r, final_fold v5 v50, if_neg h6]
    by_cases t : r ∈ unpackTemps
    · rw [if_pos t, unpack_regs_same input r h6 (fun e => by subst e; exact absurd t (by decide))]
      exact (start_temps input r t).symm
    · rw [if_neg t]
      by_cases r17 : r = .x17
      · subst r17
        rw [if_pos rfl, fr5 .x28 (by decide), mv.x28]
        change _ = (BitVec.ofNat 64 (unpackInput input).proof.length).toNat
        rw [unpack_input_length input wf, BitVec.toNat_ofNat]
        unfold lenOf at len ⊢
        omega
      · rw [if_neg r17, keep r t, unpack_regs_same input r h6 r17]
        rfl
  · intro nonempty a
    rw [setPC_getByte, getByte_of_mem mF, setPC_getByte, m5]
    exact final_bytes input wf sz nonempty a

end TwoPermutationPrototype.Packed.Checker
