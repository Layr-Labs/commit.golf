import CommitGolfCandidate.TwoPermutationPackedUnpackPrefix
import CommitGolfCandidate.InputMemory

/-! Loader bytes of the proof buffer, and the unpacked input. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.ProofCodec
open TwoPermutationPrototype.Checker (checker_positions_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- The checker input with its proof replaced by the unpacked proof (unchanged if malformed). -/
def unpackInput (input : CheckInput) : CheckInput :=
  { input with proof := (unpack input.positions.card input.proof).getD input.proof }

theorem unpack_input_proof (input : CheckInput)
    (wf : WellFormed input.positions.card input.proof.length) :
    (unpackInput input).proof = List.ofFn (fun i : Fin (unpackedLength input.positions.card
      (packedCount input.positions.card input.proof.length)) =>
        unpackedByte input.proof input.positions.card
          (packedCount input.positions.card input.proof.length) i.val) := by
  simp [unpackInput, unpack, wf]

theorem input_byte_high (X : CheckInput) (a : Nat) (lo : proofBase ≤ a) :
    inputByte Assembly.submission .check X a = X.proof[a - proofBase]?.getD 0 := by
  have card := checker_positions_bound X
  unfold proofBase at lo
  have outsideRoot : ¬ (Assembly.submission.layout.commitment ≤ a ∧
      a < Assembly.submission.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬ (4294971392 ≤ a ∧ a < 4294971424); omega
  have outsideIndices : ¬ (Assembly.submission.layout.indices ≤ a ∧
      a < Assembly.submission.layout.indices+8*X.positions.card) := by
    change ¬ (5905584160 ≤ a ∧ a < 5905584160+8*X.positions.card); omega
  have outsideValues : ¬ (Assembly.submission.layout.values ≤ a ∧
      a < Assembly.submission.layout.values+(LEAF_SIZE/8)*X.positions.card) := by
    change ¬ (6039801952 ≤ a ∧ a < 6039801952+256*X.positions.card); omega
  have data : (Assembly.submission.image .check).data = [] := rfl
  have base : Assembly.submission.layout.proof = proofBase := rfl
  by_cases inside : a < proofBase + X.proof.length
  · have selected : proofBase ≤ a ∧ a < proofBase+X.proof.length := by
      unfold proofBase at *; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
      positionsBuffer, valuesBuffer, Finset.length_sort, Finset.card_attach,
      outsideRoot, outsideIndices, outsideValues, decide_false, base, selected, and_self, decide_true]
  · have notSel : ¬ (proofBase ≤ a ∧ a < proofBase+X.proof.length) := by
      unfold proofBase at *; omega
    have none : X.proof[a - proofBase]? = none := by
      apply List.getElem?_eq_none; unfold proofBase at *; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
      positionsBuffer, valuesBuffer, Finset.length_sort, Finset.card_attach,
      outsideRoot, outsideIndices, outsideValues, decide_false, base, notSel, List.find?_nil, data,
      List.getElem?_nil, Option.getD_none, ite_self, none]

theorem input_byte_low (X : CheckInput) (Q : Proof) (a : Nat) (lo : a < proofBase) :
    inputByte Assembly.submission .check { X with proof := Q } a = inputByte Assembly.submission .check X a := by
  have notSel : ¬ Assembly.submission.layout.proof ≤ a := by
    change ¬ 10334769248 ≤ a; unfold proofBase at lo; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, notSel, false_and, decide_false]

/-- Bytes of the initial checker state, by address. -/
theorem initial_byte (X : CheckInput) (a : Word) :
    (Assembly.submission.initialState .check X).getByte a = inputByte Assembly.submission .check X a.toNat := by
  have h := initial_input_byte Assembly.submission .check X a.toNat a.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

theorem start_byte (X : CheckInput) (a : Word) :
    (unpackStart X).getByte a = inputByte Assembly.submission .check X a.toNat := by
  rw [← initial_byte]; rfl

theorem start_proof_byte (X : CheckInput) (p : Nat) (h : p < 2^34) :
    (unpackStart X).getByte (BitVec.ofNat 64 (proofBase + p)) = X.proof.getD p 0 := by
  rw [start_byte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold proofBase; omega),
    input_byte_high _ _ (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD]


/-! ### Steps with natural-number views -/

theorem getByte_of_mem {s t : MachineState} (h : s.mem = t.mem) (a : Word) : s.getByte a = t.getByte a := by
  unfold MachineState.getByte MachineState.getMem; rw [h]

theorem lbu_step (s : MachineState) (v : Reg → Nat) (hv : View s v) (index : Nat) (rd rs : Reg)
    (off : BitVec 12) (bounded : index < 506) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base (.LBU rd rs off)))
    (addr : Nat) (haddr : v rs + (signExtend12 off).toNat = addr) (room : addr + 1 ≤ 2^36) :
    Hop s (execInstrBr s (.LBU rd rs off)) 1 1 ∧
    View (execInstrBr s (.LBU rd rs off)) (setV v rd (s.getByte (BitVec.ofNat 64 addr)).toNat) ∧
    (execInstrBr s (.LBU rd rs off)).pc = BitVec.ofNat 64 (4096+4*(index+1)) ∧
    (execInstrBr s (.LBU rd rs off)).mem = s.mem := by
  have ea : s.getReg rs + signExtend12 off = BitVec.ofNat 64 addr := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hv rs, haddr, BitVec.toNat_ofNat]
  refine ⟨hop_one s index _ bounded pc decoded (lbu_ordinary s rd rs off (by
    rw [ea, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; unfold MEMORY_BYTES; omega)), ?_, ?_,
    lbu_mem s rd rs off⟩
  · have := view_lbu s v hv rd rs off; rwa [ea] at this
  · rw [lbu_exec]; change s.pc + 4 = _; rw [pc, pc_next]

theorem sb_step (s : MachineState) (v : Reg → Nat) (hv : View s v) (index : Nat) (rs1 rs2 : Reg)
    (off : BitVec 12) (bounded : index < 506) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base (.SB rs1 rs2 off)))
    (addr : Nat) (haddr : v rs1 + (signExtend12 off).toNat = addr) (room : addr + 1 ≤ 2^36) :
    Hop s (execInstrBr s (.SB rs1 rs2 off)) 1 1 ∧
    View (execInstrBr s (.SB rs1 rs2 off)) v ∧
    (execInstrBr s (.SB rs1 rs2 off)).pc = BitVec.ofNat 64 (4096+4*(index+1)) ∧
    ∀ q, (execInstrBr s (.SB rs1 rs2 off)).getByte q =
      if q = BitVec.ofNat 64 addr then BitVec.ofNat 8 (v rs2) else s.getByte q := by
  have ea : s.getReg rs1 + signExtend12 off = BitVec.ofNat 64 addr := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hv rs1, haddr, BitVec.toNat_ofNat]
  refine ⟨hop_one s index _ bounded pc decoded (sb_ordinary s rs1 rs2 off (by
    rw [ea, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; unfold MEMORY_BYTES; omega)),
    view_sb s v hv rs1 rs2 off, ?_, ?_⟩
  · rw [sb_exec]; change s.pc + 4 = _; rw [pc, pc_next]
  · intro q
    rw [sb_byte, ea]
    have : (s.getReg rs2).truncate 8 = BitVec.ofNat 8 (v rs2) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hv rs2]
    rw [this]

theorem beq_step (s : MachineState) (v : Reg → Nat) (hv : View s v) (index : Nat) (a b : Reg)
    (off : BitVec 13) (bounded : index < 506) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base (.BEQ a b off)))
    (target : Nat) (ht : BitVec.ofNat 64 (4096+4*index) + signExtend13 off = BitVec.ofNat 64 (4096+4*target)) :
    Hop s (s.setPC (if v a = v b then BitVec.ofNat 64 (4096+4*target)
      else BitVec.ofNat 64 (4096+4*(index+1)))) 1 1 := by
  have h := hop_one s index _ bounded pc decoded (branch_ordinary _ _ rfl)
  rw [beq_exec s v hv, pc, ht, pc_next] at h
  exact h

theorem bgeu_step (s : MachineState) (v : Reg → Nat) (hv : View s v) (index : Nat) (a b : Reg)
    (off : BitVec 13) (bounded : index < 506) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base (.BGEU a b off)))
    (target : Nat) (ht : BitVec.ofNat 64 (4096+4*index) + signExtend13 off = BitVec.ofNat 64 (4096+4*target)) :
    Hop s (s.setPC (if v a < v b then BitVec.ofNat 64 (4096+4*(index+1))
      else BitVec.ofNat 64 (4096+4*target))) 1 1 := by
  have h := hop_one s index _ bounded pc decoded (branch_ordinary _ _ rfl)
  rw [bgeu_exec s v hv, pc, ht, pc_next] at h
  exact h

theorem jal_step (s : MachineState) (index : Nat) (off : BitVec 21) (bounded : index < 506)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base (.JAL .x0 off)))
    (target : Nat) (ht : BitVec.ofNat 64 (4096+4*index) + signExtend21 off = BitVec.ofNat 64 (4096+4*target)) :
    Hop s (s.setPC (BitVec.ofNat 64 (4096+4*target))) 1 1 := by
  have h := hop_one s index _ bounded pc decoded (branch_ordinary _ _ rfl)
  rw [jal0_exec, pc, ht] at h
  exact h

theorem lor_shift (a b i : Nat) (h : a < 2^i) : a ||| b * 2^i = a + b * 2^i := by
  rw [← Nat.shiftLeft_eq, Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt h]; omega

theorem and_low (x i : Nat) : x &&& (2^i - 1) = x % 2^i := Nat.and_two_pow_sub_one_eq_mod x i

def tempsOnly (is : List Instr) : Bool := is.all (fun i => unpackTemps.contains (aluDest i))

theorem foldl_stepV_frame (is : List Instr) (h : tempsOnly is = true) (v : Reg → Nat) (r : Reg)
    (hr : r ∉ unpackTemps) : is.foldl stepV v r = v r := by
  apply foldl_stepV_other
  intro i hi e
  simp only [tempsOnly, List.all_eq_true] at h
  have := h i hi
  rw [e] at this
  exact hr (by simpa using this)

theorem setV_frame (v : Reg → Nat) (rd : Reg) (x : Nat) (hd : rd ∈ unpackTemps) (r : Reg)
    (hr : r ∉ unpackTemps) : setV v rd x r = v r := by
  simp only [setV]
  rw [if_neg (fun (h : r = rd ∧ rd ≠ .x0) => hr (h.1 ▸ hd))]

end TwoPermutationPrototype.Packed.Checker
