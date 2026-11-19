import CommitGolfCandidate.GroupOpenCapEmitPrefix

/-! T238 cap emit, plain node (`count ≠ 0`): after the shared prefix, WK (word 855) `beq x30,x0` falls through,
`addi x30,x30,-1; sh x31,28(x21)` stores halfword 14 of the node, `jal` back to word 700, `addi x21,x21,30`;
`CapCopy.cycles dest+9` cycles, one 30-byte slot. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (capDigestAddress cap_digest_bounds)
set_option maxRecDepth 8192

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

private theorem half_store_eq (state : MachineState) (address : Word) (value : BitVec 16) :
    state.setHalfword address value = state.setMem (alignToDword address)
      (replaceHalfword (state.getMem (alignToDword address)) ((byteOffset address)/2) value) := rfl

@[local simp] private theorem reg_set_half (state : MachineState) (address : Word) (value : BitVec 16) (reg : Reg) :
    (state.setHalfword address value).getReg reg = state.getReg reg := by
  rw [half_store_eq]; exact Opening.getReg_setMem _ _ _ _

private theorem trunc_ext (h : BitVec 16) : ((h.zeroExtend 64).truncate 16) = h := by
  apply BitVec.eq_of_toNat_eq
  have fit : h.toNat < 2^16 := h.isLt
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt fit, Nat.mod_eq_of_lt (show h.toNat < 2^64 by omega)]

private theorem succ_word (n : Nat) : BitVec.ofNat 64 (n+1) = BitVec.ofNat 64 n+1 := by
  rw [BitVec.ofNat_add]
  rfl

private theorem jal_zero_mem (s : MachineState) (offset : BitVec 21) :
    (execInstrBr s (.JAL .x0 offset)).mem = s.mem := by
  simp [execInstrBr]

private theorem jal_zero_reg (s : MachineState) (offset : BitVec 21) (r : Reg) :
    (execInstrBr s (.JAL .x0 offset)).getReg r = s.getReg r := by
  simp [execInstrBr]

private theorem minus_one_word (c : Nat) (small : c+1 < 2^64) :
    BitVec.ofNat 64 (c+1) + signExtend12 (4095#12) = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show signExtend12 (4095#12) = BitVec.ofNat 64 (2^64-1) by decide,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem emit_cap238_plain (groups : List Nat) (state : MachineState) (node dest count : Nat)
    (bounded : node < 512) (position : CapPosition groups state node dest)
    (counter : state.getReg .x30 = BitVec.ofNat 64 count) (positive : 0 < count) (small : count ≤ 7)
    (pc : state.pc = 0x1a70) (separate : Opening.proofBase ≤ dest) (aligned : dest%2=0) (fits : dest+30 ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after (CapCopy.cycles dest+9) ∧ after.pc = 0x1af4 ∧
      CapPosition groups after node (dest+30) ∧
      after.getReg .x30 = BitVec.ofNat 64 (count-1) ∧
      (∀ b<30, after.getByte (BitVec.ofNat 64 (dest+b)) =
        state.getByte (BitVec.ofNat 64 (capDigestAddress node+b))) ∧
      (∀ a<2^64, ¬EmitTouched dest count a →
        after.getByte (BitVec.ofNat 64 a) = state.getByte (BitVec.ofNat 64 a)) := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  obtain ⟨srcAlign, srcBelow⟩ := cap_digest_bounds node bounded
  obtain ⟨mid, run, pcMid, x21Mid, topMid, regsMid, bytesMid, frameMid, wordsMid⟩ :=
    cap_emit_prefix groups state node dest bounded position pc separate aligned fits
  have x30Mid : mid.getReg .x30 = BitVec.ofNat 64 count := (regsMid .x30 (by decide) (by decide)).trans counter
  have ne0 : BitVec.ofNat 64 count ≠ mid.getReg .x0 := by
    intro h
    have := congrArg BitVec.toNat h
    change (BitVec.ofNat 64 count).toNat = (0#64).toNat at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have cond : (mid.getReg .x30 == mid.getReg .x0) = false := by
    rw [x30Mid]
    exact beq_false_of_ne ne0
  -- 855 `beq x30,x0,+16`, not taken
  have run5 := beq_step mid 855 .x30 .x0 16#13 (by decide) pcMid (by decide +kernel)
  let s5 := execInstrBr mid (.BEQ .x30 .x0 16#13)
  have e5 : s5 = mid.setPC (mid.pc + 4) := by
    simp only [s5, execInstrBr, cond, Bool.false_eq_true, ↓reduceIte]
  have pc5 : s5.pc = BitVec.ofNat 64 (4096+4*856) := by
    rw [e5]
    change mid.pc + 4 = _
    rw [pcMid]
    decide +kernel
  have mem5 : s5.mem = mid.mem := by rw [e5]; rfl
  have regs5 (r : Reg) : s5.getReg r = mid.getReg r := by rw [e5]; exact MachineState.getReg_setPC ..
  -- 856 `addi x30,x30,-1`
  have step6 := row_step s5 856 (.ADDI .x30 .x30 4095#12) (by decide) pc5 (by decide +kernel) rfl rfl
  let s6 := execInstrBr s5 (.ADDI .x30 .x30 4095#12)
  have pc6 : s6.pc = BitVec.ofNat 64 (4096+4*857) := step6.2
  have mem6 : s6.mem = mid.mem := by simp [s6, execInstrBr, mem5]
  have reg6 (r : Reg) (other : r ≠ .x30) : s6.getReg r = s5.getReg r := by
    simp [s6, execInstrBr, Ne.symm other]
  have x30_6 : s6.getReg .x30 = BitVec.ofNat 64 (count-1) := by
    have e : s6.getReg .x30 = s5.getReg .x30 + signExtend12 (4095#12) := by simp [s6, execInstrBr]
    rw [e, regs5, x30Mid]
    obtain ⟨c, rfl⟩ : ∃ c, count = c+1 := ⟨count-1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact minus_one_word c (by omega)
  -- 857 `sh x31,28(x21)`
  have x21_6 : s6.getReg .x21 = BitVec.ofNat 64 dest := by rw [reg6 .x21 (by decide), regs5, x21Mid]
  have addr7 : s6.getReg .x21 + signExtend12 (28#12) = BitVec.ofNat 64 (dest+28) := by
    rw [x21_6, show signExtend12 (28#12) = BitVec.ofNat 64 28 by decide +kernel, ← BitVec.ofNat_add]
  have step7 := row_step s6 857 (.SH .x21 .x31 28#12) (by decide) pc6 (by decide +kernel) rfl
    (by change accessValid (s6.getReg .x21 + signExtend12 (28#12)) 2 = true
        rw [addr7]; exact half_access _ (by omega) (by omega))
  let s7 := execInstrBr s6 (.SH .x21 .x31 28#12)
  have pc7 : s7.pc = BitVec.ofNat 64 (4096+4*858) := step7.2
  have top6 : (s6.getReg .x31).truncate 16 = halfAt state (capDigestAddress node+28) := by
    rw [reg6 .x31 (by decide), regs5, topMid]
    exact trunc_ext _
  have mem7 : s7.mem = (s6.setHalfword (BitVec.ofNat 64 (dest+28)) (halfAt state (capDigestAddress node+28))).mem := by
    show (s6.setHalfword (s6.getReg .x21 + signExtend12 (28#12)) ((s6.getReg .x31).truncate 16)).mem = _
    rw [addr7, top6]
  have reg7 (r : Reg) : s7.getReg r = s6.getReg r := by simp [s7, execInstrBr]
  -- 858 `jal x0,-632` to word 700
  have step8 := row_step s7 858 (.JAL .x0 2096520#21) (by decide) pc7 (by decide +kernel) rfl rfl
  let s8 := execInstrBr s7 (.JAL .x0 2096520#21)
  have pc8 : s8.pc = BitVec.ofNat 64 (4096+4*700) := step8.2.trans (by decide +kernel)
  -- 700 `addi x21,x21,30`
  have step9 := row_step s8 700 (.ADDI .x21 .x21 30#12) (by decide) pc8 (by decide +kernel) rfl rfl
  let s9 := execInstrBr s8 (.ADDI .x21 .x21 30#12)
  have mem8 : s8.mem = s7.mem := jal_zero_mem s7 _
  have reg8 (r : Reg) : s8.getReg r = s7.getReg r := jal_zero_reg s7 _ r
  have mem9 : s9.mem = s7.mem := by simp [s9, execInstrBr, mem8]
  have reg9 (r : Reg) (other : r ≠ .x21) : s9.getReg r = s7.getReg r := by
    simp [s9, execInstrBr, Ne.symm other, reg8]
  have x21_9 : s9.getReg .x21 = BitVec.ofNat 64 (dest+30) := by
    have e : s9.getReg .x21 = s8.getReg .x21 + signExtend12 (30#12) := by simp [s9, execInstrBr]
    have f : s8.getReg .x21 = s7.getReg .x21 := reg8 .x21
    rw [e, f, reg7, x21_6, show signExtend12 (30#12) = BitVec.ofNat 64 30 by decide +kernel, ← BitVec.ofNat_add]
  have evenW : (BitVec.ofNat 64 (dest+28)).toNat % 2 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show dest+28 < 2^64 by omega)]
    omega
  have apart (q : Nat) (qsmall : q < 2^64) (away : q ≠ dest+28 ∧ q ≠ dest+28+1) :
      BitVec.ofNat 64 q ≠ BitVec.ofNat 64 (dest+28) ∧ BitVec.ofNat 64 q ≠ BitVec.ofNat 64 (dest+28)+1 := by
    refine ⟨fun e => away.1 (Opening.nat_address_injective qsmall (by omega) e), fun e => ?_⟩
    rw [← succ_word] at e
    exact away.2 (Opening.nat_address_injective qsmall (by omega) e)
  refine ⟨s9, ?_,
    step9.2.trans (by decide +kernel), ?_, ?_, ?_, ?_⟩
  · exact ((((run.next run5).next step6.1).next step7.1).next step8.1).next step9.1
  · apply cap_position_kept position
    · intro r h7 h21 _ _ h30 h31
      rw [reg9 r h21, reg7, reg6 r h30, regs5]
      exact regsMid r h7 h31
    · intro a below
      calc s9.getMem (BitVec.ofNat 64 a)
          = (s6.setHalfword (BitVec.ofNat 64 (dest+28)) (halfAt state (capDigestAddress node+28))).getMem
              (BitVec.ofNat 64 a) := by simp only [MachineState.getMem, mem9, mem7]
        _ = s6.getMem (BitVec.ofNat 64 a) := by
          rw [half_store_eq, MachineState.getMem_setMem_ne]
          intro e
          have h := congrArg BitVec.toNat e
          rw [align_any (dest+28) (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2^64 by omega)] at h
          omega
        _ = mid.getMem (BitVec.ofNat 64 a) := by simp only [MachineState.getMem, mem6]
        _ = state.getMem (BitVec.ofNat 64 a) := wordsMid a below
    · exact x21_9
  · rw [reg9 .x30 (by decide), reg7, x30_6]
  · intro b inside
    rw [emit_byte_of_mem mem9, emit_byte_of_mem mem7]
    by_cases low : b < 28
    · rw [ProjectedHalfword.store_outside _ _ _ _ evenW (apart (dest+b) (by omega) ⟨by omega, by omega⟩),
        emit_byte_of_mem mem6]
      exact bytesMid b low
    · obtain ⟨c, rfl, hc⟩ : ∃ c, b = 28+c ∧ c < 2 := ⟨b-28, by omega, by omega⟩
      rw [show dest+(28+c) = dest+28+c by omega, show capDigestAddress node+(28+c) = capDigestAddress node+28+c by omega,
        emit_stored_byte s6 (dest+28) c _ (by omega) (by omega) hc]
      unfold halfAt
      rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
      · simp only [Nat.mul_zero, Nat.add_zero]
        rw [append_low_byte]
      · simp only [Nat.mul_one]
        rw [append_high_byte]
  · intro a asmall untouched
    unfold EmitTouched at untouched
    have away : a < dest ∨ dest+30 ≤ a := by
      by_contra inside
      exact untouched (Or.inl ⟨by omega, by rw [if_neg (show count ≠ 0 by omega)]; omega⟩)
    rw [emit_byte_of_mem mem9, emit_byte_of_mem mem7,
      ProjectedHalfword.store_outside _ _ _ _ evenW (apart a asmall ⟨by omega, by omega⟩), emit_byte_of_mem mem6]
    exact frameMid a asmall (by omega)

end TwoPermutationPrototype.GroupedOpening
