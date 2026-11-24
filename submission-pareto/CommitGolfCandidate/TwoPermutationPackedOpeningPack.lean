import CommitGolfCandidate.FastPackRecords

namespace TwoPermutationPrototype.PackedOpening.Pack
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setReg set_byte_read


/-- Fuel from the exit block at `0x1a5c` to the head-stream conversion pass. -/
def exitSteps (k b : Nat) : Nat :=
  46 + 1311*k + 568*b + 7*(rounded k b - count k b) + 5*rounded k b

/-- Cycles from the exit block at `0x1a5c` to the head-stream conversion pass. -/
def exitCycles (k b : Nat) : Nat :=
  64 + 1494*k + 922*b + 7*(rounded k b - count k b) + 5*rounded k b

set_option maxHeartbeats 1000000 in
theorem prepare_pack (k b base : Nat) (P : List Byte) (s : MachineState) (pc : s.pc = 0x1a5c)
    (x16 : s.getReg .x16 = BitVec.ofNat 64 k) (x20 : s.getReg .x20 = BitVec.ofNat 64 base)
    (len : s.getReg .x21 - s.getReg .x20 = BitVec.ofNat 64 (498*k + 30*b))
    (fits : 498*k + 30*b ≤ capacityBytes) (room : base + 2^34 ≤ 2^36)
    (src : Source k b base P s) :
    ∃ final : MachineState,
      Runs s final (exitSteps k b) (exitCycles k b) ∧ final.pc=pcOf 142 ∧
      final.getReg .x11 = BitVec.ofNat 64 (ProofCodec.packedLength k (count k b)) ∧
      PackRegs k b base final ∧
      ∀ a : Word, final.getByte a =
        if base ≤ a.toNat ∧ a.toNat < base + ProofCodec.packedLength k (count k b) then
          ProofCodec.packedByte P k (count k b) (a.toNat - base)
        else if scratch base ≤ a.toNat ∧ a.toNat < scratch base + rounded k b + k then
          stashed P k b (a.toNat - scratch base)
        else s.getByte a := by
  have fits' := fits
  unfold capacityBytes at fits'
  have hR : rounded k b ≤ 15*k + b + 3 := by unfold rounded count; omega
  -- exit block
  have r0 := runs_enter s pc
  obtain ⟨epc, e5, e10, e11, ekeep, emem⟩ := enter_facts s pc
  let e := enterPack s
  -- prelude
  have pre := prelude_run k b base P s e epc e5 e10
    ((ekeep .x16 (by decide) (by decide) (by decide)).trans x16)
    ((ekeep .x20 (by decide) (by decide) (by decide)).trans x20) (e11.trans len) emem fits room
  have r1 := (runs_path _ e pre.1).cast (s2 := 14) (c2 := 23) rfl (by decide)
  -- gather loop
  obtain ⟨s1, g1, r2⟩ := gather_loop k b base P s (run e prelude) pre.2 src fits room
  have ge := gather_exit k b base P s s1 g1
  have r3 := (runs_path _ s1 ge.1).cast (s2 := 3) (c2 := 3) rfl (by decide)
  -- heads loop
  obtain ⟨sh, h1, rh⟩ := heads_loop k b base P s _ ge.2 src fits room
  have he := heads_exit k b base P s sh h1
  have rh' := (runs_path _ sh he.1).cast (s2 := 8) (c2 := 17) rfl (by decide)
  have unpacked : Unpacked k b base P sh := fun a lo hi => h1.read src fits a lo hi
  have heads : ∀ r < k, sh.getByte (BitVec.ofNat 64 (scratch base + rounded k b + r)) =
      ProofCodec.headByte P r := by
    intro r hr
    have fit : scratch base + rounded k b + r < 2^64 := by unfold scratch; omega
    rw [h1.mem, toNat_w _ fit, if_pos (by omega), stashed, if_neg (by omega),
      show scratch base + rounded k b + r - scratch base - rounded k b = r by omega]
  -- pack loop
  obtain ⟨s2, p2, r4⟩ := records_and_footer k b base P sh _ he.2 unpacked heads fits room
    (getByte_of_mem (run_mem heWords sh (by decide)))
  have pe := pack_exit k b base P sh s2 p2
  have r5 := (runs_path _ s2 pe.1).cast (s2 := 3) (c2 := 3) rfl (by decide)
  -- remainder loop
  have scr : ∀ j < rounded k b, sh.getByte (BitVec.ofNat 64 (scratch base + j)) = gathered P k b j := by
    intro j hj
    have fit : scratch base + j < 2^64 := by unfold scratch; omega
    rw [h1.mem, toNat_w _ fit, if_pos (by omega), Nat.add_sub_cancel_left, stashed, if_pos hj]
  obtain ⟨s3, p3, r6⟩ := rem_loop k b base P sh _ pe.2 scr fits room
  obtain ⟨ok, fpc, f11, f5, f10, fmem⟩ := rem_exit k b base P sh s3 p3 fits
  have r7 := (runs_path _ s3 ok).cast (s2 := 5) (c2 := 5) rfl (by decide)
  have all := (((((((((r0.trans r1).trans r2).trans r3).trans rh).trans rh').trans r4).trans r5).trans r6).trans r7)
  let f := run s3 remExit
  have transfer := (runs_step f 141 (by decide) fpc rfl rfl).cast
    (s2 := 1) (c2 := 1) rfl rfl
  refine ⟨execInstrBr f (.JAL .x0 4), (all.trans transfer).cast ?_ ?_, ?_, ?_, ?_, ?_⟩
  · unfold exitSteps rounded; omega
  · unfold exitCycles rounded; omega
  · change f.pc+signExtend21 4=pcOf 142
    rw [fpc]
    decide
  · simpa [execInstrBr] using f11
  · exact (p3.regs.keep remExit (by decide)).keep [141] (by decide)
  · intro a
    have transferByte : (execInstrBr f (.JAL .x0 4)).getByte a=f.getByte a := by
      simp only [execInstrBr,getByte_setPC,getByte_setReg]
    rw [transferByte]
    rw [getByte_of_mem fmem, p3.mem, h1.mem]
    have e1 : bodyLen k b + 3 * (rounded k b / 4) = ProofCodec.packedLength k (count k b) := by
      unfold bodyLen ProofCodec.packedLength ProofCodec.bodyLength rounded; omega
    rw [e1]

theorem exit_cycles_le (k b : Nat) (hk : k ≤ 128) (hb : b ≤ 128) : exitCycles k b ≤ 319552 := by
  unfold exitCycles rounded count
  generalize hm : (15*k + b + 3) / 4 = m
  have h1 : 4*m ≤ 15*k + b + 3 := by omega
  have h2 : 15*k + b ≤ 4*m := by omega
  have h3 : m ≤ 512 := by omega
  omega

theorem exit_cycles_max : exitCycles 128 128 = 319552 := by decide

theorem exit_steps_le (k b : Nat) (hk : k ≤ 128) (hb : b ≤ 128) : exitSteps k b ≤ 250798 := by
  unfold exitSteps rounded count
  generalize hm : (15*k + b + 3) / 4 = m
  have h1 : 4*m ≤ 15*k + b + 3 := by omega
  have h2 : 15*k + b ≤ 4*m := by omega
  have h3 : m ≤ 512 := by omega
  omega

theorem exit_steps_le_cardinality (k b : Nat) (hk : k ≤ 16777216) (hb : b ≤ 128) :
    exitSteps k b ≤ 241407434407 := by
  unfold exitSteps rounded count
  generalize hm : (15*k + b + 3) / 4 = m
  have h1 : 4*m ≤ 15*k + b + 3 := by omega
  have h2 : 15*k + b ≤ 4*m := by omega
  have h3 : m ≤ 62914592 := by omega
  omega

theorem exit_steps_le_cycles (k b : Nat) : exitSteps k b ≤ exitCycles k b := by
  unfold exitSteps exitCycles; omega

/-- The first-stage packed bytes as `ProofCodec.pack`, for an unpacked proof list. -/
theorem packed_bytes (k b : Nat) (P : List Byte) (hlen : P.length = 498*k + 30*b) (p : Nat)
    (hp : p < ProofCodec.packedLength k (count k b)) :
    ProofCodec.packedByte P k (count k b) p = (ProofCodec.pack k P).getD p 0 := by
  have hc : ProofCodec.unpackedCount k P.length = count k b := by
    rw [hlen, ProofCodec.unpackedCount, count]; omega
  rw [ProofCodec.getD_pack k P p (by rw [hc]; exact hp), hc]
end TwoPermutationPrototype.PackedOpening.Pack
