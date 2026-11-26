import CommitGolfCandidate.R4ParentCode
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Late (pcAt nodeAddress)
private theorem copyRoot (oracle : Oracle) (s : MachineState)
    (basePc : Nat) (srcReg dstReg : Reg) (srcBase dstBase srcOff dstOff : Nat)
    (hsrcReg : srcReg ≠ .x6) (hdstReg : dstReg ≠ .x6)
    (hdstOff : dstOff + 24 < 2048)
    (hsrcAl : (srcBase + srcOff) % 8 = 0) (hdstAl : (dstBase + dstOff) % 8 = 0)
    (hsrcBd : srcBase + srcOff + 32 ≤ MEMORY_BYTES) (hdstBd : dstBase + dstOff + 32 ≤ MEMORY_BYTES)
    (hdisj : srcBase + srcOff + 32 ≤ dstBase + dstOff ∨ dstBase + dstOff + 32 ≤ srcBase + srcOff)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hsrc : s.getReg srcReg = BitVec.ofNat 64 (srcBase+srcOff+32))
    (hdst : s.getReg dstReg = BitVec.ofNat 64 dstBase)
    (hfetch : ∀ k < 4, ∀ st : MachineState,
      (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * k)) →
        fetch (submission.image .commit) st = some (.base (.LD .x6 srcReg (BitVec.ofNat 12 (4064 + 8 * k))))) ∧
      (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * k + 1)) →
        fetch (submission.image .commit) st = some (.base (.SD dstReg .x6 (BitVec.ofNat 12 (dstOff + 8 * k)))))) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 8 s' 8 0 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 8)) ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      readBuffer s' (dstBase + dstOff) 32 = readBuffer s (srcBase + srcOff) 32 ∧
      MemPreservedOutside s s' (dstBase + dstOff) (dstBase + dstOff + 32) := by
  have hmemBd : MEMORY_BYTES < 2 ^ 64 := by unfold MEMORY_BYTES; decide
  have hind : ∀ m ≤ 4,
      ∃ sm,
        DetRun oracle (submission.image .commit) s (2 * m) sm (2 * m) 0 ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * m)) ∧
        (∀ r : Reg, r ≠ .x6 → sm.getReg r = s.getReg r) ∧
        (∀ k < m, sm.getMem (BitVec.ofNat 64 (dstBase + dstOff + 8 * k)) =
          s.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k))) ∧
        MemPreservedOutside s sm (dstBase + dstOff) (dstBase + dstOff + 8 * m) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨s, DetRun.refl _ _ _, by simpa using hpc, fun _ _ => rfl,
        fun _ hk => (Nat.not_lt_zero _ hk).elim, MemPreservedOutside.refl _ _ _⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hwordm, hpresm⟩ := ih (by omega)
      let insL := Instr.LD .x6 srcReg (BitVec.ofNat 12 (4064 + 8 * m))
      let insS := Instr.SD dstReg .x6 (BitVec.ofNat 12 (dstOff + 8 * m))
      let s1 := execInstrBr sm insL
      let s2 := execInstrBr s1 insS
      have hsrcAddr : sm.getReg srcReg + signExtend12 (BitVec.ofNat 12 (4064 + 8 * m)) =
          BitVec.ofNat 64 (srcBase + srcOff + 8 * m) := by
        rw [hregm srcReg hsrcReg, hsrc]
        have hm4 : m<4:=by omega
        rw [show 4064+8*m=4096-(32-8*m) by omega,add_signExtend12_neg' _ _ (by omega) (by omega) (by omega)]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hdstAddr : s1.getReg dstReg + signExtend12 (BitVec.ofNat 12 (dstOff + 8 * m)) =
          BitVec.ofNat 64 (dstBase + dstOff + 8 * m) := by
        have hd1 : s1.getReg dstReg = sm.getReg dstReg := by
          simp only [s1, insL, execInstrBr, MachineState.getReg_setPC,
            getReg_setReg_ne' .x6 dstReg (Ne.symm hdstReg)]
        rw [hd1, hregm dstReg hdstReg, hdst, add_signExtend12_ofNat_small _ (dstOff + 8 * m) (by omega)]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hstL : DetRun oracle (submission.image .commit) sm 1 s1 1 0 :=
        DetRun.step1 ((hfetch m (by omega) sm).1 hpcm)
          (ordinaryStep_LD sm .x6 srcReg _ (by
            rw [hsrcAddr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * m + 1)) := by
        rw [pc_exec_LD, hpcm, bv64_add4]; exact congrArg (BitVec.ofNat 64) (by omega)
      have hstS : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
        DetRun.step1 ((hfetch m (by omega) s1).2 hs1_pc)
          (ordinaryStep_SD s1 dstReg .x6 _ (by
            rw [hdstAddr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      have hs2_mem : s2.mem = (sm.setMem (BitVec.ofNat 64 (dstBase + dstOff + 8 * m))
          (sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * m)))).mem := by
        have hm1 : s1.mem = sm.mem := mem_exec_LD sm .x6 srcReg _
        have hx6 : s1.getReg .x6 = sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * m)) := by
          simp only [s1, insL, execInstrBr, MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hsrcAddr]
        simp only [s2, insS, execInstrBr, hdstAddr, hx6, c_mem_setPC, MachineState.setMem, hm1]
      have hp12 : MemPreservedOutside sm s2 (dstBase + dstOff + 8 * m) (dstBase + dstOff + 8 * (m + 1)) := by
        have hp := memPreserved_setMem sm (dstBase + dstOff + 8 * m)
          (sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * m))) (by omega) (by omega)
        exact (hp.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hs2_mem _ _)
      refine ⟨s2, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrunm.trans hstL).trans hstS, ?_, ?_, ?_, ?_⟩
      · rw [pc_exec_SD, hs1_pc, bv64_add4]; exact congrArg (BitVec.ofNat 64) (by omega)
      · intro r hr
        have h1 : s2.getReg r = s1.getReg r := reg_exec_SD s1 dstReg .x6 _ r
        have h2 : s1.getReg r = sm.getReg r := by
          simp only [s1, insL, execInstrBr, MachineState.getReg_setPC,
            getReg_setReg_ne' .x6 r (Ne.symm hr)]
        exact (h1.trans h2).trans (hregm r hr)
      · intro k hk
        by_cases hkm : k = m
        · subst hkm
          have hsrc_eq : sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k)) =
              s.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k)) :=
            hpresm.getMem_eq (by omega) (by omega) (by omega)
          rw [← hsrc_eq]
          simp only [MachineState.getMem, hs2_mem]
          exact MachineState.getMem_setMem_eq
        · rw [hp12.getMem_eq (by omega) (by omega) (by omega)]
          exact hwordm k (by omega)
      · exact (hpresm.mono (le_refl _) (by omega)).trans (hp12.mono (by omega) (le_refl _))
  obtain ⟨s4, hrun4, hpc4, hreg4, hword4, hpres4⟩ := hind 4 (le_refl _)
  refine ⟨s4, hrun4, hpc4, hreg4, ?_, hpres4⟩
  exact (read_digest_eq_iff s4 s (dstBase + dstOff) (srcBase + srcOff) hdstAl hsrcAl).mpr hword4


theorem exit (o : Oracle) (s : MachineState) (pc : s.pc=pcAt 21436) (src : s.getReg .x12=BitVec.ofNat 64 (nodeAddress 24 1))
    (dst : s.getReg .x26=4294971392) :
    ∃ t,DetRun o (submission.image .commit) s 10 t 10 0 ∧ t.pc=pcAt 21446 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t C_CMT 32=readBuffer s (nodeAddress 24 0) 32 ∧ MemPreservedOutside s t C_CMT C_TD := by
  have sites : ∀ j : Fin 4,hasOp (21436+2*j.val) (.LD .x6 .x12 (BitVec.ofNat 12 (4064+8*j.val))) ∧
      hasOp (21436+2*j.val+1) (.SD .x26 .x6 (BitVec.ofNat 12 (8*j.val))) := by decide
  obtain ⟨u,run,ip,_,root,mem⟩:=copyRoot o s 21436 .x12 .x26 (nodeAddress 24 0) C_CMT 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    pc src dst (fun k hk t=>⟨hasOp_sound (sites ⟨k,hk⟩).1 t,by simpa only [pcAt,Nat.zero_add] using hasOp_sound (sites ⟨k,hk⟩).2 t⟩)
  let v:=execInstrBr u (.ADDI .x5 .x0 1)
  let t:=execInstrBr v (.ADDI .x10 .x0 0)
  have f1:=hasOp_sound (by decide : hasOp 21444 (.ADDI .x5 .x0 1)) u ip
  have f2:=hasOp_sound (by decide : hasOp 21445 (.ADDI .x10 .x0 0)) v
    (show v.pc=pcAt 21445 from (congrArg (·+4) ip).trans rfl)
  have r1 : DetRun o (submission.image .commit) u 1 v 1 0:=DetRun.step1 f1 rfl
  have r2 : DetRun o (submission.image .commit) v 1 t 1 0:=DetRun.step1 f2 rfl
  exact ⟨t,(run.trans r1).trans r2,(congrArg (fun x : Word=>x+4+4) ip).trans rfl,rfl,rfl,
    (readBuffer_of_mem_eq (s1:=t) (s2:=u) rfl _ _).trans root,mem.trans (MemPreservedOutside.of_mem_eq (s1:=u) (s2:=t) rfl _ _)⟩
end CommitGolfCandidate.R4
