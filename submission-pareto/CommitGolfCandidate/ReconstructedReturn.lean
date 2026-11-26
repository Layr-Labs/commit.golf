import CommitGolf.Artifact
import CommitGolfCandidate.Execution
import CommitGolfCandidate.ReconstructedFetch
import CommitGolfCandidate.ReconstructedFrontier

namespace CommitGolfCandidate.Reconstruction.Return
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] ArtifactEncoding.decode

private def code := Artifact.submission.image .opening

private def pcIndex (i : Nat) := if i < 19 then 1641+i else 20+(i-19)

private def words : List (BitVec 32) :=
  [0x03f38513,0x00355513,0xff857513,0x12010113,0x7e813083,0x7e013403,
   0x7d813483,0x7d013903,0x7c813983,0x7c013a03,0x7b813a83,0x7b013b03,
   0x7a813b83,0x7a013c03,0x79813c83,0x79013d03,0x78813d83,0x7f010113,
   0x00008067,0x00050593,0x00052533,0x00100293,0x00000073]

private def ops : List Instr :=
  [.ADDI .x10 .x7 63,.SRLI .x10 .x10 3,.ANDI .x10 .x10 0xff8,.ADDI .x2 .x2 0x120,
   .LD .x1 .x2 0x7e8,.LD .x8 .x2 0x7e0,.LD .x9 .x2 0x7d8,
   .LD .x18 .x2 0x7d0,.LD .x19 .x2 0x7c8,.LD .x20 .x2 0x7c0,.LD .x21 .x2 0x7b8,
   .LD .x22 .x2 0x7b0,.LD .x23 .x2 0x7a8,.LD .x24 .x2 0x7a0,.LD .x25 .x2 0x798,
   .LD .x26 .x2 0x790,.LD .x27 .x2 0x788,.ADDI .x2 .x2 0x7f0,
   .JALR .x0 .x1 0,.ADDI .x11 .x10 0,.SLT .x10 .x10 .x0,.ADDI .x5 .x0 1,.ECALL]

private theorem index_ok (i : Fin 23) : pcIndex i.val < 1660 := by
  have := i.isLt
  unfold pcIndex
  split <;> omega

private theorem raw_word (i : Fin 23) :
    Artifact.openingCode.get 32 ⟨pcIndex i.val, index_ok i⟩ = words[i.val]?.getD 0 := by
  fin_cases i <;> rfl

private theorem op_decode (i : Fin 23) :
    decodeInstruction (words[i.val]?.getD 0) = some (.base (ops[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> rfl

private theorem fetch_return (i : Fin 23) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*pcIndex i.val)) :
    fetch code s = some (.base (ops[i.val]?.getD .EBREAK)) := by
  have bound := index_ok i
  have image : code.code = ArtifactEncoding.decode 32 Artifact.openingCode :=
    Eq.refl (ArtifactEncoding.decode 32 Artifact.openingCode)
  rw [@fetch_packed 1660 _ Artifact.openingCode image _ bound (by omega) s pc,
      raw_word, op_decode]

private def after (s : MachineState) (n : Nat) := (ops.take n).foldl execInstrBr s

private def lengthWord (w : BitVec 64) := ((w+63) >>> 3) &&& 0xfffffffffffffff8

private theorem length_nonnegative (w : BitVec 64) : (lengthWord w).slt 0 = false := by
  simp [lengthWord, BitVec.slt_zero_eq_msb]

private theorem length_bytes (w : BitVec 64) (small : w.toNat ≤ 70000000000) :
    (lengthWord w).toNat = alignedBytes w.toNat := by
  have bits : lengthWord w = (((w+63) >>> 6) <<< 3) := by
    unfold lengthWord
    rw [show (0xfffffffffffffff8 : BitVec 64) = BitVec.allOnes 64 <<< 3 by decide]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have sub : i - 3 < 64 := by omega
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
      BitVec.getLsbD_ushiftRight, hi, sub, decide_true, Bool.true_and, Bool.and_true]
    by_cases low : i < 3
    · simp [low]
    · simp [low, show 6 + (i - 3) = 3 + i by omega]
  rw [bits]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, alignedBytes]
  change (((w.toNat + 63) % 2^64 / 64 * 8) % 2^64) = _
  omega

private theorem return_locations (s : MachineState) (pc : s.pc=10660) (sp : s.getReg .x2=68719474016)
    (ret : s.getMem 68719476328=4176) (i : Fin 23) :
    (after s i.val).pc=BitVec.ofNat 64 (4096+4*pcIndex i.val) := by
  have stack : s.regs .x2 = 68719474016 := sp
  have saved : s.mem 68719476328 = 4176 := ret
  fin_cases i <;> simp [pcIndex, after, ops, execInstrBr, MachineState.setPC,
      MachineState.setReg, MachineState.getMem, MachineState.getReg, signExtend12, pc, stack] <;>
      rw [show s.mem 68719476328#64 = 4176#64 from saved] <;> decide

private theorem return_steps (s : MachineState) (pc : s.pc=10660) (sp : s.getReg .x2=68719474016)
    (ret : s.getMem 68719476328=4176) : ∀ i<22, ∃ instruction,
    fetch code (after s i)=some instruction ∧ ordinaryStep (after s i) instruction=some (after s (i+1)) ∧
    instructionCycles instruction=1 := by
  have loc := return_locations s pc sp ret
  have stack : s.regs .x2 = 68719474016 := sp
  intro i hi
  refine ⟨.base (ops[i]?.getD .EBREAK), fetch_return ⟨i,by omega⟩ _ (loc ⟨i,by omega⟩), ?_, ?_⟩
  · interval_cases i <;> simp [after, ops, ordinaryStep, memoryArgumentsValid, memAccess,
      accessValid, rangeValid, MEMORY_BYTES, execInstrBr, MachineState.setPC, MachineState.setReg,
      MachineState.getReg, signExtend12, stack]
  · interval_cases i <;> rfl

/-- From the final cursor through the return instruction and HALT. The frame address
and saved return PC are those established by the delivered entry code. -/
private theorem execute_return_state (s : MachineState) (pc : s.pc = 10660)
    (sp : s.getReg .x2 = 68719474016)
    (ret : s.getMem 68719476328 = 4176)
    (small : (s.getReg .x7).toNat ≤ 70000000000) (fuel : Nat) :
    execute (Artifact.submission.image .opening) (23+fuel) s true = pure ⟨.success, after s 22, 23, 0⟩ ∧
      ((after s 22).getReg .x11).toNat = alignedBytes (s.getReg .x7).toNat := by
  have loc := return_locations s pc sp ret
  have steps := execute_unit_steps code 22 (fuel+1) (after s) true (return_steps s pc sp ret)
  let final := after s 22
  have last := fetch_return 22 final (loc 22)
  change fetch code final = some (.base .ECALL) at last
  have mode : final.getReg .x5 = 1 := rfl
  have valid : final.getReg .x10 = 0 := by
    change (if (lengthWord (s.getReg .x7)).slt 0 then (1 : BitVec 64) else 0) = 0
    rw [length_nonnegative]; rfl
  have halt : execute code (fuel+1) final true = pure ⟨.success,final,1,0⟩ := by
    rw [execute, last]; simp [mode, valid]
  refine ⟨?_, ?_⟩
  · change execute code (23+fuel) (after s 0) true = _
    rw [show 23+fuel=22+(fuel+1) by omega,steps,halt]
    simp [Execution.charge, final]
  · have reported : final.getReg .x11 = lengthWord (s.getReg .x7) := by
      simp [final, after, ops, execInstrBr, MachineState.setPC, MachineState.setReg, MachineState.getReg,
        signExtend12, lengthWord]
    rw [reported]
    exact length_bytes _ small

/-- The same final state and data memory are returned for every remaining fuel.
No stack restoration instruction writes to RAM. -/
theorem execute_return_memory (s : MachineState) (pc : s.pc=10660)
    (sp : s.getReg .x2=68719474016) (ret : s.getMem 68719476328=4176)
    (small : (s.getReg .x7).toNat≤70000000000) :
    ∃ final : MachineState,
      (∀ fuel, execute (Artifact.submission.image .opening) (23+fuel) s true=pure ⟨.success,final,23,0⟩) ∧
      (final.getReg .x11).toNat=alignedBytes (s.getReg .x7).toNat ∧ final.mem=s.mem := by
  exact ⟨after s 22,fun fuel => (execute_return_state s pc sp ret small fuel).1,
    (execute_return_state s pc sp ret small 0).2,rfl⟩

/-- A partial execution of the epilogue can never revisit the cap entry. -/
theorem no_cap_prefix (s : MachineState) (pc : s.pc=10660) (sp : s.getReg .x2=68719474016)
    (ret : s.getMem 68719476328=4176) (small : (s.getReg .x7).toNat≤70000000000)
    (f : Nat) (r : Execution) (run : r∈support (execute (Artifact.submission.image .opening) f s true))
    (alive : r.exit=.unfinished) : r.state.pc≠9812 := by
  by_cases short : f<23
  · have h := execute_unit_steps code f 0 (after s) true
      (fun i hi => return_steps s pc sp ret i (by omega))
    change r∈support (execute code f (after s 0) true) at run
    rw [Nat.add_zero] at h
    rw [h] at run
    simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at run
    subst r
    have loc := return_locations s pc sp ret ⟨f,short⟩
    change (after s f).pc≠9812
    rw [loc]
    exact (by decide +kernel : ∀ i : Fin 23, (BitVec.ofNat 64 (4096+4*pcIndex i.val))≠9812) ⟨f,short⟩
  · have h := (execute_return_state s pc sp ret small (f-23)).1
    rw [show 23+(f-23)=f by omega] at h
    rw [h,support_pure,Set.mem_singleton_iff] at run
    subst r; cases alive

theorem execute_return_wide (s : MachineState) (pc : s.pc=10660)
    (sp : s.getReg .x2=68719474016) (ret : s.getMem 68719476328=4176)
    (small : (s.getReg .x7).toNat≤70000000000) (fuel : Nat) :
    ∃ final : MachineState,
      execute (Artifact.submission.image .opening) (23+fuel) s true=pure ⟨.success,final,23,0⟩ ∧
      (final.getReg .x11).toNat=alignedBytes (s.getReg .x7).toNat := by
  obtain ⟨t,run,size,_⟩ := execute_return_memory s pc sp ret small
  exact ⟨t,run fuel,size⟩

theorem execute_return (s : MachineState) (pc : s.pc = 10660)
    (sp : s.getReg .x2 = 68719474016)
    (ret : s.getMem 68719476328 = 4176)
    (small : (s.getReg .x7).toNat ≤ 600000) (fuel : Nat) :
    ∃ final : MachineState,
      execute (Artifact.submission.image .opening) (23+fuel) s true = pure ⟨.success, final, 23, 0⟩ ∧
      (final.getReg .x11).toNat = alignedBytes (s.getReg .x7).toNat :=
  execute_return_wide s pc sp ret (small.trans (by decide)) fuel

/-- The byte count returned for the contest's serialized positions when the
cursor equals the sum established by the heap scan. -/
theorem batch_return (s : MachineState) (positions : Positions) (batch : positions.card = BATCH)
    (cursor : (s.getReg .x7).toNat = Frontier.cursor (positions.sort (· ≤ ·)))
    (pc : s.pc = 10660) (sp : s.getReg .x2 = 68719474016)
    (ret : s.getMem 68719476328 = 4176) (fuel : Nat) :
    ∃ final : MachineState,
      execute (Artifact.submission.image .opening) (23+fuel) s true = pure ⟨.success, final, 23, 0⟩ ∧
      (final.getReg .x11).toNat ≤ 65544 := by
  have len : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
  have size := Frontier.cursor_bound (positions.sort (· ≤ ·)) (len.trans batch)
  have small : (s.getReg .x7).toNat ≤ 600000 := by
    rw [cursor]
    exact Nat.le_trans size.1 (by decide)
  obtain ⟨final, run, bytes⟩ := execute_return s pc sp ret small fuel
  exact ⟨final, run, by rw [bytes, cursor]; exact size.2⟩

end CommitGolfCandidate.Reconstruction.Return
