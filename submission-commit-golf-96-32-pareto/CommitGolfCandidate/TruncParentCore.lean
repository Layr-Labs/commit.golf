import CommitGolfCandidate.TruncParentCode
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
theorem rawLane (state : MachineState) (bank : Bank) (j : Nat)
    (hj : inBank bank j)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (startWord bank j)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (valid : ParentCallValid state (31 - j)) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let answer ← World.query (.inr (parentQuery state (31 - j)))
          let result ← execute (submission.image .commit) fuel (parentCallState state (31 - j) answer) true
          return result.charge 10 1) := by
  let baseIdx := startWord bank j
  let u := 31 - j
  have hu : u < 32 := by have := bankBound bank hj;omega
  have hbound : baseIdx + 2 < 2048 := by
    have := bankBound bank hj;cases bank <;> simp [baseIdx,startWord] <;> omega
  let mid := (state.setReg .x10 (parentSource state u)).setPC (state.pc + 4)
  let ready := parentSetupState state u
  have midPC : mid.pc = BitVec.ofNat 64 (4096 + 4 * (baseIdx + 1)) := by
    change state.pc + 4 = _
    rw [pc]
    apply ofNat64_add_eq _ 4 _; omega
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (baseIdx + 2)) := by
    change state.pc + 8 = _
    rw [pc]
    apply ofNat64_add_eq _ 8 _; omega
  have f0 : fetch (submission.image .commit) state = some (.base (parentLaneInstr u 0)) :=
    fetchAt _ state (baseIdx + 0) _ (by omega) pc
      (laneDecode bank j 0 hj (by decide))
  have f1 : fetch (submission.image .commit) mid = some (.base (parentLaneInstr u 1)) :=
    fetchAt _ mid (baseIdx + 1) _ (by omega) midPC
      (laneDecode bank j 1 hj (by decide))
  have f2 : fetch (submission.image .commit) ready = some (.base .ECALL) :=
    fetchAt _ ready (baseIdx + 2) .ECALL (by omega) readyPC
      (laneDecode bank j 2 hj (by decide))
  have s0 : ordinaryStep state (.base (parentLaneInstr u 0)) = some mid := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, parentLaneInstr,
      parentSource, mid]
  have s1 : ordinaryStep mid (.base (parentLaneInstr u 1)) = some ready := by
    have sheap := signExtend12_heapOffset ⟨u, hu⟩
    have h44 : (4 : Word) + 4 = 8 := by decide
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, parentLaneInstr,
      parentOutput, mid, ready, parentSetupState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, BitVec.add_assoc, sheap, h44]
  have rr5 : ready.getReg .x5 = 0 := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r5]
  have rr11 : ready.getReg .x11 = 96 := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r11]
  have rr13 : ready.getReg .x13 = 0 := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r13]
  have rr10 : ready.getReg .x10 = parentSource state u := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  have rr12 : ready.getReg .x12 = parentOutput state u := by
    simp [ready, parentSetupState, MachineState.getReg_setPC, MachineState.getReg_setReg_eq]
  have sameMem : ready.mem = state.mem := rfl
  have rmem : readBuffer ready (parentSource state u).toNat 96 =
      readBuffer state (parentSource state u).toNat 96 := by
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, sameMem]
  have hinput : oracleInput ready = some (.inl (readBuffer state (parentSource state u).toNat 96)) := by
    have h := oracleInput_compression ready rr11 rr13
      (by rw [rr10]; exact valid.1) (by rw [rr10]; exact valid.2.1)
      (by rw [rr12]; exact valid.2.2.1) (by rw [rr12]; exact valid.2.2.2)
    rwa [rr10, rmem] at h
  rw [show 3 + fuel = ((fuel + 1) + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ f0 s0,
    execute_ordinary_step _ _ _ _ _ _ f1 s1,
    execute, f2, if_pos rr5, hinput]
  simp only [writeOracleAnswer, rr12, bind_assoc, pure_bind]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (parentQuery state u))) : OracleComp World (BitVec 256)) >>= k)
  funext answer
  change BitVec 256 at answer
  simp [oracleCycles, COMPRESSION_CYCLES, instructionCycles, charge_charge]
  rfl


end CommitGolfCandidate.Trunc
