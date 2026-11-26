import CommitGolfCandidate.R1bCodecRun
import CommitGolfCandidate.R1bCodecSites

namespace CommitGolfCandidate.R1b.Codec
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open R1bPC (pcAt)

private theorem takenJump (c : Code) (s : MachineState) (atPC toPC : Nat) (imm : BitVec 21)
    (limit : atPC<c.count) (here : s.pc=pcAt atPC)
    (code : stands c atPC (.JAL .x0 imm)) (dest : pcAt atPC+signExtend21 imm=pcAt toPC) :
    Runs c s (s.setPC (pcAt toPC)) 1 1 := by
  apply one limit here _ (stood code)
  simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,here,dest]

/-- The entry and return edges are kernel-checked against the two delivered images. -/
theorem checkEnter (s : MachineState) (pc : s.pc=pcAt 0) :
    Runs .check s (s.setPC (pcAt 372)) 1 1 :=
  takenJump _ _ _ _ 1488 (by decide) pc (by decide) (by decide)

theorem openEnter (s : MachineState) (pc : s.pc=pcAt 664) :
    Runs .opening s (s.setPC (pcAt 1435)) 1 1 :=
  takenJump _ _ _ _ 3084 (by decide) pc (by decide) (by decide)

theorem returnWideCheck (s : MachineState) (pc : s.pc=pcAt 10526) :
    Runs .check s (s.setPC (pcAt 1)) 1 1 :=
  takenJump _ _ _ _ (BitVec.ofInt 21 (-42100)) (by decide) pc (by decide) (by decide)

theorem rejectTag (s : MachineState) (pc : s.pc=pcAt 10527) :
    Runs .check s (s.setPC (pcAt 364)) 1 1 :=
  takenJump _ _ _ _ (BitVec.ofInt 21 (-40652)) (by decide) pc (by decide) (by decide)

theorem returnOpen (s : MachineState) (pc : s.pc=pcAt 12625) :
    Runs .opening s (s.setPC (pcAt 665)) 1 1 :=
  takenJump _ _ _ _ (BitVec.ofInt 21 (-47840)) (by decide) pc (by decide) (by decide)

theorem realCodec (d : Bool) (s : MachineState) (pc : s.pc=pcAt (entry d)) (ptr : Input d s) :
    ∃ t,Common d s t 352 1396 ∧ t.pc=pcAt (donePC d) ∧
      Runs (program d) s t (bodySteps d) (bodySteps d) :=
  run byteSites d s pc ptr

end CommitGolfCandidate.R1b.Codec
