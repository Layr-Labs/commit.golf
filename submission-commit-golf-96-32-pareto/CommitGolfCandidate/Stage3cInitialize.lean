import CommitGolfCandidate.Stage3cRngDraws
import CommitGolfCandidate.Stage3cCode
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option Elab.async false

def initializeOps : List Instr :=
  [.ADDI .x8 .x10 0,.ADDI .x9 .x11 0,.ADDI .x18 .x12 0,
   .LUI .x6 393216,.ADD .x19 .x18 .x6,.LUI .x6 192,.SLLI .x6 .x6 12,
   .ADD .x24 .x18 .x6,.ADDI .x5 .x0 2,.ADDI .x10 .x19 72,.ADDI .x11 .x0 40,.LUI .x20 1]

def start (m : Message) := Artifact.submission.initialState .commit m
def prepared (m : Message) := initializeOps.foldl execInstrBr (start m)

private theorem init_decode : ∀ j : Fin 12,
    decodeInstruction (atWord .commit ⟨j.val,by change j.val<11543;omega⟩)=
      some (.base (initializeOps.get ⟨j.val,j.isLt⟩)) := by decide +kernel

theorem init_sites (i : Nat) (bound : i < initializeOps.length) : Site .commit i initializeOps[i] := by
  change i<12 at bound
  apply site (by change i<11543;omega)
  exact init_decode ⟨i,bound⟩

theorem init_run (m : Message) (fuel : Nat) :
    execute commitImage (fuel+12) (start m) true=
      (do let r←execute commitImage fuel (prepared m) true; return r.charge 12 0) := by
  apply execute_linear .commit true initializeOps 0 _ _ rfl
  · intro op member
    simp only [initializeOps,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> intro s <;> exact ⟨rfl,rfl,rfl⟩
  · intro i hi;simpa only [Nat.zero_add] using init_sites i hi

private theorem ready_generic (s : MachineState) (pc : s.pc=4096) (td : s.getReg .x12=4294975488) :
    AtPair (initializeOps.foldl execInstrBr s) 0 := by
  have raw : s.regs .x12=4294975488 := td
  constructor <;> simp [initializeOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,
    signExtend12,pc,raw,pcAt,pairCount,destination,pairAddress,rowBase] <;> rfl

theorem ready (m : Message) : AtPair (prepared m) 0 := ready_generic (start m) rfl rfl

def draws := (List.range pairCount).mapM fun _=>draw40
def sampled (m : Message) (ws : List Draw40) := applyPairs 0 (prepared m) ws

theorem commit_sampling (m : Message) (fuel : Nat) :
    execute commitImage (fuel+16789515) (start m) true =
      (do let ws←draws;let r←execute commitImage fuel (sampled m ws) true;return r.charge 58732555 0) := by
  have run:=execute_pairs (List.range pairCount) 0 (prepared m) (ready m)
    (by simp only [List.length_range,Nat.zero_add];rfl) fuel
  simp only [List.length_range] at run
  rw [show samplingSteps 0 pairCount=16789503 by decide,show samplingCycles 0 pairCount=58732543 by decide] at run
  rw [show fuel+16789515=(fuel+16789503)+12 by omega,init_run,run]
  simp [draws,sampled,bind_assoc,Execution.charge,←Nat.add_assoc]

end CommitGolfCandidate.Chained.BinaryMachine
