import CommitGolfCandidate.ReconstructedCheckTailOps

namespace CommitGolfCandidate.Reconstruction.CheckTailReturn
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding.Machine CheckRecorded CheckCapArith CommitBlocks CheckTailOps
open TwoPermutationPrototype.RV64
set_option maxRecDepth 40000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def Finished (o : Oracle) (s : MachineState) (n : Nat) (value : Word) := ∀ fuel,
  let obs := observation o (n+fuel) s
  obs.1.1.exit=CheckHalt.exit value ∧ obs.1.2=[] ∧ obs.2=0 ∧ obs.1.1.state.getReg .x11=value

theorem extend {o s t n m value} (seg : Segment o n s t []) (end_ : Finished o t m value) : Finished o s (n+m) value := by
  obtain ⟨cost,step⟩ := seg
  intro fuel
  simp only [Nat.add_assoc,step,List.nil_append,List.length_nil,Nat.zero_add,Execution.charge]
  exact end_ fuel

theorem finish57 (o : Oracle) (s : MachineState) (pc : s.pc=addr 57) (stack : s.getReg .x2=W CheckLayout.sp)
    (ret : s.getMem (W (CheckLayout.fp-8))=addr 20) : Finished o s 20 (s.getReg .x10) := by
  obtain ⟨t,seg,loc,rv,_⟩ := CheckEpilogue.positive o s CheckLayout.sp (by decide) (by decide) pc stack ret
  apply extend (m:=4) seg
  intro fuel
  simpa only [rv] using CheckHalt.terminal o t loc fuel

def acceptOps : List Line := [(.x10,.op (.lui 1)),(.x10,.op (.sub .x8 .x10))]
def rejectOps : List Line := [(.x10,.op (.addi .x0 4095))]
private theorem acceptListed : listed 668 acceptOps=true := by decide +kernel
private theorem rejectListed : listed 672 rejectOps=true := by decide +kernel
private theorem savedListed : CheckMemoryOps.word 670 (.base (.LD .x10 .x10 1672))=true := by decide +kernel
private theorem acceptJump : CheckStraight.actualAt 671=some (.base (.JAL .x0 2094696)) := CheckDecode.same_sound (by decide +kernel)
private theorem rejectJump : CheckStraight.actualAt 673=some (.base (.JAL .x0 2094688)) := CheckDecode.same_sound (by decide +kernel)

private theorem retPC (o : Oracle) (u : MachineState) (loc : u.pc=addr 673) (stack : u.getReg .x2=W CheckLayout.sp)
    (rv : u.getReg .x10=(-1)) (ret : u.getMem (W (CheckLayout.fp-8))=addr 20) : Finished o u 21 (-1) := by
  have jump := CheckBranch.jump o u 673 57 2094688 (by decide) loc rejectJump (by decide)
  have sp : (u.setPC (addr 57)).getReg .x2=W CheckLayout.sp := (MachineState.getReg_setPC ..).trans stack
  have finish := finish57 o (u.setPC (addr 57)) rfl sp ret
  rw [MachineState.getReg_setPC,rv] at finish
  exact extend jump finish

private theorem retMinus (s : MachineState) : (effect s rejectOps).getReg .x10=(-1) := by
  rw [register];change 0#64+signExtend12 4095=(-1);decide

theorem reject672 (o : Oracle) (s : MachineState) (pc : s.pc=addr 672) (stack : s.getReg .x2=W CheckLayout.sp)
    (ret : s.getMem (W (CheckLayout.fp-8))=addr 20) : Finished o s 22 (-1) := by
  have step := CheckCapArith.positive o s 672 rejectOps pc rejectListed
  have final_ := retPC o (effect s rejectOps) (location s 672 rejectOps pc)
    ((outside s rejectOps .x2 (by decide)).trans stack) (retMinus s) ((congrFun (memory s rejectOps) _).trans ret)
  exact extend step final_

theorem accept668 (o : Oracle) (s : MachineState) (len : Nat) (pc : s.pc=addr 668)
    (stack : s.getReg .x2=W CheckLayout.sp) (fp : s.getReg .x8=W CheckLayout.fp)
    (ret : s.getMem (W (CheckLayout.fp-8))=addr 20) (saved : s.getMem (W (CheckLayout.fp-2424))=W len) :
    Finished o s 24 (W len) := by
  let u := effect s acceptOps
  have step := CheckCapArith.positive o s 668 acceptOps pc acceptListed
  have ptr : u.getReg .x10+signExtend12 1672=wordAddress 8589934163 := by
    rw [register];change (s.getReg .x8-W 4096)+signExtend12 1672=_;rw [fp];decide
  let v := (u.setReg .x10 (W len)).setPC (addr 671)
  have ld := CheckTailOps.load o u 670 .x10 .x10 1672 8589934163 (by decide) (W len)
    (location s 668 acceptOps pc) savedListed ptr ((congrFun (memory s acceptOps) _).trans saved)
  have jump := CheckBranch.jump o v 671 57 2094696 (by decide) rfl acceptJump (by decide)
  let t:=v.setPC (addr 57)
  have sp : t.getReg .x2=W CheckLayout.sp := by
    change ((u.setReg .x10 (W len)).setPC (addr 671) |>.setPC (addr 57)).getReg .x2=_
    simp only [MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg]
    exact (outside s acceptOps _ (by decide)).trans stack
  have retT : t.getMem (W (CheckLayout.fp-8))=addr 20 := (congrFun (memory s acceptOps) _).trans ret
  have end_ := finish57 o t rfl sp retT
  have rv : t.getReg .x10=W len := by
    change (((u.setReg .x10 (W len)).setPC (addr 671)).setPC (addr 57)).getReg .x10=_
    rw [MachineState.getReg_setPC,MachineState.getReg_setPC,MachineState.getReg_setReg_eq]
    decide
  rw [rv] at end_
  exact extend (compose (compose step ld) jump) end_

end CommitGolfCandidate.Reconstruction.CheckTailReturn
