import CommitGolfCandidate.Stage3cCheckParent
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def maskStart (wide : Bool) : PathCode :=
  [(211,.ADDI .x6 .x0 256),(212,.BEQ .x31 .x6 48)]++
  if wide then [] else [(213,.ADDI .x6 .x0 240),(214,.BNE .x31 .x6 12)]

private theorem mask_prep (s : MachineState) (pc : s.pc=pcAt 211) (wide : Bool) (width : s.getReg .x31=(if wide then 256 else 240)) :
    pathReady s (maskStart wide) ∧
      let t:=pathEnd s (maskStart wide)
      t.pc=pcAt (if wide then 224 else 215) ∧ t.mem=s.mem ∧ t.getReg .x12=s.getReg .x12 := by
  change s.regs .x31=_ at width
  cases wide <;> simp +decide [maskStart,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
    MachineState.getReg,MachineState.setReg,MachineState.setPC,pcAt,pc,width,signExtend12,signExtend13] at * <;> simp_all +decide

def projected (s : MachineState) (wide : Bool) :=
  let t:=pathEnd s (maskStart wide)
  if wide then t else execInstrBr (execInstrBr t (.SH .x12 .x0 30)) (.JAL .x0 32)

theorem mask_full (s : MachineState) (pc : s.pc=pcAt 211) (w : s.getReg .x31=256) :
    let t:=projected s true
    (∀ fuel, execute (image .check) (fuel+2) s false=(do let r←execute (image .check) fuel t false;return r.charge 2 0)) ∧
    t.pc=pcAt 224 ∧ t.mem=s.mem := by
  obtain ⟨ok,last,eq,_⟩:=mask_prep s pc true w
  exact ⟨path_run _ false _ _ (by decide +kernel) ok,last,eq⟩

theorem mask_halfword (s : MachineState) (pc : s.pc=pcAt 211) (w : s.getReg .x31=240) (a : Nat)
    (dst : s.getReg .x12=BitVec.ofNat 64 a) (bound : a+32≤MEMORY_BYTES) (align : a%8=0) :
    let t:=projected s false
    (∀ fuel, execute (image .check) (fuel+6) s false=(do let r←execute (image .check) fuel t false;return r.charge 6 0)) ∧
    t.pc=pcAt 224 ∧ t.mem=(s.setHalfword (BitVec.ofNat 64 (a+30)) 0).mem := by
  let z:=pathEnd s (maskStart false)
  obtain ⟨pre,ip,mem,ptr⟩:=mask_prep s pc false w
  have address : z.getReg .x12+signExtend12 30=BitVec.ofNat 64 (a+30) :=
    (congrArg (·+signExtend12 30) (ptr.trans dst)).trans (BitVec.ofNat_add a 30).symm
  have ok : memoryArgumentsValid z (.SH .x12 .x0 30)=true := by
    change accessValid (_+_) 2=true;rw [address]
    apply access_ok <;> change a+32≤2^36 at bound <;> first | omega | (change _≤2^36;omega)
  let u:=execInstrBr z (.SH .x12 .x0 30)
  have up : u.pc=pcAt 216 := by change z.pc+4=_;rw [show z.pc=pcAt 215 from ip];rfl
  have j:=site (p:=.check) (n:=216) (op:=.JAL .x0 32) (by decide) (by rfl) u up
  have sh:=site (p:=.check) (n:=215) (op:=.SH .x12 .x0 30) (by decide) (by rfl) z ip
  refine ⟨?_,?_,?_⟩
  · intro fuel
    have head:=path_run .check false s (maskStart false) (by decide +kernel) pre (fuel+2)
    rw [show fuel+6=(fuel+2)+(maskStart false).length by rfl,head]
    change (do let r←execute (image .check) ((fuel+1)+1) z false;return r.charge 4 0)=_
    rw [execute_ordinary_step _ _ _ u _ _ sh (by simp only [ordinaryStep,ok,↓reduceIte];rfl),
      execute_ordinary_step _ _ _ (projected s false) _ _ j rfl]
    simp only [bind_assoc,pure_bind]
    apply bind_congr;intro out;congr 1 <;> simp [Execution.charge,instructionCycles] <;> omega
  · change u.pc+signExtend21 32=_;rw [up];rfl
  · change (z.setHalfword (z.getReg .x12+signExtend12 30) 0).mem=_
    rw [address];simp only [MachineState.setHalfword,MachineState.setMem,MachineState.getMem,show z.mem=s.mem from mem]

/-- Test the two full-byte width cases. The narrower branch jumps to word 217. -/
def narrowStart : PathCode := [(211,.ADDI .x6 .x0 256),(212,.BEQ .x31 .x6 48),(213,.ADDI .x6 .x0 240),(214,.BNE .x31 .x6 12)]
def maskArithmetic : PathCode := [(217,.ADDI .x6 .x31 3872),(218,.ADDI .x7 .x0 1),(219,.SLL .x7 .x7 .x6),(220,.ADDI .x7 .x7 4095),
  (221,.LHU .x28 .x12 28),(222,.AND .x28 .x28 .x7),(223,.SW .x12 .x28 28)]
theorem narrow_sites : narrowStart.all (matchesWord .check) ∧ maskArithmetic.all (matchesWord .check) := by decide +kernel

theorem narrow_guard (s : MachineState) (pc : s.pc=pcAt 211) (w : Nat) (few : w≤238)
    (width : s.getReg .x31=BitVec.ofNat 64 w) :
    pathReady s narrowStart ∧ (pathEnd s narrowStart).pc=pcAt 217 ∧ (pathEnd s narrowStart).mem=s.mem ∧
    (pathEnd s narrowStart).getReg .x12=s.getReg .x12 ∧ (pathEnd s narrowStart).getReg .x31=s.getReg .x31 := by
  have ne (n : Nat) (h : w<n) (small : n<2^64) : s.regs .x31≠BitVec.ofNat 64 n := by
    intro eq;change s.getReg .x31=_ at eq;rw [width] at eq
    have num:=congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt (h.trans small)] at num;omega
  have wide:=ne 256 (by omega) (by decide)
  have half:=ne 240 (by omega) (by decide)
  simp +decide [narrowStart,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
    MachineState.getReg,MachineState.setReg,MachineState.setPC,pc,pcAt,signExtend12,signExtend13,wide,half] <;> simp_all +decide

end CommitGolfCandidate.Chained.BinaryMachine.Check
