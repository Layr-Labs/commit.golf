import CommitGolfCandidate.Stage3cCheckMaskSetup
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
theorem write_mask_tail (s : MachineState) (a : Nat) (m : Word) (pc : s.pc=pcAt 221)
    (dst : s.getReg .x12=BitVec.ofNat 64 a) (mask : s.getReg .x7=m) (bound : a+32≤MEMORY_BYTES) (al : a%8=0) :
    pathReady s maskWrite ∧ (writtenMask s).pc=pcAt 224 ∧ (writtenMask s).mem=(maskedWord s a m).mem := by
  let p:=s.getReg .x12+signExtend12 28
  have loc : p=BitVec.ofNat 64 (a+28) := (congrArg (·+signExtend12 28) dst).trans (BitVec.ofNat_add a 28).symm
  have h : accessValid p 2=true := by rw [loc];apply access_ok <;> change a+32≤2^36 at bound <;> first | omega | (change _≤2^36;omega)
  have h' : accessValid p 4=true := by rw [loc];apply access_ok <;> change a+32≤2^36 at bound <;> first | omega | (change _≤2^36;omega)
  let z:=execInstrBr s (.LHU .x28 .x12 28)
  let u:=execInstrBr z (.AND .x28 .x28 .x7)
  have pz : z.pc=pcAt 222 := by change s.pc+4=_;rw [pc,pc_succ]
  have pu : u.pc=pcAt 223 := by change z.pc+4=_;rw [pz,pc_succ]
  have first : ordinaryStep s (.base (.LHU .x28 .x12 28))=some z := by
    change (if accessValid p 2 then some z else none)=_;rw [h];rfl
  have last : ordinaryStep u (.base (.SW .x12 .x28 28))=some (execInstrBr u (.SW .x12 .x28 28)) := by
    change (if accessValid p 4 then some (execInstrBr u (.SW .x12 .x28 28)) else none)=_;rw [h'];rfl
  refine ⟨⟨pc,first,rfl,pz,rfl,rfl,pu,last,rfl,True.intro⟩,?_,?_⟩
  · change u.pc+4=_;rw [pu,pc_succ]
  · change (s.setWord32 p (((s.getHalfword p).zeroExtend 64 &&& s.getReg .x7).truncate 32)).mem=_
    rw [loc,mask];rfl

end CommitGolfCandidate.Chained.BinaryMachine.Check
