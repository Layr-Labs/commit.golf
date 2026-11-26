import CommitGolfCandidate.R1bCheckMask
import CommitGolfCandidate.TwoPermutationHybridPaths
import CommitGolfCandidate.TwoPermutationPackedImage
import CommitGolfCandidate.ProjectedMask

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec ShortTree
set_option maxRecDepth 8192
set_option maxHeartbeats 850000
attribute [local irreducible] execute readBuffer writeBits capCompressionAnswer

theorem parent_hash_step (site : ProjectSite) (cap : site = .cap) (s : MachineState) (source target : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*site.start))
    (src : s.getReg .x10=BitVec.ofNat 64 source) (dst : s.getReg .x12=BitVec.ofNat 64 target)
    (mask : s.getReg site.dest=s.getReg .x12)
    (selector : s.getReg .x5=0 ∧ s.getReg .x11=64 ∧ s.getReg .x13=0)
    (srcRoom : source+64≤MEMORY_BYTES) (dstRoom : target+32≤MEMORY_BYTES)
    (srcAlign : source%8=0) (dstAlign : target%8=0) (fuel : Nat) :
    execute packedImage (7+fuel) s false = do
      let answer ← World.query (.inr (.inl (readBuffer s (source+32) 32 ++ readBuffer s source 32)))
      let result ← execute packedImage fuel (((capCompressionAnswer s (Hybrid.pad238 answer)).setReg .x1 (TwoPermutationPrototype.RV64.maskValue answer)).setPC (s.pc+8)) false
      return result.charge 14 1 := by
  subst site
  have lim : MEMORY_BYTES<2^64 := by decide
  have srcV : rangeValid (s.getReg .x10) 64=true := by
    simp only [src,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),decide_eq_true_eq];exact srcRoom
  have dstV : rangeValid (s.getReg .x12) 32=true := by
    simp only [dst,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target<2^64),decide_eq_true_eq];exact dstRoom
  have asrc : (s.getReg .x10).toNat%8=0 := by simpa [src,Nat.mod_eq_of_lt (by omega : source<2^64)] using srcAlign
  have adst : (s.getReg .x12).toNat%8=0 := by simpa [dst,Nat.mod_eq_of_lt (by omega : target<2^64)] using dstAlign
  have hash := cap_compression_execute packedImage s (project_fetch .cap _ pc) selector srcV dstV asrc adst (fuel+6) false
  change execute packedImage (1+(fuel+6)) s false = (do
    let answer ← World.query (.inr (.inl (readBuffer s (s.getReg .x10).toNat 64)))
    let result ← execute packedImage (fuel+6) (capCompressionAnswer s answer) false
    return result.charge 8 1) at hash
  rw [src,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),read_compression_halves s source srcAlign] at hash
  rw [show 7+fuel=1+(fuel+6) by omega,hash]
  congr 1
  funext answer
  change BitVec 256 at answer
  let raw := capCompressionAnswer s answer
  have after : raw.pc=5456 := by
    have moved : raw.pc=s.pc+4 := by unfold raw capCompressionAnswer;exact RV64.written_pc s _ answer
    rw [moved,pc] <;> rfl
  let st := raw.setPC (R1bPC.pcAt 10537)
  have jump : ordinaryStep raw (.base (.JAL .x0 40788))=some st := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,after,MachineState.setReg,st,R1bPC.pcAt] <;> rfl
  have enter := execute_ordinary_step packedImage _ raw st (fuel+5) false (project_fetch_mask raw after) jump
  have ptr : st.getReg .x12=BitVec.ofNat 64 target := (cap_compression_register ..).trans dst
  have run := R1b.Machine.runMask true st target rfl ptr dstAlign dstRoom (fuel+1) false
  change execute (Artifact.submission.image .check) ((fuel+1)+4) st false = _ at run
  simp only [R1b.Machine.Code.image,delivered_check_image] at run
  have exit := R1b.Machine.maskOutput true s target answer dst dst dstAlign (by omega)
  let doneState := ((capCompressionAnswer s (Hybrid.pad238 answer)).setReg .x1 (RV64.maskValue answer)).setPC (R1bPC.pcAt 10541)
  have endEq : R1b.Machine.maskState true st 4=doneState := exit
  rw [endEq] at run
  let resume := ((capCompressionAnswer s (Hybrid.pad238 answer)).setReg .x1 (RV64.maskValue answer)).setPC (s.pc+8)
  have backCode : fetch packedImage doneState=some (.base (.JAL .x0 (BitVec.ofInt 21 (-40800)))) := by
    rw [←delivered_check_image]
    exact (R1b.Machine.fetched .check 10541 (by decide) doneState rfl).trans (by apply R1b.Machine.stood;decide)
  have back : ordinaryStep doneState (.base (.JAL .x0 (BitVec.ofInt 21 (-40800))))=some resume := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,doneState,resume,
      MachineState.setPC,R1bPC.pcAt,pc] <;> rfl
  rw [show fuel+6=(fuel+5)+1 by omega,enter,show fuel+5=(fuel+1)+4 by omega,run,
    execute_ordinary_step packedImage _ doneState resume fuel false backCode back]
  simp [Execution.charge,instructionCycles,bind_assoc,←Nat.add_assoc,resume]

end TwoPermutationPrototype.Packed.Checker
