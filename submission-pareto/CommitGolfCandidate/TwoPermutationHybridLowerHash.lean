import CommitGolfCandidate.TwoPermutationPackedParent
import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationHybridPaths

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec ShortTree

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem one (s t : MachineState) (i : Instr)
    (found : fetch packedImage s = some (.base i)) (step : ordinaryStep s (.base i) = some t)
    (unit : instructionCycles (.base i) = 1) : GroupHop s t 1 := by
  intro fuel
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ found step,unit]

private theorem entry (s : MachineState) (pc : s.pc=5036) :
    GroupHop s ((s.setReg .x7 131072).setPC 5568) 2 := by
  have jump : GroupHop s (s.setPC 5564) 1 := by
    apply one s _ (.JAL .x0 528) (fetch_at s 235 _ (by decide) pc rfl) _ rfl
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend21,pc,MachineState.setReg]
  have load : GroupHop (s.setPC 5564) ((s.setReg .x7 131072).setPC 5568) 1 := by
    apply one _ _ (.LUI .x7 32) (fetch_at _ 367 _ (by decide) rfl rfl) _ rfl
    rfl
  exact jump.thenDo load

private theorem test (s : MachineState) (pc : s.pc = 5568) :
    GroupHop s (s.setPC (if s.getReg .x7 ≤ s.getReg .x6 then 5580 else 5572)) 1 := by
  apply one s _ (.BGEU .x6 .x7 12) (fetch_at s 368 _ (by decide) pc rfl) _ rfl
  by_cases b : s.getReg .x7 ≤ s.getReg .x6
  · have cmp : (s.getReg .x6).ult (s.getReg .x7) = false := decide_eq_false (not_lt_of_ge b)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,pc,b,cmp]
  · have cmp : (s.getReg .x6).ult (s.getReg .x7) = true := decide_eq_true (lt_of_not_ge b)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,pc,b,cmp]

private theorem full_return (s : MachineState) (pc : s.pc = 5580) : GroupHop s (s.setPC 5040) 2 := by
  have nop : GroupHop s (s.setPC 5584) 1 := by
    apply one s _ (.ADDI .x0 .x0 0) (fetch_at s 371 _ (by decide) pc rfl) _ rfl
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,pc]
  have jump : GroupHop (s.setPC 5584) (s.setPC 5040) 1 := by
    apply one _ _ (.JAL .x0 2096608) (fetch_at _ 372 _ (by decide) rfl rfl) _ rfl
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend21,MachineState.setReg,MachineState.setPC]
  exact nop.thenDo jump

private theorem masked_return (s : MachineState) (pc : s.pc = 5576) : GroupHop s (s.setPC 5040) 1 := by
  apply one _ _ (.JAL .x0 2096616) (fetch_at s 370 _ (by decide) pc rfl) _ rfl
  simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend21,pc,MachineState.setReg]

private theorem moved_mask (raw dst : MachineState)
    (valid : accessValid (raw.getReg .x23 + signExtend12 30) 2=true)
    (store : execInstrBr raw (.SH .x23 .x0 30)=dst) :
    GroupHop (((raw.setReg .x7 131072).setPC 5568).setPC 5572) ((dst.setReg .x7 131072).setPC 5576) 1 := by
  let s := ((raw.setReg .x7 131072).setPC 5568).setPC 5572
  have decoded : (packedImage.code[369]?).bind decodeInstruction=some (.base (.SH .x23 .x0 30)) := by rfl
  have f := fetch_at s 369 _ (by decide) (show s.pc=5572#64 from rfl) decoded
  apply one s _ _ f _ rfl
  have access : accessValid (s.getReg .x23 + signExtend12 30) 2=true := valid
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,access,↓reduceIte]
  have move : execInstrBr s (.SH .x23 .x0 30)=((execInstrBr raw (.SH .x23 .x0 30)).setReg .x7 131072).setPC 5576 := by rfl
  exact congrArg some (move.trans (congrArg (fun st : MachineState => (st.setReg .x7 131072).setPC 5576) store))

theorem hybrid_lower_hash (s : MachineState) (source target node : Nat)
    (pc : s.pc = 5032) (nodeReg : s.getReg .x6=BitVec.ofNat 64 node)
    (len : s.getReg .x20=16777216) (nodeBound : node<2^64)
    (src : s.getReg .x10=BitVec.ofNat 64 source) (dst : s.getReg .x12=BitVec.ofNat 64 target)
    (mask : s.getReg .x23=s.getReg .x12)
    (selector : s.getReg .x5=0 ∧ s.getReg .x11=64 ∧ s.getReg .x13=0)
    (srcRoom : source+64≤MEMORY_BYTES) (dstRoom : target+32≤MEMORY_BYTES)
    (srcAlign : source%8=0) (dstAlign : target%8=0) (fuel : Nat) :
    execute packedImage (6+fuel) s false = do
      let answer ← World.query (.inr (.inl (readBuffer s (source+32) 32 ++ readBuffer s source 32)))
      let result ← execute packedImage fuel
        (((capCompressionAnswer s (Hybrid.normalize (node/2) answer)).setReg .x7 131072).setPC (s.pc+8)) false
      return result.charge 13 1 := by
  have lim : MEMORY_BYTES<2^64 := by decide
  have srcV : rangeValid (s.getReg .x10) 64=true := by
    simp only [src,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),decide_eq_true_eq];exact srcRoom
  have dstV : rangeValid (s.getReg .x12) 32=true := by
    simp only [dst,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target<2^64),decide_eq_true_eq];exact dstRoom
  have asrc : (s.getReg .x10).toNat%8=0 := by simpa [src,Nat.mod_eq_of_lt (by omega : source<2^64)] using srcAlign
  have adst : (s.getReg .x12).toNat%8=0 := by simpa [dst,Nat.mod_eq_of_lt (by omega : target<2^64)] using dstAlign
  have hash := cap_compression_execute packedImage s (project_fetch .lower _ pc) selector srcV dstV asrc adst (fuel+5) false
  change execute packedImage (1+(fuel+5)) s false = (do
    let answer ← World.query (.inr (.inl (readBuffer s (s.getReg .x10).toNat 64)))
    let result ← execute packedImage (fuel+5) (capCompressionAnswer s answer) false
    return result.charge 8 1) at hash
  rw [src,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),read_compression_halves s source srcAlign] at hash
  rw [show 6+fuel=1+(fuel+5) by omega,hash]
  congr 1
  funext answer
  change BitVec 256 at answer
  let raw := capCompressionAnswer s answer
  have after : raw.pc=BitVec.ofNat 64 (4096+4*(ProjectSite.lower.start+1)) := by
    have moved : raw.pc=s.pc+4 := by unfold raw capCompressionAnswer writeBits;rfl
    rw [moved,pc];rfl
  have reg : raw.getReg .x23=raw.getReg .x12 := by
    dsimp only [raw]
    rw [cap_compression_register,cap_compression_register,mask]
  have am : accessValid (raw.getReg .x23 + signExtend12 30) 2=true := by
    rw [reg,show raw.getReg .x12=s.getReg .x12 from cap_compression_register _ _ _,dst]
    change accessValid (BitVec.ofNat 64 target + BitVec.ofNat 64 30) 2=true
    rw [←BitVec.ofNat_add]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target+30<2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨by omega,by omega⟩
  have masked := masked_reply_step s target answer dst dstAlign (by omega)
  have same : execInstrBr raw (.SH .x23 .x0 30)=execInstrBr raw (.SH .x12 .x0 30) := by
    simp only [execInstrBr,reg]
  have shifted := entry raw after
  have branch := test ((raw.setReg .x7 131072).setPC 5568) rfl
  have nodeReg' : raw.getReg .x6=BitVec.ofNat 64 node := (cap_compression_register ..).trans nodeReg
  have enough : ((131072 : BitVec 64) ≤ raw.getReg .x6) ↔ 131072≤node := by
    rw [nodeReg']
    change 131072 ≤ (BitVec.ofNat 64 node).toNat ↔ _
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nodeBound]
  have readFlag : ((raw.setReg .x7 131072).setPC 5568).getReg .x7=131072 := by rfl
  have readNode : ((raw.setReg .x7 131072).setPC 5568).getReg .x6=raw.getReg .x6 := by rfl
  rw [readFlag,readNode] at branch
  by_cases full : 131072≤node
  · have h := enough.mpr full
    have side : ¬node/2<LENGTH/256 := by change ¬node/2<65536; omega
    rw [ite_eq_left h] at branch
    have run := (shifted.thenDo branch).thenDo (full_return _ rfl)
    have last := run fuel
    rw [show fuel+5=2+1+2+fuel by omega,last]
    simp [Hybrid.normalize,side,pc,Execution.charge,←Nat.add_assoc,MachineState.setPC,raw]
  · have h : ¬ (131072 : BitVec 64) ≤ raw.getReg .x6 := fun le => full (enough.mp le)
    have side : node/2<LENGTH/256 := by change node/2<65536; omega
    rw [ite_eq_right h] at branch
    let atMask := ((raw.setReg .x7 131072).setPC 5568).setPC 5572
    let maskedState := (((capCompressionAnswer s (padLow answer)).setPC (s.pc+8)).setReg .x7 131072).setPC 5576
    have maskHop : GroupHop atMask maskedState 1 :=
      moved_mask raw _ am (same.trans masked)
    have finish : GroupHop maskedState (maskedState.setPC 5040) 1 := masked_return maskedState rfl
    have run : GroupHop raw (maskedState.setPC 5040) 5 :=
      ((shifted.thenDo branch).thenDo maskHop).thenDo finish
    have last := run fuel
    rw [show fuel+5=2+1+1+1+fuel by omega,last]
    simp [Hybrid.normalize,side,pc,Execution.charge,←Nat.add_assoc,maskedState,MachineState.setPC,MachineState.setReg]

end TwoPermutationPrototype.Packed.Checker
