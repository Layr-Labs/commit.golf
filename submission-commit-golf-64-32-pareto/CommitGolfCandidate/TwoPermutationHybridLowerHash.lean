import CommitGolfCandidate.R1bCheckMask
import CommitGolfCandidate.TwoPermutationPackedParent
import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationHybridPaths

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec ShortTree

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
attribute [local irreducible] execute writeBits capCompressionAnswer

private theorem resetPC (z : MachineState) (a b : Word) : (z.setPC a).setPC b=z.setPC b := rfl

private theorem one (s t : MachineState) (i : Instr)
    (found : fetch packedImage s = some (.base i)) (step : ordinaryStep s (.base i) = some t)
    (unit : instructionCycles (.base i) = 1) : GroupHop s t 1 := by
  intro fuel
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ found step,unit]

private theorem entry (s : MachineState) (pc : s.pc = 5036) : GroupHop s (s.setPC 5564) 1 := by
  apply one s _ (.JAL .x0 528) (fetch_at s 235 _ (by decide) pc rfl) _ rfl
  simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend21,pc,MachineState.setReg]

private theorem test (s : MachineState) (pc : s.pc = 5564) :
    GroupHop s (s.setPC (if s.getReg .x20 ≤ s.getReg .x6 then 5576 else 5568)) 1 := by
  apply one s _ (.BGEU .x6 .x20 12) (fetch_at s 367 _ (by decide) pc rfl) _ rfl
  by_cases b : s.getReg .x20 ≤ s.getReg .x6
  · have cmp : (s.getReg .x6).ult (s.getReg .x20) = false := decide_eq_false (not_lt_of_ge b)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,pc,b,cmp]
  · have cmp : (s.getReg .x6).ult (s.getReg .x20) = true := decide_eq_true (lt_of_not_ge b)
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,pc,b,cmp]

private theorem full_return (s : MachineState) (pc : s.pc = 5576) : GroupHop s (s.setPC 5040) 2 := by
  have nop : GroupHop s (s.setPC 5580) 1 := by
    apply one s _ (.ADDI .x0 .x0 0) (fetch_at s 370 _ (by decide) pc rfl) _ rfl
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,pc]
  have jump : GroupHop (s.setPC 5580) (s.setPC 5040) 1 := by
    apply one _ _ (.JAL .x0 2096612) (fetch_at _ 371 _ (by decide) rfl rfl) _ rfl
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend21,MachineState.setReg,MachineState.setPC]
  exact nop.thenDo jump

private theorem masked_return (s : MachineState) (pc : s.pc = 5572) : GroupHop s (s.setPC 5040) 1 := by
  apply one _ _ (.JAL .x0 2096620) (fetch_at s 369 _ (by decide) pc rfl) _ rfl
  simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend21,pc,MachineState.setReg]

def maskExtra (node : Nat) : Nat :=
  if LENGTH≤node then 0 else if node<1048576 then 7 else 4

def withMaskReg (s : MachineState) (node : Nat) (answer : BitVec 256) : MachineState :=
  if LENGTH≤node then s else s.setReg .x1 (if node<1048576 then RV64.maskValue answer else 1048576)

theorem maskReg_keeps (s : MachineState) (n : Nat) (v : BitVec 256) (r : Reg) (h : r≠.x1) :
    (withMaskReg s n v).getReg r=s.getReg r := by
  unfold withMaskReg;split
  · rfl
  · exact MachineState.getReg_setReg_ne _ _ _ _ h.symm

theorem maskReg_mem (s : MachineState) (n : Nat) (v : BitVec 256) : (withMaskReg s n v).mem=s.mem := by
  unfold withMaskReg;split <;> rfl

private theorem extFetch (s : MachineState) (i : Nat) (op : Instr) (hi : i<10542)
    (pc : s.pc=R1bPC.pcAt i) (enc : R1b.Machine.stands .check i op) :
    fetch packedImage s = some (.base op) := by
  rw [←delivered_check_image]
  exact (R1b.Machine.fetched .check i hi s pc).trans (R1b.Machine.stood enc)

private theorem extJump (s : MachineState) (i j : Nat) (off : BitVec 21) (bound : i<10542)
    (pc : s.pc=R1bPC.pcAt i) (enc : R1b.Machine.stands .check i (.JAL .x0 off))
    (eq : R1bPC.pcAt i+signExtend21 off=R1bPC.pcAt j) : GroupHop s (s.setPC (R1bPC.pcAt j)) 1 := by
  apply one _ _ _ (extFetch _ _ _ bound pc enc) _ rfl
  simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,pc,eq]

private theorem maskRoute (raw : MachineState) (node : Nat) (rn : raw.getReg .x6=BitVec.ofNat 64 node)
    (bound : node<2^64) :
    let t:=(raw.setReg .x1 1048576).setPC (R1bPC.pcAt (if node<1048576 then 10532 else 10530))
    GroupHop (raw.setPC 5568) t 3 := by
  let a:=raw.setPC (R1bPC.pcAt 10528)
  let b:=(raw.setReg .x1 1048576).setPC (R1bPC.pcAt 10529)
  have ja:=extJump (raw.setPC 5568) 368 10528 40640 (by decide) rfl (by decide) (by decide)
  have hi : GroupHop a b 1 := by
    exact one _ _ _ (extFetch a 10528 (.LUI .x1 256) (by decide) rfl (by decide)) (by rfl) rfl
  have lt : (b.getReg .x6).ult (b.getReg .x1)=decide (node<1048576) := by
    change decide ((raw.getReg .x6).toNat<1048576)=_
    rw [rn,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
  have br : GroupHop b ((raw.setReg .x1 1048576).setPC (R1bPC.pcAt (if node<1048576 then 10532 else 10530))) 1 := by
    apply one _ _ _ (extFetch b 10529 (.BLTU .x6 .x1 12) (by decide) rfl (by decide)) _ rfl
    change some (if (b.getReg .x6).ult (b.getReg .x1) then b.setPC (b.pc+signExtend13 12) else b.setPC (b.pc+4))=_
    rw [lt]
    by_cases h : node<1048576 <;> simp only [h,decide_true,decide_false,if_true,if_false] <;> rfl
  exact (ja.thenDo hi).thenDo br

attribute [local irreducible] packedImage

theorem hybrid_lower_hash (s : MachineState) (source target node : Nat)
    (pc : s.pc = 5032) (nodeReg : s.getReg .x6=BitVec.ofNat 64 node)
    (len : s.getReg .x20=16777216) (nodeBound : node<2^64)
    (src : s.getReg .x10=BitVec.ofNat 64 source) (dst : s.getReg .x12=BitVec.ofNat 64 target)
    (mask : s.getReg .x23=s.getReg .x12)
    (selector : s.getReg .x5=0 ∧ s.getReg .x11=64 ∧ s.getReg .x13=0)
    (srcRoom : source+64≤MEMORY_BYTES) (dstRoom : target+32≤MEMORY_BYTES)
    (srcAlign : source%8=0) (dstAlign : target%8=0) (fuel : Nat) :
    execute packedImage (5+maskExtra node+fuel) s false = do
      let answer ← World.query (.inr (.inl (readBuffer s (source+32) 32 ++ readBuffer s source 32)))
      let result ← execute packedImage fuel
        ((withMaskReg (capCompressionAnswer s (Hybrid.normalize (node/2) answer)) node answer).setPC (s.pc+8)) false
      return result.charge (12+maskExtra node) 1 := by
  have lim : MEMORY_BYTES<2^64 := by decide
  have srcV : rangeValid (s.getReg .x10) 64=true := by
    simp only [src,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),decide_eq_true_eq];exact srcRoom
  have dstV : rangeValid (s.getReg .x12) 32=true := by
    simp only [dst,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target<2^64),decide_eq_true_eq];exact dstRoom
  have asrc : (s.getReg .x10).toNat%8=0 := by simpa [src,Nat.mod_eq_of_lt (by omega : source<2^64)] using srcAlign
  have adst : (s.getReg .x12).toNat%8=0 := by simpa [dst,Nat.mod_eq_of_lt (by omega : target<2^64)] using dstAlign
  have hash := cap_compression_execute packedImage s (project_fetch .lower _ pc) selector srcV dstV asrc adst (fuel+(4+maskExtra node)) false
  change execute packedImage (1+(fuel+(4+maskExtra node))) s false = (do
    let answer ← World.query (.inr (.inl (readBuffer s (s.getReg .x10).toNat 64)))
    let result ← execute packedImage (fuel+(4+maskExtra node)) (capCompressionAnswer s answer) false
    return result.charge 8 1) at hash
  rw [src,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),read_compression_halves s source srcAlign] at hash
  rw [show 5+maskExtra node+fuel=1+(fuel+(4+maskExtra node)) by omega,hash]
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
  have step : ordinaryStep raw (.base (.SH .x23 .x0 30)) =
      some ((capCompressionAnswer s (padLow answer)).setPC (s.pc+8)) := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,am,↓reduceIte]
    exact congrArg some (same.trans masked)
  have shifted := entry raw after
  have branch := test (raw.setPC 5564) rfl
  have nodeReg' : raw.getReg .x6=BitVec.ofNat 64 node := (cap_compression_register ..).trans nodeReg
  have length' : raw.getReg .x20=16777216 := (cap_compression_register ..).trans len
  have enough : (raw.getReg .x20 ≤ raw.getReg .x6) ↔ LENGTH≤node := by
    rw [nodeReg',length']
    change 16777216 ≤ (BitVec.ofNat 64 node).toNat ↔ 16777216 ≤ node
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nodeBound]
  by_cases full : LENGTH≤node
  · have h := enough.mpr full
    have side : ¬node/2<LENGTH/2 := by change ¬node/2<8388608; change 16777216≤node at full; omega
    simp only [MachineState.getReg_setPC,h,ite_true] at branch
    have run := (shifted.thenDo branch).thenDo (full_return _ rfl)
    have last := run fuel
    rw [maskExtra,if_pos full,show fuel+(4+0)=1+1+2+fuel by omega,last]
    simp [Hybrid.normalize,withMaskReg,maskExtra,full,side,pc,Execution.charge,←Nat.add_assoc,MachineState.setPC,raw]
  · have h : ¬ raw.getReg .x20 ≤ raw.getReg .x6 := fun le => full (enough.mp le)
    have side : node/2<LENGTH/2 := by change node/2<8388608; change ¬16777216≤node at full; omega
    simp only [MachineState.getReg_setPC,ite_eq_right h] at branch
    rw [resetPC raw 5564 5568] at branch
    have routing:=maskRoute raw node nodeReg' nodeBound
    by_cases small : node<1048576
    · simp only [if_pos small] at routing
      let begin:=(raw.setReg .x1 1048576).setPC (R1bPC.pcAt 10532)
      have pointer : begin.getReg .x23=BitVec.ofNat 64 target := reg.trans ((cap_compression_register ..).trans dst)
      have body:=R1b.Machine.runMask false begin target rfl pointer dstAlign dstRoom
      have projected := R1b.Machine.maskOutput false s target answer dst (mask.trans dst) dstAlign (by omega)
      have scratchGone : R1b.Machine.maskState false begin 4 =
          R1b.Machine.maskState false (raw.setPC (R1bPC.pcAt 10532)) 4 := by
        let z:=raw.setPC (R1bPC.pcAt 10532)
        let read:=(z.getHalfword (z.getReg .x23+signExtend12 28)).zeroExtend 64
        have first : execInstrBr (z.setReg .x1 1048576) (.LHU .x1 .x23 28)=execInstrBr z (.LHU .x1 .x23 28) := by
          change (((z.setReg .x1 1048576).setReg .x1 read).setPC (z.pc+4))=(z.setReg .x1 read).setPC (z.pc+4)
          rw [R1b.Machine.overwrite1]
        exact congrArg (fun t=>execInstrBr (execInstrBr (execInstrBr t (.SLLI .x1 .x1 50)) (.SRLI .x1 .x1 50)) (.SW .x23 .x1 28)) first
      let out:=((capCompressionAnswer s (Hybrid.pad238 answer)).setReg .x1 (RV64.maskValue answer)).setPC (R1bPC.pcAt 10536)
      have hop : GroupHop begin out 4 := by
        intro f;have run:=body f false
        change execute (Artifact.submission.image .check) (f+4) begin false=_ at run
        simp only [R1b.Machine.Code.image,delivered_check_image] at run
        have outEq : R1b.Machine.maskState false begin 4=out := scratchGone.trans projected
        rw [outEq] at run
        simpa only [Nat.add_comm 4 f] using run
      have j:=extJump out 10536 369 (BitVec.ofInt 21 (-40668)) (by decide) rfl (by decide) (by decide)
      change GroupHop (raw.setPC 5568) begin 3 at routing
      change GroupHop out (out.setPC 5572) 1 at j
      have back : GroupHop (out.setPC 5572) (out.setPC 5040) 1 := masked_return _ rfl
      have path : GroupHop raw (out.setPC 5040) (1+1+3+4+1+1) :=
        ((((shifted.thenDo branch).thenDo routing).thenDo hop).thenDo j).thenDo back
      have last:=path fuel
      rw [maskExtra,if_neg full,if_pos small,show fuel+(4+7)=(1+1+3+4+1+1)+fuel by omega,last]
      simp [Hybrid.normalize,withMaskReg,full,small,side,show node/2<524288 by omega,pc,
        Execution.charge,←Nat.add_assoc,out,MachineState.setPC]
    · simp only [if_neg small] at routing
      let begin:=(raw.setReg .x1 1048576).setPC (R1bPC.pcAt 10530)
      let stored:=(((capCompressionAnswer s (padLow answer)).setPC (s.pc+8)).setReg .x1 1048576).setPC (R1bPC.pcAt 10531)
      have sh : GroupHop begin stored 1 := by
        apply one _ _ _ (extFetch begin 10530 (.SH .x23 .x0 30) (by decide) rfl (by decide)) _ rfl
        have ok : memoryArgumentsValid begin (.SH .x23 .x0 30)=true := am
        simp only [ordinaryStep,ok,ite_true]
        have eq : execInstrBr begin (.SH .x23 .x0 30) =
            ((execInstrBr raw (.SH .x23 .x0 30)).setReg .x1 1048576).setPC (R1bPC.pcAt 10531) := rfl
        rw [eq,same,masked]
      have j:=extJump stored 10531 369 (BitVec.ofInt 21 (-40648)) (by decide) rfl (by decide) (by decide)
      change GroupHop (raw.setPC 5568) begin 3 at routing
      change GroupHop stored (stored.setPC 5572) 1 at j
      have back : GroupHop (stored.setPC 5572) (stored.setPC 5040) 1 := masked_return _ rfl
      have path : GroupHop raw (stored.setPC 5040) (1+1+3+1+1+1) :=
        ((((shifted.thenDo branch).thenDo routing).thenDo sh).thenDo j).thenDo back
      have last:=path fuel
      rw [maskExtra,if_neg full,if_neg small,show fuel+(4+4)=(1+1+3+1+1+1)+fuel by omega,last]
      simp [Hybrid.normalize,withMaskReg,full,small,side,show ¬node/2<524288 by omega,pc,
        Execution.charge,←Nat.add_assoc,stored,MachineState.setPC] <;> rfl

end TwoPermutationPrototype.Packed.Checker
