import CommitGolfCandidate.R1bDecodedMemory
import CommitGolfCandidate.R1bRoutes

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.R1b
open Machine (W byte proofBase Code Runs one fetched stood)
open R1bPC (pcAt)
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

inductive Route | count | length | low | high | packed deriving DecidableEq

def frontierCount (x : CheckInput) := (Carry.read x.proof 67488).toNat
def Route.ofInput (x : CheckInput) : Route :=
  if x.positions.card≠128 then .count else if x.proof.length≠67489 then .length
  else if frontierCount x<117 then .low else if 128<frontierCount x then .high else .packed

def Route.code (r : Route) : List (Nat×Instr) :=
  [(0,.JAL .x0 1488),(372,.ADDI .x6 .x0 128),(373,.BEQ .x16 .x6 8)] ++
  (if r=.count then [(374,.JAL .x0 40604)] else
   [(375,.LUI .x6 16),(376,.ADDI .x6 .x6 1953),(377,.BEQ .x17 .x6 8)] ++
   (if r=.length then [(378,.JAL .x0 40588)] else
    [(379,.ADDI .x8 .x15 0),(380,.LUI .x6 16),(381,.ADDI .x6 .x6 1952),
     (382,.ADD .x9 .x8 .x6),(383,.LBU .x7 .x9 0),(384,.ADDI .x6 .x0 117),(385,.BGEU .x7 .x6 8)] ++
    (if r=.low then [(386,.JAL .x0 40564)] else [(387,.ADDI .x6 .x0 128),(388,.BGEU .x6 .x7 8)] ++
     (if r=.high then [(389,.JAL .x0 40552)] else [(390,.ADDI .x6 .x0 30),(391,.MUL .x17 .x7 .x6),
     (392,.LUI .x6 16),(393,.ADDI .x6 .x6 2560),(394,.ADD .x17 .x17 .x6),(395,.ADDI .x18 .x15 0)]))))

def Route.next (r : Route) : Nat := match r with
  | .count|.length=>10525 | .low|.high=>10527 | .packed=>396


private theorem jump (s : MachineState) (i j : Nat) (d : BitVec 21) (hi : i<10542)
    (pc : s.pc=pcAt i) (enc : Machine.stands .check i (.JAL .x0 d))
    (toPC : pcAt i+signExtend21 d=pcAt j) : Runs .check s (s.setPC (pcAt j)) 1 1 := by
  apply one hi pc _ (stood enc)
  simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,pc,toPC]

private theorem eqBranch (s : MachineState) (i j : Nat) (a b : Reg) (hi : i<10542)
    (pc : s.pc=pcAt i) (enc : Machine.stands .check i (.BEQ a b 8))
    (toPC : (if s.getReg a=s.getReg b then pcAt i+signExtend13 8 else pcAt i+4)=pcAt j) :
    Runs .check s (s.setPC (pcAt j)) 1 1 := by
  apply one hi pc _ (stood enc)
  by_cases cond : s.getReg a=s.getReg b <;> simp [cond] at toPC <;>
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,cond,pc,toPC]

private theorem geBranch (s : MachineState) (i j : Nat) (a b : Reg) (hi : i<10542)
    (pc : s.pc=pcAt i) (enc : Machine.stands .check i (.BGEU a b 8))
    (toPC : (if (s.getReg a).ult (s.getReg b) then pcAt i+4 else pcAt i+signExtend13 8)=pcAt j) :
    Runs .check s (s.setPC (pcAt j)) 1 1 := by
  apply one hi pc _ (stood enc)
  by_cases cond : (s.getReg a).ult (s.getReg b)=true <;> simp only [cond,if_true,if_false] at toPC <;>
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,cond,pc] <;>
      exact congrArg s.setPC toPC

private def cost (r : Route) := (r.code.map (fun row=>instructionCycles (.base row.2))).sum

structure RouteResult (x : CheckInput) (r : Route) (s t : MachineState) : Prop where
  run : Runs .check s t r.code.length (cost r)
  pc : t.pc=pcAt r.next
  mem : t.mem=s.mem
  len : t.getReg .x17=W (if r=.packed then 64000+30*frontierCount x else x.proof.length)
  ptr : r=.packed → t.getReg .x18=W proofBase
  keep : ∀ reg,reg∈[Reg.x11,.x13,.x14,.x15,.x16] → t.getReg reg=s.getReg reg

private theorem entryLength (s : MachineState) :
    (execInstrBr s (.ADDI .x18 .x15 0)).getReg .x17=s.getReg .x17 := rfl

private theorem routeState (x : CheckInput) (s : MachineState) (fits : x.proof.length≤8388615680)
    (pc : s.pc=pcAt 0) (count : s.getReg .x16=W x.positions.card) (len : s.getReg .x17=W x.proof.length)
    (packet : s.getReg .x15=W proofBase)
    (readTag : x.proof.length=67489 → s.getByte (W (proofBase+67488))=Carry.read x.proof 67488) :
    ∃ t,RouteResult x (Route.ofInput x) s t := by
  have cb:=TwoPermutationPrototype.Checker.checker_positions_bound x
  have countEq : s.getReg .x16=128 ↔ x.positions.card=128 := by
    rw [count];constructor
    · exact Machine.wordNumber (by omega) (by decide : 128<2^64)
    · intro h;rw [h] <;> rfl
  have lenEq : s.getReg .x17=67489 ↔ x.proof.length=67489 := by
    rw [len];constructor
    · exact Machine.wordNumber (by omega) (by decide : 67489<2^64)
    · intro h;rw [h] <;> rfl
  let q372:=s.setPC (pcAt 372)
  have run372 : Runs .check s q372 1 1:=Codec.checkEnter s pc
  let q373:=execInstrBr q372 (.ADDI .x6 .x0 128)
  have e373:=one (c:=.check) (n:=372) (by decide) (show q372.pc=pcAt 372 from rfl) (.ADDI .x6 .x0 128) (stood (by decide))
    (show ordinaryStep q372 _=some q373 from rfl)
  have run373:=run372.trans e373
  have cmp373 : q373.getReg .x16=q373.getReg .x6 ↔ x.positions.card=128 := countEq
  by_cases batch : x.positions.card=128
  case neg =>
    let q374:=q373.setPC (pcAt 374)
    have e374:=eqBranch q373 373 374 .x16 .x6 (by decide) rfl (by decide) (by
      rw [if_neg (mt cmp373.mp batch)] <;> decide)
    have run374:=run373.trans e374
    let t:=q374.setPC (pcAt 10525)
    have last:=jump q374 374 10525 40604 (by decide) rfl (by decide) (by decide)
    have classify : Route.ofInput x=.count := by simp [Route.ofInput,batch]
    rw [classify]
    refine ⟨t,⟨run374.trans last,rfl,rfl,?_,?_,?_⟩⟩
    · exact len
    · intro bad;cases bad
    · intro reg hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl <;> rfl
  case pos =>
    let q375:=q373.setPC (pcAt 375)
    have e375:=eqBranch q373 373 375 .x16 .x6 (by decide) rfl (by decide) (by
      rw [if_pos (cmp373.mpr batch)] <;> decide)
    have run375:=run373.trans e375
    let q376:=execInstrBr q375 (.LUI .x6 16)
    have e376:=one (c:=.check) (n:=375) (by decide) (show q375.pc=pcAt 375 from rfl) (.LUI .x6 16) (stood (by decide))
      (show ordinaryStep q375 _=some q376 from rfl)
    have run376:=run375.trans e376
    let q377:=execInstrBr q376 (.ADDI .x6 .x6 1953)
    have e377:=one (c:=.check) (n:=376) (by decide) (show q376.pc=pcAt 376 from rfl) (.ADDI .x6 .x6 1953) (stood (by decide))
      (show ordinaryStep q376 _=some q377 from rfl)
    have run377:=run376.trans e377
    have cmp377 : q377.getReg .x17=q377.getReg .x6 ↔ x.proof.length=67489 := lenEq
    by_cases size : x.proof.length=67489
    case neg =>
      let q378:=q377.setPC (pcAt 378)
      have e378:=eqBranch q377 377 378 .x17 .x6 (by decide) rfl (by decide) (by
        rw [if_neg (mt cmp377.mp size)] <;> decide)
      have run378:=run377.trans e378
      let t:=q378.setPC (pcAt 10525)
      have last:=jump q378 378 10525 40588 (by decide) rfl (by decide) (by decide)
      have classify : Route.ofInput x=.length := by simp [Route.ofInput,batch,size]
      rw [classify]
      refine ⟨t,⟨run378.trans last,rfl,rfl,?_,?_,?_⟩⟩
      · exact len
      · intro bad;cases bad
      · intro reg hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl|rfl <;> rfl
    case pos =>
      let q379:=q377.setPC (pcAt 379)
      have e379:=eqBranch q377 377 379 .x17 .x6 (by decide) rfl (by decide) (by
        rw [if_pos (cmp377.mpr size)] <;> decide)
      have run379:=run377.trans e379
      let q380:=execInstrBr q379 (.ADDI .x8 .x15 0)
      have e380:=one (c:=.check) (n:=379) (by decide) (show q379.pc=pcAt 379 from rfl) (.ADDI .x8 .x15 0) (stood (by decide))
        (show ordinaryStep q379 _=some q380 from rfl)
      have run380:=run379.trans e380
      let q381:=execInstrBr q380 (.LUI .x6 16)
      have e381:=one (c:=.check) (n:=380) (by decide) (show q380.pc=pcAt 380 from rfl) (.LUI .x6 16) (stood (by decide))
        (show ordinaryStep q380 _=some q381 from rfl)
      have run381:=run380.trans e381
      let q382:=execInstrBr q381 (.ADDI .x6 .x6 1952)
      have e382:=one (c:=.check) (n:=381) (by decide) (show q381.pc=pcAt 381 from rfl) (.ADDI .x6 .x6 1952) (stood (by decide))
        (show ordinaryStep q381 _=some q382 from rfl)
      have run382:=run381.trans e382
      let q383:=execInstrBr q382 (.ADD .x9 .x8 .x6)
      have e383:=one (c:=.check) (n:=382) (by decide) (show q382.pc=pcAt 382 from rfl) (.ADD .x9 .x8 .x6) (stood (by decide))
        (show ordinaryStep q382 _=some q383 from rfl)
      have run383:=run382.trans e383
      have addr : q383.getReg .x9+0=W (proofBase+67488) := by
        change s.getReg .x15+0+W 67488+0=_
        rw [packet] <;> decide
      have safe : accessValid (W (proofBase+67488)) 1=true := by decide
      let q384:=execInstrBr q383 (.LBU .x7 .x9 0)
      have e384:=one (c:=.check) (n:=383) (by decide) (show q383.pc=pcAt 383 from rfl) (.LBU .x7 .x9 0) (stood (by decide))
        (show ordinaryStep q383 _=some q384 by
          change (if accessValid (q383.getReg .x9+0) 1 then some _ else none)=_
          rw [addr,safe] <;> rfl)
      have run384:=run383.trans e384
      have tag : q384.getReg .x7=W (frontierCount x) := by
        change (q383.getByte (q383.getReg .x9+0)).zeroExtend 64=_
        rw [addr];change (s.getByte _).zeroExtend 64=_;rw [readTag size]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth_of_le (by decide : 8≤64),BitVec.toNat_ofNat]
        have bound : frontierCount x<256 := (Carry.read x.proof 67488).isLt
        exact (Nat.mod_eq_of_lt (by omega : frontierCount x<2^64)).symm
      have natural : (W (frontierCount x)).toNat=frontierCount x := by
        have bound : frontierCount x<256 := (Carry.read x.proof 67488).isLt
        rw [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : frontierCount x<2^64)]
      let q385:=execInstrBr q384 (.ADDI .x6 .x0 117)
      have e385:=one (c:=.check) (n:=384) (by decide) (show q384.pc=pcAt 384 from rfl) (.ADDI .x6 .x0 117) (stood (by decide))
        (show ordinaryStep q384 _=some q385 from rfl)
      have run385:=run384.trans e385
      have cmp385 : (q385.getReg .x7).ult (q385.getReg .x6)=decide (frontierCount x<117) := by
        change decide ((q384.getReg .x7).toNat<117)=_;rw [tag,natural]
      by_cases low : frontierCount x<117
      case pos =>
        let q386:=q385.setPC (pcAt 386)
        have e386:=geBranch q385 385 386 .x7 .x6 (by decide) rfl (by decide) (by
          rw [cmp385,if_pos (decide_eq_true low)] <;> decide)
        have run386:=run385.trans e386
        let t:=q386.setPC (pcAt 10527)
        have last:=jump q386 386 10527 40564 (by decide) rfl (by decide) (by decide)
        have classify : Route.ofInput x=.low := by simp [Route.ofInput,batch,size,low]
        rw [classify]
        refine ⟨t,⟨run386.trans last,rfl,rfl,?_,?_,?_⟩⟩
        · exact len
        · intro bad;cases bad
        · intro reg hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl|rfl|rfl <;> rfl
      case neg =>
        let q387:=q385.setPC (pcAt 387)
        have e387:=geBranch q385 385 387 .x7 .x6 (by decide) rfl (by decide) (by
          rw [cmp385,if_neg (by simpa using low)] <;> decide)
        have run387:=run385.trans e387
        let q388:=execInstrBr q387 (.ADDI .x6 .x0 128)
        have e388:=one (c:=.check) (n:=387) (by decide) (show q387.pc=pcAt 387 from rfl) (.ADDI .x6 .x0 128) (stood (by decide))
          (show ordinaryStep q387 _=some q388 from rfl)
        have run388:=run387.trans e388
        have cmp388 : (q388.getReg .x6).ult (q388.getReg .x7)=decide (128<frontierCount x) := by
          change decide (128<(q384.getReg .x7).toNat)=_;rw [tag,natural]
        by_cases high : 128<frontierCount x
        case pos =>
          let q389:=q388.setPC (pcAt 389)
          have e389:=geBranch q388 388 389 .x6 .x7 (by decide) rfl (by decide) (by
            rw [cmp388,if_pos (decide_eq_true high)] <;> decide)
          have run389:=run388.trans e389
          let t:=q389.setPC (pcAt 10527)
          have last:=jump q389 389 10527 40552 (by decide) rfl (by decide) (by decide)
          have classify : Route.ofInput x=.high := by simp [Route.ofInput,batch,size,low,high]
          rw [classify]
          refine ⟨t,⟨run389.trans last,rfl,rfl,?_,?_,?_⟩⟩
          · exact len
          · intro bad;cases bad
          · intro reg hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
            rcases hr with rfl|rfl|rfl|rfl|rfl <;> rfl
        case neg =>
          let q390:=q388.setPC (pcAt 390)
          have e390:=geBranch q388 388 390 .x6 .x7 (by decide) rfl (by decide) (by
            rw [cmp388,if_neg (by simpa using high)] <;> decide)
          have run390:=run388.trans e390
          let q391:=execInstrBr q390 (.ADDI .x6 .x0 30)
          have e391:=one (c:=.check) (n:=390) (by decide) (show q390.pc=pcAt 390 from rfl) (.ADDI .x6 .x0 30) (stood (by decide))
            (show ordinaryStep q390 _=some q391 from rfl)
          have run391:=run390.trans e391
          let q392:=execInstrBr q391 (.MUL .x17 .x7 .x6)
          have e392:=one (c:=.check) (n:=391) (by decide) (show q391.pc=pcAt 391 from rfl) (.MUL .x17 .x7 .x6) (stood (by decide))
            (show ordinaryStep q391 _=some q392 from rfl)
          have run392:=run391.trans e392
          let q393:=execInstrBr q392 (.LUI .x6 16)
          have e393:=one (c:=.check) (n:=392) (by decide) (show q392.pc=pcAt 392 from rfl) (.LUI .x6 16) (stood (by decide))
            (show ordinaryStep q392 _=some q393 from rfl)
          have run393:=run392.trans e393
          let q394:=execInstrBr q393 (.ADDI .x6 .x6 2560)
          have e394:=one (c:=.check) (n:=393) (by decide) (show q393.pc=pcAt 393 from rfl) (.ADDI .x6 .x6 2560) (stood (by decide))
            (show ordinaryStep q393 _=some q394 from rfl)
          have run394:=run393.trans e394
          let q395:=execInstrBr q394 (.ADD .x17 .x17 .x6)
          have e395:=one (c:=.check) (n:=394) (by decide) (show q394.pc=pcAt 394 from rfl) (.ADD .x17 .x17 .x6) (stood (by decide))
            (show ordinaryStep q394 _=some q395 from rfl)
          have run395:=run394.trans e395
          let q396:=execInstrBr q395 (.ADDI .x18 .x15 0)
          have e396:=one (c:=.check) (n:=395) (by decide) (show q395.pc=pcAt 395 from rfl) (.ADDI .x18 .x15 0) (stood (by decide))
            (show ordinaryStep q395 _=some q396 from rfl)
          have run396:=run395.trans e396
          let t:=q396
          have classify : Route.ofInput x=.packed := by simp [Route.ofInput,batch,size,low,high]
          rw [classify]
          refine ⟨t,⟨run396,rfl,rfl,?_,?_,?_⟩⟩
          · have factor : q391.getReg .x6=W 30 := rfl
            have src : q391.getReg .x7=q384.getReg .x7 := rfl
            have product : q392.getReg .x17=W (frontierCount x*30) := by
              change q391.getReg .x7*q391.getReg .x6=_
              rw [src,tag,factor];exact (BitVec.ofNat_mul ..).symm
            have constant : q394.getReg .x6=W 64000 := by change 65536#64+signExtend12 2560=W 64000;decide
            have old : q394.getReg .x17=q392.getReg .x17 := rfl
            have value : q395.getReg .x17=W (64000+30*frontierCount x) := by
              change q394.getReg .x17+q394.getReg .x6=_
              rw [old,product,constant,←BitVec.ofNat_add,Nat.mul_comm (frontierCount x),Nat.add_comm]
            rw [if_pos (rfl : Route.packed=Route.packed)]
            exact (entryLength q395).trans value
          · intro _;exact (BitVec.add_zero _).trans packet
          · intro reg hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
            rcases hr with rfl|rfl|rfl|rfl|rfl <;> rfl

theorem routeRun (x : CheckInput) (fits : x.proof.length≤8388615680) :
    ∃ t,RouteResult x (Route.ofInput x) (initial x) t := by
  apply routeState x (initial x) fits rfl rfl rfl rfl
  intro len
  have bound : 67488<x.proof.length:=by omega
  exact (TwoPermutationPrototype.Checker.check_input_proof_byte x (by change _≤8858378240;omega) 67488 bound).trans
    (by simp [Carry.read,List.getElem?_eq_getElem bound])

end TwoPermutationPrototype.Packed.Checker
