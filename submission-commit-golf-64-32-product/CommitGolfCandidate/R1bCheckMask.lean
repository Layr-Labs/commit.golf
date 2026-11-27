import CommitGolfCandidate.R1bMachine
import CommitGolfCandidate.TwoPermutationPackedParentMask

namespace CommitGolfCandidate.R1b.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 (maskValue)
open R1bPC (pcAt)
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384
attribute [local irreducible] writeBits capCompressionAnswer

def maskOps (cap : Bool) : List Instr :=
  let r := if cap then Reg.x12 else Reg.x23
  [.LHU .x1 r 28,.SLLI .x1 .x1 50,.SRLI .x1 .x1 50,.SW r .x1 28]
def maskPC (cap : Bool) := if cap then 10537 else 10532
def maskState (cap : Bool) (s : MachineState) (k : Nat) := ((maskOps cap).take k).foldl execInstrBr s

private theorem maskCode (cap : Bool) : listed .check (maskPC cap) (maskOps cap) := by cases cap <;> decide

theorem runMask (cap : Bool) (s : MachineState) (target : Nat)
    (pc : s.pc=pcAt (maskPC cap)) (reg : s.getReg (if cap then .x12 else .x23)=W target)
    (align : target%8=0) (fits : target+32≤MEMORY_BYTES) :
    Runs .check s (maskState cap s 4) 4 4 := by
  let p := W (target+28)
  have pa : s.getReg (if cap then .x12 else .x23)+signExtend12 28=p := by
    rw [reg];change W target+W 28=W _;rw [←BitVec.ofNat_add]
  have safe2 : accessValid p 2=true := Safe.valid ⟨by omega,by omega⟩
  have safe4 : accessValid p 4=true := Safe.valid ⟨by omega,by omega⟩
  have decoded := matchesListed (maskCode cap)
  intro fuel coins
  rw [Nat.add_comm fuel 4]
  apply execute_unit_steps (states:=maskState cap s) (count:=4)
  intro k hk
  have inside : k<(maskOps cap).length := by cases cap <;> exact hk
  have atPC : (maskState cap s k).pc=pcAt (maskPC cap+k) := by
    cases cap <;> interval_cases k <;> simp [maskState,maskOps,List.foldl,execInstrBr,pc,pcAt,maskPC,MachineState.setPC]
  have limit : maskPC cap+k<Code.check.count := by
    have h : maskPC cap<10538 := by cases cap <;> decide
    change maskPC cap+k<10624;omega
  have v2 : accessValid (s.getReg (if cap then .x12 else .x23)+signExtend12 28) 2=true := by rw [pa];exact safe2
  have v4 : accessValid (s.getReg (if cap then .x12 else .x23)+signExtend12 28) 4=true := by rw [pa];exact safe4
  refine ⟨.base (maskOps cap)[k],(fetched .check (maskPC cap+k) limit _ atPC).trans (decoded k inside),?_,?_⟩
  · have access : memoryArgumentsValid (maskState cap s k) ((maskOps cap)[k])=true := by
      cases cap <;> interval_cases k <;> first | rfl | exact v2 | exact v4
    have normal : ordinaryStep (maskState cap s k) (.base (maskOps cap)[k]) =
        (if memoryArgumentsValid (maskState cap s k) (maskOps cap)[k] then
          some (execInstrBr (maskState cap s k) (maskOps cap)[k]) else none) := by
      cases cap <;> interval_cases k <;> rfl
    rw [normal,if_pos access];cases cap <;> interval_cases k <;> rfl
  · cases cap <;> interval_cases k <;> rfl

theorem shiftMask (v : BitVec 16) :
    (v.zeroExtend 64 <<< (50 : Nat)) >>> (50 : Nat)=v.zeroExtend 64 &&& 16383 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp (config := {decide := true})

theorem overwrite1 (s : MachineState) (a b : Word) : (s.setReg .x1 a).setReg .x1 b=s.setReg .x1 b := by
  cases s
  simp only [MachineState.setReg,MachineState.mk.injEq,and_true,true_and]
  funext r;by_cases e:r=Reg.x1 <;> simp [e]

private def clipped (s : MachineState) (r : Reg) : Word :=
  ((s.getHalfword (s.getReg r+signExtend12 28)).zeroExtend 64 <<< (50 : Nat)) >>> (50 : Nat)

private theorem shape (cap : Bool) (s : MachineState) :
    let r:=if cap then Reg.x12 else .x23
    let v:=clipped s r
    maskState cap s 4=((s.setWord32 (s.getReg r+signExtend12 28) (v.truncate 32)).setReg .x1 v).setPC (s.pc+16) := by
  let r:=if cap then Reg.x12 else .x23
  let addr:=s.getReg r+signExtend12 28
  let a:=(s.getHalfword addr).zeroExtend 64
  let b:=a <<< (50 : Nat)
  let v:=b >>> (50 : Nat)
  cases cap <;>
    change (((((s.setReg .x1 a).setReg .x1 b).setReg .x1 v).setWord32 addr (v.truncate 32)).setPC (s.pc+4+4+4+4))=_
  all_goals rw [overwrite1,overwrite1,BitVec.add_assoc,BitVec.add_assoc,BitVec.add_assoc] <;> rfl

theorem maskOutput (cap : Bool) (s : MachineState) (a : Nat) (v : BitVec 256)
    (dest : s.getReg .x12=W a) (same : s.getReg (if cap then .x12 else .x23)=W a)
    (al : a%8=0) (fit : a+32≤2^64) :
    let raw:=(capCompressionAnswer s v).setPC (pcAt (maskPC cap))
    maskState cap raw 4 =
      ((capCompressionAnswer s (TwoPermutationPrototype.RV64.pad238 v)).setReg .x1 (maskValue v)).setPC
        (pcAt (maskPC cap+4)) := by
  let reg:=if cap then Reg.x12 else .x23
  let raw:=(capCompressionAnswer s v).setPC (pcAt (maskPC cap))
  have addr : raw.getReg reg + signExtend12 28=W (a+28) := by
    change (capCompressionAnswer s v).getReg reg + signExtend12 28=_
    rw [cap_compression_register s v reg,same]
    change W a+W 28=W _;rw [←BitVec.ofNat_add]
  have value : clipped raw reg=maskValue v := by
    unfold clipped
    rw [addr,shiftMask]
    have rd : raw.getHalfword (W (a+28))=v.extractLsb' 224 16 := by
      change (capCompressionAnswer s v).getHalfword (W (a+28))=_
      unfold capCompressionAnswer
      rw [dest];exact TwoPermutationPrototype.RV64.loaded238 s a v al fit
    rw [rd] <;> rfl
  have clean : (capCompressionAnswer s v).setWord32 (W (a+28)) ((maskValue v).truncate 32)=
      capCompressionAnswer s (TwoPermutationPrototype.RV64.pad238 v) := by
    unfold capCompressionAnswer;rw [dest];exact TwoPermutationPrototype.RV64.cleared238 s a v al fit
  change maskState cap raw 4=_
  rw [shape]
  change ((raw.setWord32 (raw.getReg reg+signExtend12 28) ((clipped raw reg).truncate 32)).setReg .x1 (clipped raw reg)).setPC (raw.pc+16)=_
  rw [addr,value]
  change ((((capCompressionAnswer s v).setWord32 _ _).setReg .x1 (maskValue v)).setPC (pcAt (maskPC cap)+16))=_
  rw [clean];cases cap <;> rfl

end CommitGolfCandidate.R1b.Machine
