import CommitGolfCandidate.ReconstructedCheckRecordSpec
import CommitGolfCandidate.ReconstructedCheckCapArith

namespace CommitGolfCandidate.Reconstruction.CheckRecordGuard
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CheckCapArith
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8500
set_option maxHeartbeats 500000
abbrev W:=BitVec.ofNat 64

def keep : List Reg := [.x2,.x8,.x19,.x23,.x24,.x11,.x12,.x13,.x14]
def code : List Line := [(.x10,.op (.or .x18 .x27)),(.x15,.op (.or .x20 .x25)),(.x15,.op (.or .x10 .x15)),(.x10,.op (.addi .x0 4095))]

private theorem certified : listed 381 code=true := by decide
private theorem tested : CheckStraight.actualAt 385=some (.base (.BNE .x15 .x0 6880)):=CheckDecode.same_sound (by decide)
private theorem target : CommitBlocks.addr 385+signExtend13 6880=CommitBlocks.addr 57:=by decide

private theorem combined (a b c d : Word) :
    (a ||| b ||| (c ||| d))=0#64 ↔ [b.toNat,a.toNat,c.toNat,d.toNat]=[0,0,0,0] := by
  have nat (x : Word) : x.toNat=0 ↔ x=0#64:=⟨fun h=>BitVec.eq_of_toNat_eq (y:=0#64) h,fun eq=>eq ▸ rfl⟩
  simp only [BitVec.or_eq_zero_iff,List.cons.injEq,and_true,nat]
  exact ⟨fun ⟨⟨a,b⟩,c,d⟩=>⟨b,a,c,d⟩,fun ⟨b,a,c,d⟩=>⟨⟨a,b⟩,c,d⟩⟩

private theorem zero (s : MachineState) : (effect s code).getReg .x15=0#64 ↔ CheckRecordHeader.limbs s=[0,0,0,0] := by
  rw [register];exact combined _ _ _ _

private theorem minusOne (s : MachineState) : (effect s code).getReg .x10=0xffffffffffffffff#64 := by
  rw [register];change 0#64+signExtend12 4095=0xffffffffffffffff#64;decide

theorem positive (o : Oracle) (s : MachineState) (pc : s.pc=CommitBlocks.addr 381) :
    ∃ t,Segment o 5 s t [] ∧ t.pc=(if CheckRecordHeader.limbs s=[0,0,0,0] then CommitBlocks.addr 386 else CommitBlocks.addr 57) ∧
      t.getReg .x10=0xffffffffffffffff#64 ∧ (∀ r∈keep,t.getReg r=s.getReg r) ∧ ∀ a,a<2^33→t.getMem (wordAddress a)=s.getMem (wordAddress a) := by
  let u:=effect s code
  have seg:=CheckCapArith.positive o s 381 code pc certified
  have b:=CheckBranch.event o u 385 57 .ne .x15 .x0 6880 (by decide) (location s 381 code pc) tested target
  refine ⟨u.setPC (if CheckOrdinary.Cond.test .ne (u.getReg .x15) (u.getReg .x0) then CommitBlocks.addr 57 else CommitBlocks.addr 386),by simpa only [List.nil_append,show code.length=4 by decide] using compose seg b,?_,minusOne s,?_,?_⟩
  · change (if (u.getReg .x15 != 0#64)=true then _ else _)=_
    by_cases ok : u.getReg .x15=0#64
    · rw [ite_eq_left ((zero s).mp ok),ok];rfl
    · rw [ite_eq_right (fun q=>ok ((zero s).mpr q))];simp [ok]
  · intro r hr;exact outside s code r ((by decide : ∀ q : Reg,q∈keep→q∉code.map Prod.fst) r hr)
  · intro a _;exact congrFun (memory s code) _

end CommitGolfCandidate.Reconstruction.CheckRecordGuard
