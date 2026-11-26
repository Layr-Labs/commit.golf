import CommitGolfCandidate.ReconstructedCheckRecordHeader
import CommitGolfCandidate.ReconstructedCheckDivisionResult
import CommitGolfCandidate.ReconstructedCheckBranch
import CommitGolfCandidate.ReconstructedCheckLowerLayout

namespace CommitGolfCandidate.Reconstruction.CheckMixed
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded LeafModel CommitBlocks
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
abbrev W:=BitVec.ofNat 64

def base (i : Fin 15) := sameSize.bases[10+i.val]?.getD 0
def width (i : Fin 15) := CheckLowerPlan.lowWidth (10+i.val)
def out (i : Fin 15) (xs : List Nat) := if i.val<10 then HonestDivision.divide (base i) 0 xs else (xs,0)
def frame : List Reg := [.x1,.x2,.x3,.x4,.x5,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x16,.x17,.x19,.x21,.x22,.x23,.x24,.x26]

private theorem bounds : ∀ i : Fin 15, 0<base i ∧ base i≤2^31 ∧ (i.val<10 ↔ 1<base i) ∧ (W (width i)).toNat%64=width i-192 := by decide

private theorem route : ∀ i : Fin 15,CheckOrdinary.Cond.test .lt 11 (W (10+i.val)+(-8))=decide (10 ≤ i.val) := by decide

private theorem saved (m : Model) (cell : Nat) (r : Reg) (inside : r∈frame) : (CheckDivision.after m cell).reg r=m.reg r := by
  simp only [frame,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst r <;> rfl

def typed (s : MachineState) (q3 q2 q1 q0 : Fin (2^32)) : Prop :=
  s.getReg .x27=W q3.val ∧ s.getReg .x18=W q2.val ∧ s.getReg .x20=W q1.val ∧ s.getReg .x25=W q0.val

private theorem initial_limbs (s : MachineState) (q3 q2 q1 q0 : Fin (2^32)) (head : typed s q3 q2 q1 q0) :
    CheckRecordHeader.limbs s=[q3.val,q2.val,q1.val,q0.val] := by
  obtain ⟨a,b,c,d⟩:=head
  have wide (q : Fin (2^32)) : q.val<2^64:=Nat.lt_of_lt_of_le q.isLt (by decide)
  simp only [CheckRecordHeader.limbs,a,b,c,d,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (wide q3),
    Nat.mod_eq_of_lt (wide q2),Nat.mod_eq_of_lt (wide q1),Nat.mod_eq_of_lt (wide q0)]

/-- The branch at instruction 350 selects exactly the ten mixed-radix depths.
The quotient stays in the header registers and the recovered digit extends the sibling. -/
theorem positive (o : Oracle) (s : MachineState) (i : Fin 15) (cell : Nat) (room : cell<2^33)
    (pc : s.pc=addr 350) (guardV : s.getReg .x7=11) (depth : s.getReg .x28=W (10+i.val)+(-8))
    (place : s.getReg .x22=wordAddress cell) (tableValue : s.getMem (wordAddress cell)=W (base i))
    (field : s.getReg .x15=W (width i)) (q3 q2 q1 q0 : Fin (2^32)) (head : typed s q3 q2 q1 q0) :
    let v:=out i [q3.val,q2.val,q1.val,q0.val]
    ∃ t n, n≤31 ∧ Segment o n s t [] ∧ t.pc=addr 246 ∧
      CheckRecordHeader.limbs t=v.1 ∧ t.getReg .x6=(W v.2 <<< (width i-192)) ||| s.getReg .x6 ∧
      (∀ r∈frame,t.getReg r=s.getReg r) ∧ (∀ a,a<2^33→t.getMem (wordAddress a)=s.getMem (wordAddress a)) := by
  let xs:=[q3.val,q2.val,q1.val,q0.val]
  have first:=CheckBranch.event o s 350 246 .lt .x7 .x28 7776 (by decide) pc (by rfl) (by decide)
  rw [guardV,depth,route] at first
  by_cases mix : i.val<10
  · have less : ¬ 10 ≤ i.val:=by omega
    simp only [decide_eq_false less,Bool.false_eq_true,ite_false] at first
    let u:=s.setPC (addr 351)
    let m:=CheckRecordHeader.model u
    have fit:=CheckRecordHeader.fits u
    obtain ⟨v,divseg,pos,agree⟩:=CheckDivision.positive o m cell room place u rfl fit
    obtain ⟨r3,r2,r1,r0⟩:=head
    obtain ⟨limbs,_,word,memory⟩:=CheckDivisionResult.result m cell (base i) ⟨(bounds i).1,(bounds i).2.1⟩ tableValue q3 q2 q1 q0 r3 r2 r1 r0
    have j:=CheckBranch.jump o v 380 246 2096616 (by decide) pos (by rfl) (by decide)
    have hi : m.reg .x15=W (width i):=field
    rw [hi,(bounds i).2.2.2] at word
    simp only [out,ite_eq_left mix]
    refine ⟨v.setPC (addr 246),31,by decide,by simpa using compose (compose first divseg) j,rfl,?_,?_,?_,?_⟩
    · change [(v.getReg .x27).toNat,(v.getReg .x18).toNat,(v.getReg .x20).toNat,(v.getReg .x25).toNat]=_
      simp only [agree.registers];exact limbs
    · change v.getReg .x6=_;rw [agree.registers];exact word
    · intro r hr;change v.getReg r=_;rw [agree.registers,saved _ _ _ hr];rfl
    · intro a small;change memoryView v a=_
      rw [agree.memory _ small,memory];rfl
  · have take : 10 ≤ i.val:=by omega
    simp only [decide_eq_true take,ite_true] at first
    simp only [out,ite_eq_right mix]
    refine ⟨s.setPC (addr 246),1,by decide,first,rfl,initial_limbs _ _ _ _ _ head,?_,fun _ _=>rfl,fun _ _=>rfl⟩
    change (s.getReg .x6)=0#64 <<< (width i-192) ||| s.getReg .x6;simp

end CommitGolfCandidate.Reconstruction.CheckMixed
