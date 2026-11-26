import CommitGolfCandidate.ReconstructedOpeningRecordFrame

namespace CommitGolfCandidate.Reconstruction.OpeningRecordMark
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps OpeningCursor
open TwoPermutationPrototype.RV64 OpeningQuery OpeningRowEntry
open CommitBlocks (addr)
set_option maxRecDepth 14000
attribute [local irreducible] execute ArtifactEncoding.decode

def byteAt (i : Index) := 4259840+512+i.val/32768
def wordAt (i : Index) := byteAt i/8
theorem mark_range (i : Index) : 532480≤wordAt i ∧ wordAt i<532608 := by
  have h : i.val < 2^24 := i.isLt
  unfold wordAt byteAt;omega

def setupOps : List Op := [.reg .x7 (.addi .x20 1582),.reg .x10 (.srli .x10 15),
  .reg .x11 (.lui 1040),.reg .x10 (.add .x10 .x11),.reg .x11 (.addi .x0 1)]

private theorem calculated (i : Index) : (W (2^24+i.val) >>> (15 : Nat))+W 4259840=W (byteAt i) := by
  have small : i.val < 2^24 := i.isLt
  have sh : W (2^24+i.val) >>> (15:Nat)=W ((2^24+i.val)/32768) := by
    apply BitVec.eq_of_toNat_eq
    simp only [W,BitVec.toNat_ofNat,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : 2^24+i.val<2^64),Nat.mod_eq_of_lt (by omega : (2^24+i.val)/32768<2^64)]
  rw [sh,←BitVec.ofNat_add];congr 1;unfold byteAt;omega

theorem setup (e : Env) (m : Model) (h : Ready9 e m) :
    let a := after m setupOps
    a.reg .x7=W (e.cursor+3633) ∧ a.reg .x10=W (byteAt e.index) ∧ a.reg .x11=1 := by
  refine ⟨?_,?_,?_⟩
  · change m.reg .x20+signExtend12 1582=_
    rw [h.r20];exact OpeningRowOps.plusBit e.cursor 2051 1582 3633 1582 rfl rfl
  · change (m.reg .x10 >>> (15 : Nat))+W 4259840=_
    rw [h.r10,calculated]
  · change m.reg .x0+1=1;rw [h.r0];rfl

theorem setupRun (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 130) (f : Fits s m) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 5 s t ∧ t.pc=addr 135 ∧ Fits t (after m setupOps) :=
  OpeningStraight.block o m setupOps 130 (by decide) ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
    (by simp [setupOps,Checked,Op.Valid]) s pc f

def mark (m : Model) (i : Index) := m.store (wordAt i)
  (replaceByte (m.mem (wordAt i)) (byteOffset (W (byteAt i))) 1)

theorem write (o : Oracle) (m : Model) (i : Index) (p : m.reg .x10=W (byteAt i)) (one : m.reg .x11=1) :
    Contract o [.SB .x10 .x11 0] m (mark m i) := by
  intro s fits
  have r := mark_range i
  have small : i.val < 2^24 := i.isLt
  have b : accessValid (W (byteAt i)) 1=true := by
    simp [accessValid,rangeValid,MEMORY_BYTES,W,byteAt];omega
  have eq₁ : s.getReg .x10+signExtend12 0=W (byteAt i) := (BitVec.add_zero _).trans ((fits.registers _).trans p)
  have eq₂ : (s.getReg .x11).truncate 8=1 := by rw [fits.registers,one];rfl
  have alignedAt : alignToDword (W (byteAt i))=wordAddress (wordAt i) := OpeningCursor.aligned _
  have physical : s.getMem (wordAddress (wordAt i))=m.mem (wordAt i) := fits.memory _ (by omega)
  let v := replaceByte (m.mem (wordAt i)) (byteOffset (W (byteAt i))) 1
  let t := (s.setMem (wordAddress (wordAt i)) v).setPC (s.pc+4)
  have step : ordinaryStep s (.base (.SB .x10 .x11 0))=some t := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,eq₁,eq₂,b,ite_true,
      MachineState.setByte,alignedAt,physical,t,v]
  exact ⟨t,Run.one (.ordinary _ _ _ step rfl),(fits.store _ v (by omega)).pc _⟩

theorem keep (m : Model) (i : Index) (w : Nat) (away : w<532480 ∨ 532608≤w) : (mark m i).mem w=m.mem w := by
  have b := mark_range i
  change (if w=wordAt i then _ else _)=_
  rw [ite_eq_right (by omega : w≠wordAt i)]

end CommitGolfCandidate.Reconstruction.OpeningRecordMark
