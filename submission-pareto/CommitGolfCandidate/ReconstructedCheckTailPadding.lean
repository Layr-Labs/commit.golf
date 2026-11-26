import CommitGolfCandidate.ReconstructedCheckTailOps

namespace CommitGolfCandidate.Reconstruction.CheckTailPadding
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CheckCapArith CommitBlocks CheckTailOps
open TwoPermutationPrototype.RV64
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
attribute [local irreducible] ArtifactEncoding.decode execute

def remainder (c stream : Nat) := W (HonestStream.word stream (c/64)) >>> (c%64)
def Padded (c stream : Nat) := c%64=0 ∨ remainder c stream=0
instance (c stream : Nat) : Decidable (Padded c stream) := by unfold Padded;infer_instance

def bitOps : List Line := [(.x11,.op (.andi .x24 63))]
def ptrOps : List Line := [(.x12,.op (.srli .x24 3)),(.x12,.op (.andi .x12 4088)),(.x13,.op (.lui 78848)),
  (.x13,.addiw .x13 131),(.x13,.op (.slli .x13 5)),(.x12,.op (.add .x12 .x13))]
def shiftOps : List Line := [(.x11,.op (.srl .x12 .x11))]

private theorem bitListed : listed 657 bitOps=true := by decide +kernel
private theorem ptrListed : listed 659 ptrOps=true := by decide +kernel
private theorem shiftListed : listed 666 shiftOps=true := by decide +kernel
private theorem ldListed : CheckMemoryOps.word 665 (.base (.LD .x12 .x12 0))=true := by decide +kernel
private theorem firstBranch : CheckStraight.actualAt 658=some (.base (.BEQ .x11 .x0 40)) := CheckDecode.same_sound (by decide +kernel)
private theorem lastBranch : CheckStraight.actualAt 667=some (.base (.BNE .x11 .x0 5752)) := CheckDecode.same_sound (by decide +kernel)

private theorem offset (s : MachineState) (c : Nat) (bound : c≤70000000000) (cursor : s.getReg .x24=W c) :
    (effect s bitOps).getReg .x11=W (c%64) := by
  rw [register];change s.getReg .x24 &&& W 63=W (c%64);rw [cursor]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : c<2^64),Nat.mod_eq_of_lt (by omega : c%64<2^64)]
  exact Nat.and_two_pow_sub_one_eq_mod c 6

private theorem rawPtr (r : Reg → Word) : regs r ptrOps .x12=((r .x24 >>> (3 : Nat)) &&& 0xfffffffffffffff8#64)+W 10334769248 := by
  simp [ptrOps,regs,update,E.value,OpeningOps.Expr.eval]
  first | rfl | congr 1 <;> decide +kernel

private theorem ptr (s : MachineState) (c : Nat) (bound : c≤70000000000) (cursor : s.getReg .x24=W c) :
    (effect s ptrOps).getReg .x12+signExtend12 0=wordAddress (1291846156+c/64) := by
  rw [register,rawPtr,cursor,align _ (by omega),show signExtend12 0=0#64 by decide,BitVec.add_zero,←BitVec.ofNat_add]
  change W (8*(c/64)+10334769248)=W (8*(1291846156+c/64))
  exact congrArg W (by omega)

private theorem masked (s : MachineState) (c bits : Nat) (v : s.getReg .x12=W (HonestStream.word bits (c/64)))
    (off : s.getReg .x11=W (c%64)) : (effect s shiftOps).getReg .x11=remainder c bits := by
  rw [register];change s.getReg .x12 >>> ((s.getReg .x11).toNat%64)=_
  rw [v,off];unfold remainder W
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : c%64<2^64),Nat.mod_mod]

theorem ordinary (s : MachineState) (ops : List Line) (h : ∀ r∈[Reg.x2,.x8,.x24],r∉ops.map Prod.fst) :
    Frame s (effect s ops) :=
  ⟨fun r hr => outside s ops r (h r hr),fun p => congrFun (memory s ops) p⟩

theorem Frame.trans' {s t u : MachineState} (x : Frame s t) (y : Frame t u) : Frame s u :=
  ⟨fun r h => (y.regs r h).trans (x.regs r h),fun p => (y.mem p).trans (x.mem p)⟩

def readState (u : MachineState) (v : Word) := (u.setReg .x12 v).setPC (addr 666)
private theorem readOther (u : MachineState) (v : Word) (r : Reg) (h : r≠.x12) :
    (readState u v).getReg r=u.getReg r := by
  unfold readState;rw [MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg];simp [Ne.symm h]
private theorem readMemory (u : MachineState) (val : Word) (p : Word) : (readState u val).getMem p=u.getMem p := rfl
private theorem readValue (u : MachineState) (v : Word) : (readState u v).getReg .x12=v := rfl
private theorem framePC (a t : MachineState) (p : Word) (h : Frame a t) : Frame a (t.setPC p) :=
  ⟨fun r hr => (MachineState.getReg_setPC ..).trans (h.regs r hr),h.mem⟩

theorem readRun (o : Oracle) (s : MachineState) (c bits : Nat) (bound : c≤70000000000)
    (entry : s.pc=addr 659) (cursor : s.getReg .x24=W c) (off : s.getReg .x11=W (c%64))
    (stream : CheckLayout.StreamMemory s bits) :
    ∃ t, Segment o 9 s t [] ∧ t.pc=(if remainder c bits=0 then addr 668 else addr 57) ∧
      t.getReg .x10=s.getReg .x10 ∧ Frame s t := by
  let u := effect s ptrOps
  have ru := positive o s 659 ptrOps entry ptrListed
  have pc665 : u.pc=addr 665 := location s 659 ptrOps entry
  let val := W (HonestStream.word bits (c/64))
  let w := 1291846156+c/64
  have src : u.getMem (wordAddress w)=val := by
    have a : wordAddress w=W (CheckLayout.proofBase+8*(c/64)) := by unfold w wordAddress CheckLayout.proofBase;congr 1;omega
    rw [a,show u.getMem _=s.getMem _ from congrFun (memory s ptrOps) _]
    exact stream _ (by omega)
  let v := readState u val
  have rv := load o u 665 .x12 .x12 0 w (by dsimp [w];omega) val pc665 ldListed (ptr s c bound cursor) src
  let t := effect v shiftOps
  have q := positive o v 666 shiftOps rfl shiftListed
  have pos : t.pc=addr 667 := location v 666 shiftOps rfl
  have offV : v.getReg .x11=W (c%64) := (readOther u val _ (by decide)).trans ((outside s ptrOps .x11 (by decide)).trans off)
  have v10 : v.getReg .x10=s.getReg .x10 := (readOther u val _ (by decide)).trans (outside s ptrOps _ (by decide))
  have read := masked v c bits (readValue u val) offV
  have br := CheckBranch.event o t 667 57 .ne .x11 .x0 5752 (by decide) pos lastBranch (by decide)
  have dest : (if CheckOrdinary.Cond.test .ne (t.getReg .x11) (t.getReg .x0) then addr 57 else addr 668)=
      (if remainder c bits=0 then addr 668 else addr 57) := by
    change (if t.getReg .x11 != (0:Word) then _ else _)=_;rw [show t.getReg .x11=_ from read]
    by_cases z : remainder c bits=(0:Word)
    · rw [z];rfl
    · rw [bne_iff_ne.mpr z,if_neg z];rfl
  rw [dest] at br
  have f1 : Frame s u := ordinary s ptrOps (by intro r h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> decide)
  have f2 : Frame u v := by
    refine ⟨?_,readMemory u val⟩
    intro r hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl <;> exact readOther u val _ (by decide)
  have f3 : Frame v t := ordinary v shiftOps (by intro r h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> decide)
  refine ⟨_,compose (compose (compose ru rv) q) br,rfl,(MachineState.getReg_setPC ..).trans ((outside v shiftOps .x10 (by decide)).trans v10),?_⟩
  exact framePC _ _ _ (Frame.trans' (Frame.trans' f1 f2) f3)

theorem run (o : Oracle) (s : MachineState) (c bits : Nat) (bound : c≤70000000000)
    (pc : s.pc=addr 657) (cursor : s.getReg .x24=W c) (stream : CheckLayout.StreamMemory s bits) :
    ∃ t n,n≤11 ∧ Segment o n s t [] ∧ t.pc=(if Padded c bits then addr 668 else addr 57) ∧
      t.getReg .x10=s.getReg .x10 ∧ Frame s t := by
  let u := effect s bitOps
  have first := positive o s 657 bitOps pc bitListed
  have at658 : u.pc=addr 658 := location s 657 bitOps pc
  have br := CheckBranch.event o u 658 668 .eq .x11 .x0 40 (by decide) at658 firstBranch (by decide)
  have off : u.getReg .x11=W (c%64) := offset s c bound cursor
  have cond : CheckOrdinary.Cond.test .eq (u.getReg .x11) (u.getReg .x0)=decide (c%64=0) := by
    change (u.getReg .x11 == (0:Word))=_;rw [off]
    by_cases z : c%64=0
    · rw [z];rfl
    · have ne : W (c%64)≠(0:Word) := by
        intro h;have v := congrArg BitVec.toNat h;change (c%64)%2^64=0 at v;omega
      rw [beq_eq_false_iff_ne.mpr ne,decide_eq_false z]
  rw [cond] at br
  have f : Frame s u := ordinary s bitOps (by intro r h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> decide)
  by_cases z : c%64=0
  · rw [decide_eq_true z] at br
    exact ⟨_,2,by decide,compose first br,by simp only [Padded,z,true_or,ite_true];rfl,
      (MachineState.getReg_setPC ..).trans (outside s bitOps .x10 (by decide)),framePC _ _ _ f⟩
  · rw [decide_eq_false z] at br
    let v := u.setPC (addr 659)
    have streamV : CheckLayout.StreamMemory v bits := fun i hi => (f.mem _).trans (stream i hi)
    obtain ⟨t,r,p,x10,frame⟩ := readRun o v c bits bound rfl ((f.regs _ (by decide)).trans cursor) off streamV
    have eq : (Padded c bits) ↔ remainder c bits=0 := by simp [Padded,z]
    exact ⟨t,11,by decide,compose (compose first br) r,by simpa only [eq] using p,x10.trans ((MachineState.getReg_setPC ..).trans (outside s bitOps .x10 (by decide))),
      Frame.trans' (framePC _ _ _ f) frame⟩

end CommitGolfCandidate.Reconstruction.CheckTailPadding
