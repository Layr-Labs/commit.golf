import CommitGolfCandidate.ReconstructedCheckRecordAccess
import CommitGolfCandidate.ReconstructedCheckRecordFrame

namespace CommitGolfCandidate.Reconstruction.CheckRecordWrite
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckLayout CheckRecorded CheckRecordAccess LeafModel OpeningOps
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 15000
set_option maxHeartbeats 1400000
abbrev W:=BitVec.ofNat 64

def wordWindow (old : Memory) (k : Nat) (xs : Fin 4→Word) :=
  writeWord (writeWord (writeWord (writeWord old (capWord k 0) (xs 0)) (capWord k 1) (xs 1)) (capWord k 2) (xs 2)) (capWord k 3) (xs 3)

theorem windowRead (old : Memory) (k : Nat) (xs : Fin 4→Word) (j : Fin 4) : wordWindow old k xs (capWord k j)=xs j := by
  fin_cases j <;> simp [wordWindow,writeWord,capWord]

theorem windowFrame (old : Memory) (k : Nat) (xs : Fin 4→Word) (a : Nat) (safe : a<capWord k 0 ∨ capWord k 0+4≤a) :
    wordWindow old k xs a=old a := by
  have sep (j : Nat) (h : j<4) : a≠capWord k j:=by unfold capWord at *;omega
  simp only [wordWindow,writeWord,ite_eq_right (sep 3 (by decide)),ite_eq_right (sep 2 (by decide)),ite_eq_right (sep 1 (by decide)),ite_eq_right (sep 0 (by decide))]

def code (k : Nat) : List Op := [.reg .x10 (.lui 1024),.reg .x23 (.add .x23 .x10),.sd .x23 .x12 0 (capWord k 0),
  .sd .x23 .x13 8 (capWord k 1),.sd .x23 .x14 16 (capWord k 2),.reg .x10 (.lui 1),.reg .x10 (.sub .x8 .x10),
  .ld .x17 .x10 1720 8589934169,.reg .x17 (.addi .x17 1),.sd .x23 .x11 24 (capWord k 3)]

def first : List Op:=[.reg .x10 (.addi .x0 1)]
def preserved : List Reg := [.x2,.x8,.x5,.x6,.x7,.x19,.x24]

private theorem slot (k j : Nat) : W (32*k)+4194304#64+W (8*j)=wordAddress (capWord k j) := by
  change W (32*k)+W 4194304+W (8*j)=W (8*(524288+4*k+j));rw [←BitVec.ofNat_add,←BitVec.ofNat_add];congr 1;omega

def memory (s : MachineState) (k : Nat) := wordWindow (memoryView (s.setByte (flag k) 1)) k (fun j=>s.getReg (CheckPair.current j))

structure After (s t : MachineState) (k ord count : Nat) : Prop where
  pc : t.pc=(if ord+1=count then CommitBlocks.addr 409 else CommitBlocks.addr 122)
  next : t.getReg .x17=W (ord+1)
  keep : ∀ r∈preserved,t.getReg r=s.getReg r
  words : ∀ w,w<2^33→t.getMem (wordAddress w)=memory s k w

private theorem checked (m : Model) (k : Nat) (small : k<1024) (x : m.reg .x23=W (32*k)) (fp : m.reg .x8=W CheckLayout.fp) : Checked m (code k) := by
  simp only [code,Checked,Op.Valid,Op.apply,true_and,and_true]
  have bound (j : Fin 4) : capWord k j<2^33:=by have:=j.isLt;unfold capWord;omega
  refine ⟨⟨bound 0,?_⟩,⟨bound 1,?_⟩,⟨bound 2,?_⟩,⟨by decide,?_⟩,bound 3,?_⟩
  · change m.reg .x23+4194304#64+0#64=_;rw [x];exact slot k 0
  · change m.reg .x23+4194304#64+8#64=_;rw [x];exact slot k 1
  · change m.reg .x23+4194304#64+16#64=_;rw [x];exact slot k 2
  · change m.reg .x8-4096#64+1720#64=_;rw [fp];decide
  · change m.reg .x23+4194304#64+24#64=_;rw [x];exact slot k 3

private theorem listing (k : Nat) : CheckStraight.Listed 111 ((code k).map Op.instr) := by
  apply CheckRecordOps.image
  exact (by decide : CheckRecordOps.listed 111 (code 0)=true)

theorem positive (o : Oracle) (s : MachineState) (k ord count : Nat) (slotRoom : k<1024) (ordRoom : ord<2^24) (countRoom : count≤2^24)
    (pc : s.pc=CommitBlocks.addr 109) (flagAddr : s.getReg .x15=flag k) (shift : s.getReg .x23=W (32*k))
    (fp : s.getReg .x8=W CheckLayout.fp) (loaded : s.getReg .x5=W count) (ordVal : s.getMem (W (CheckLayout.fp-2376))=W ord) :
    ∃ t,Segment o 13 s t [] ∧ After s t k ord count := by
  let m:=CheckRecordHeader.model s
  obtain ⟨u,a,loc,f⟩:=CheckStraight.block o m first 109 (by decide) (CheckRecordOps.image _ _ (by decide))
    (by simp [first,Checked,Op.Valid]) s pc (CheckRecordHeader.fits s)
  have up : u.getReg .x15=flag k:=(f.registers _).trans flagAddr
  have write:=CheckMemoryOps.storeB o u 110 .x15 .x10 (flag k) 1 (by decide) loc up (by rw [f.registers];rfl) (validFlag k slotRoom)
  let v:=(u.setByte (flag k) 1).setPC (CommitBlocks.addr 111)
  have vr (r : Reg) (hr : r≠.x10) : v.getReg r=s.getReg r := by
    change u.getReg r=s.getReg r
    apply CheckRecordOps.physical first f (CheckRecordHeader.fits s) r
    simpa [first,CheckRecordOps.dest] using hr
  have pre : ∀ w,w<2^33→v.getMem (wordAddress w)=(s.setByte (flag k) 1).getMem (wordAddress w) := by
    intro w bound
    change (u.setByte _ _).getMem _=_
    unfold MachineState.setByte MachineState.getMem MachineState.setMem
    change (if _ then _ else _)=(if _ then _ else _)
    split <;> rename_i hit
    · congr 1;change u.getMem (alignToDword (flag k))=s.getMem (alignToDword (flag k))
      unfold flag;rw [OpeningCursor.aligned];exact f.memory ((4259840+k)/8) (by omega)
    · exact f.memory _ bound
  obtain ⟨z,b,pos,fz⟩:=CheckStraight.block o (CheckRecordHeader.model v) (code k) 111 (by change 111+10≤796;decide) (listing k)
    (checked _ k slotRoom ((vr .x23 (by decide)).trans shift) ((vr .x8 (by decide)).trans fp)) v rfl (CheckRecordHeader.fits v)
  have ordV : v.getMem (wordAddress 8589934169)=W ord:=by
    rw [pre _ (by decide)]
    exact (MachineState.getMem_setMem_ne (by
      intro e;change wordAddress 8589934169=alignToDword (W (4259840+k)) at e;rw [OpeningCursor.aligned] at e
      have n:=congrArg BitVec.toNat e;change (8*8589934169)%2^64=(8*((4259840+k)/8))%2^64 at n;omega)).trans ordVal
  have next : z.getReg .x17=W (ord+1):=by
    rw [fz.registers];change (writeWord (writeWord (writeWord (memoryView v) (capWord k 0) _) (capWord k 1) _) (capWord k 2) _ 8589934169)+1#64=_
    have sep (j : Nat) (hh : j<4) : 8589934169≠capWord k j:=by unfold capWord;omega
    rw [writeWord,ite_eq_right (sep 2 (by decide)),writeWord,ite_eq_right (sep 1 (by decide)),writeWord,ite_eq_right (sep 0 (by decide))]
    change v.getMem (wordAddress 8589934169)+1#64=_;rw [ordV];exact (BitVec.ofNat_add (n:=64) ord 1).symm
  have save (r : Reg) (hr : r∈preserved) : z.getReg r=s.getReg r:=by
    have table : ∀ q : Reg,q∈preserved→q∉(code k).flatMap CheckRecordOps.dest ∧ q≠.x10:=by exact (by decide : ∀ q : Reg,q∈preserved→q∉(code 0).flatMap CheckRecordOps.dest ∧ q≠.x10)
    exact (CheckRecordOps.physical (code k) fz (CheckRecordHeader.fits v) r (table r hr).1).trans (vr r (table r hr).2)
  have branch:=CheckBranch.event o z 121 409 .eq .x17 .x5 1152 (by decide) pos (CheckDecode.same_sound (by decide)) (by decide)
  refine ⟨z.setPC (if CheckOrdinary.Cond.test .eq (z.getReg .x17) (z.getReg .x5) then CommitBlocks.addr 409 else CommitBlocks.addr 122),by simpa only [List.nil_append,show first.length=1 by decide,show (code k).length=10 by rfl] using compose (compose (compose a write) b) branch,?_,next,save,?_⟩
  · change (if CheckOrdinary.Cond.test .eq (z.getReg .x17) (z.getReg .x5) then _ else _)=_;rw [next,save .x5 (by decide),loaded]
    have eq : W (ord+1)=W count ↔ ord+1=count:=by
      refine ⟨fun h=>?_,congrArg W⟩;have n:=congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at n;omega
    simp only [CheckOrdinary.Cond.test,beq_iff_eq,eq]
  · intro w small;change z.getMem (wordAddress w)=_;apply (fz.memory w small).trans
    change wordWindow (memoryView v) k (fun j=>v.getReg (CheckPair.current j)) w=_
    have vals : (fun j=>v.getReg (CheckPair.current j))=(fun j=>s.getReg (CheckPair.current j)):=by funext j;exact vr _ ((by decide : ∀ l : Fin 4,CheckPair.current l ≠ .x10) j)
    rw [vals];unfold memory wordWindow writeWord
    split_ifs <;> first | rfl | exact pre w small

end CommitGolfCandidate.Reconstruction.CheckRecordWrite
