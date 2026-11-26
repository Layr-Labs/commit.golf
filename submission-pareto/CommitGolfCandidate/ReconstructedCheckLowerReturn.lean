import CommitGolfCandidate.ReconstructedCheckLowerFinish
import CommitGolfCandidate.ReconstructedCheckPairPhysical

namespace CommitGolfCandidate.Reconstruction.CheckLowerReturn
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckValues CheckParentRun CheckPairPhysical CheckParentWords
set_option maxRecDepth 15000
set_option maxHeartbeats 1250000
abbrev W:=BitVec.ofNat 64

def keep : List Reg := [.x1,.x2,.x3,.x4,.x8,.x18,.x19,.x20,.x23,.x24,.x25,.x26,.x27]
private theorem saved : ∀ d : Fin 24,∀ r∈keep,(CheckLowerFinish.done d).get r=(CheckLowerFinish.start d).get r := by decide +kernel

theorem words (s : MachineState) (a : Nat) (aligned : a%8=0) (i : Fin 4) :
    s.getMem (W (a+8*i.val))=digWord (CommitParents.cell s a) i := by
  unfold digWord;change _=((pack (unpack (readBuffer s a 32))).extractLsb' (64*i.val) 64)
  rw [Binding.pack_unpack];exact (read_digest_word s a i aligned i.isLt).symm

/-- Reload the computed digest at the returned stack pointer and select either
another lower edge or the record's cap slot when depth nine has been reached. -/
theorem positive (o : Oracle) (s : MachineState) (a : Nat) (d : Fin 24)
    (pc : s.pc=CommitBlocks.addr 271) (fp : s.getReg .x8=W (a+312)) (depth : s.getReg .x26=W d)
    (align : a%8=0) (room : a+32≤MEMORY_BYTES) :
    ∃ t, Segment o 9 s t [] ∧ t.pc=CommitBlocks.addr (if d.val≤9 then 381 else 280) ∧
      child t CheckPair.current (CommitParents.cell s a) ∧
      (∀ r∈keep,t.getReg r=s.getReg r) ∧ (∀ p,t.getMem p=s.getMem p) ∧
      t.getReg .x9=s.getReg .x9+(-8) ∧ t.getReg .x22=s.getReg .x22+(-8) ∧
      t.getReg .x21=((s.getReg .x21).truncate 32+((-1#64).truncate 32)).signExtend 64 := by
  let e:=CheckRegion.env s a
  have owner : Layout e CheckLowerFinish.table:=CheckRegion.layout s a 32 align (by decide) room
  have init : Matches e (CheckLowerFinish.start d) s:=by
    refine ⟨pc,?_,fun _=>rfl⟩;intro r;cases r <;> try rfl
    · change s.getReg .x8=physical (CheckRegion.env s a) (loc 1 312);rw [CheckRegion.point];exact fp
    · exact depth
  obtain ⟨t,seg,hm,pos,blank,one,two,three,four,_,widthReg,baseReg,iter⟩:=CheckLowerFinish.positive o e owner d s init
  refine ⟨t,seg,hm.pc.trans pos,?_,?_,?_,?_,?_,?_⟩
  · intro i
    have data:=words s a align i
    fin_cases i
    · change t.getReg .x12=_;rw [hm.regs,one];change s.getMem (physical (CheckRegion.env s a) (loc 1 0))=_;rw [CheckRegion.point];exact data
    · change t.getReg .x13=_;rw [hm.regs,two];change s.getMem (physical (CheckRegion.env s a) (loc 1 8))=_;rw [CheckRegion.point];exact data
    · change t.getReg .x14=_;rw [hm.regs,three];change s.getMem (physical (CheckRegion.env s a) (loc 1 16))=_;rw [CheckRegion.point];exact data
    · change t.getReg .x11=_;rw [hm.regs,four];change s.getMem (physical (CheckRegion.env s a) (loc 1 24))=_;rw [CheckRegion.point];exact data
  · intro v hv;rw [hm.regs,saved _ _ hv,←init.regs]
  · intro p;rw [hm.mem,blank];rfl
  · rw [hm.regs,widthReg];rfl
  · rw [hm.regs,baseReg];rfl
  · rw [hm.regs,iter];rfl

end CommitGolfCandidate.Reconstruction.CheckLowerReturn
