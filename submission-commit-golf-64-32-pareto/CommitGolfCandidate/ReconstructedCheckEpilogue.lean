import CommitGolfCandidate.ReconstructedCheckDecode
import CommitGolfCandidate.ReconstructedCheckMemoryOps
import CommitGolfCandidate.ReconstructedCheckRegion

namespace CommitGolfCandidate.Reconstruction.CheckEpilogue
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding.Machine CheckValues CheckRecorded CheckParentRun CommitBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000

def code : List CheckLink.Op := [
  .plain (.basic (.arith (.addi .x2 .x2 400))),.plain (.basic (.ld .x1 .x2 2024)),
  .plain (.basic (.ld .x8 .x2 2016)),.plain (.basic (.ld .x9 .x2 2008)),.plain (.basic (.ld .x18 .x2 2000)),
  .plain (.basic (.ld .x19 .x2 1992)),.plain (.basic (.ld .x20 .x2 1984)),.plain (.basic (.ld .x21 .x2 1976)),
  .plain (.basic (.ld .x22 .x2 1968)),.plain (.basic (.ld .x23 .x2 1960)),.plain (.basic (.ld .x24 .x2 1952)),
  .plain (.basic (.ld .x25 .x2 1944)),.plain (.basic (.ld .x26 .x2 1936)),.plain (.basic (.ld .x27 .x2 1928)),
  .plain (.basic (.arith (.addi .x2 .x2 2032)))]

def start : State where
  pc:=addr 57
  regs:=fun r=>if r=.x2 then ptr 1 0 else .reg r
  writes:=[]

def run:=CheckLink.run (CheckRegion.tab 2432) (addr 57) code start
def done:=run.getD start
private theorem checked : run.isSome=true ∧ done.pc=addr 72 ∧ done.get .x1=.old (loc 1 2424) ∧ done.get .x10=.reg .x10 ∧ done.writes=[] := by decide +kernel

theorem positive (o : Oracle) (s : MachineState) (frame : Nat) (align : frame%8=0) (room : frame+2432≤MEMORY_BYTES)
    (pc : s.pc=addr 57) (sp : s.getReg .x2=BitVec.ofNat 64 frame) (ret : s.getMem (BitVec.ofNat 64 (frame+2424))=addr 20) :
    ∃ t, Segment o 16 s t [] ∧ t.pc=addr 20 ∧ t.getReg .x10=s.getReg .x10 ∧ ∀ p,t.getMem p=s.getMem p := by
  let e:=CheckRegion.env s frame
  have layout:=CheckRegion.layout s frame 2432 align (by decide) room
  have init : Matches e start s:=by
    refine ⟨pc,?_,fun _=>rfl⟩;intro reg;cases reg <;> try rfl
    change s.getReg .x2=physical (CheckRegion.env s frame) (loc 1 0);rw [CheckRegion.point,Nat.add_zero];exact sp
  obtain ⟨existsRun,locPC,ra,val,blank⟩:=checked
  have replay : run=some done:=by unfold done;cases h:run <;> simp_all
  obtain ⟨u,seg,hm,_⟩:=CheckLink.run_sound o e (CheckRegion.tab 2432) layout code (addr 57) start done s init
    (fun _ h=>by cases h) (CheckDecode.sound _ _ (by decide)) replay
  have rg : u.getReg .x1=addr 20:=by
    rw [hm.regs,ra];change s.getMem (physical (CheckRegion.env s frame) (loc 1 2424))=_;rw [CheckRegion.point];exact ret
  have j : Segment o 1 u (u.setPC (addr 20)) []:=by
    apply plain _ _ _ _ (CheckMemoryOps.parsed (n:=72) (ins:=.base (.JALR .x0 .x1 0)) (by decide) u (hm.pc.trans locPC))
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,execInstrBr,rg]
    rfl
  refine ⟨_,by simpa only [List.nil_append,show code.length=15 by decide] using compose seg j,rfl,?_,?_⟩
  · change u.getReg .x10=_;rw [hm.regs,val];rfl
  · intro p;change u.getMem p=_;rw [hm.mem,blank];rfl

end CommitGolfCandidate.Reconstruction.CheckEpilogue
