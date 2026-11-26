import CommitGolfCandidate.S4FlagProbe
import CommitGolfCandidate.S4Dwords

set_option Elab.async false
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
private theorem moveSite : listed .check 4355 (doubleCopies .x1 .x15 0 0 4):=by decide
attribute [local irreducible] copyBlock readBuffer lower
set_option maxRecDepth 5000 in
set_option maxHeartbeats 900000 in
theorem freshRecord (o : Oracle) (x : CheckInput) (s : MachineState) (r : Nat) (v : View)
    (pc : s.pc=pcAt 4353) (env : PendingRow x s r) (seen : Seen o.compression v r s)
    (empty : served o.compression v r (bucket v r)=none) (inside : bucket v r<342)
    (digest : readBuffer s 256 32=lower .packed o.compression v r)
    (flagPtr : s.getReg .x14=W (flagAddr (bucket v r))) (slotPtr : s.getReg .x15=W (capAddr (bucket v r)))
    (fromPtr : s.getReg .x1=W 256) :
    ∃ t,CheckRuns o s t 11 0 ∧ t.pc=pcAt 4380 ∧ PendingRow x t r ∧ Seen o.compression v (r+1) t := by
  let j:=bucket v r;let u:=execInstrBr s (.ADDI .x7 .x0 1)
  have load:=stepAdd .check s 4353 .x7 .x0 1 (by decide) pc (by rfl)
  have same (reg : Reg) (ne : reg≠.x7) : u.getReg reg=s.getReg reg:=keepAdd s .x7 .x0 reg 1 (Ne.symm ne)
  have addr : u.getReg .x14+signExtend12 0=W (flagAddr j):=by rw [same _ (by decide),flagPtr];exact BitVec.add_zero _
  obtain ⟨put,at4355,kept,w⟩:=flagRun (c:=.check) (n:=4354) (r:=.x14) (v:=.x7) (off:=0) (by decide)
    (addPC _ _ _ pc) (by rfl) addr (by unfold flagAddr MEMORY_BYTES;dsimp only [j];omega)
  let t:=execInstrBr u (.SB .x14 .x7 0)
  have bit : Wrote s t (flagAddr j) 1 (fun _=>1):=by
    intro q b;have e:=w q b;change byte t q=_
    have one : (u.getReg .x7).truncate 8=1:=rfl
    rw [one] at e;exact e
  have move:=dwordBlock .check t .x1 .x15 4355 256 (capAddr j) 0 0 4 (by decide) (by decide) at4355 (by decide)
    (matchesListed moveSite) ((kept _).trans ((same _ (by decide)).trans fromPtr)) ((kept _).trans ((same _ (by decide)).trans slotPtr))
    (by decide) (by unfold capAddr;omega) (by decide) (by decide) (by decide)
    (by unfold capAddr MEMORY_BYTES j;omega) (Or.inl (by unfold capAddr;omega))
  let mid:=copyBlock .x1 .x15 0 0 (dwords 4) t
  let z:=mid.setPC (pcAt 4380)
  have branch:=jump .check 4363 4380 mid move.endPC (by decide)
  have save : Moved t z 256 (capAddr j) 32:=move.bytes.congr rfl rfl
  have stored :=changedSlot seen empty inside digest bit save
  have ctrl (reg : Reg) (allowed : caller reg) : z.getReg reg=s.getReg reg:=by
    have h : ∀ reg : Reg,caller reg → reg≠.x6 ∧ reg≠.x7:=by intro reg;cases reg <;> decide
    have a:=h reg allowed
    exact MachineState.getReg_setPC.trans ((move.regs reg (Ne.symm a.1)).trans ((kept reg).trans (same reg a.2)))
  have data : InputsStill x z:=by
    intro q lo hi;exact (save.frame q hi (Or.inr (by unfold capAddr j;omega))).trans
      ((bit.frame q hi (Or.inr (by unfold flagAddr j;omega))).trans (env.data q lo hi))
  exact ⟨z,ofRuns o (((load.trans put).trans move.run).trans branch),rfl,env.transfer ctrl data,stored⟩
end CommitGolfCandidate.S4.Machine
