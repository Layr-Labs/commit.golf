import CommitGolfCandidate.ReconstructedCheckCapScanMissing
import CommitGolfCandidate.ReconstructedCheckCapScanAdvance
import CommitGolfCandidate.ReconstructedCheckCapScanData

namespace CommitGolfCandidate.Reconstruction.CheckCapScanPair
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks
open CheckCapScanData (W scratch flag scanned)
open HonestFlagState (code)
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000

structure Before (s : MachineState) (k p hi dst : Nat) (l r : Bool) : Prop where
  pc : s.pc=addr 447
  lo : s.getReg .x14=flag k
  hiPtr : s.getReg .x13=flag (k+1)
  parent : s.getReg .x15=flag dst
  index : s.getReg .x16=W k
  pending : s.getReg .x12=W p
  endIdx : s.getReg .x20=W hi
  scratchPtr : s.getReg .x29=W scratch
  unit : s.getReg .x18=1
  lval : s.getByte (flag k)=code l
  rval : s.getByte (flag (k+1))=code r

def changed : List Reg := [.x17,.x5,.x6,.x12,.x16,.x13,.x14,.x15]

structure After (s t : MachineState) (k p hi dst : Nat) (l r : Bool) : Prop where
  pc : t.pc=addr (CheckCapScanAdvance.dest k hi)
  lo : t.getReg .x14=flag (k+2)
  hiPtr : t.getReg .x13=flag (k+2+1)
  parent : t.getReg .x15=flag (dst+1)
  index : t.getReg .x16=W (k+2)
  pending : t.getReg .x12=W (p+(l != r).toNat)
  mem : t.mem=(scanned s (flag dst) p k l r).mem
  keep : ∀ q∉changed,t.getReg q=s.getReg q

private theorem flag_add (a n : Nat) : flag a+W n=flag (a+n) := by
  unfold flag;rw [←BitVec.ofNat_add,Nat.add_assoc]

theorem run (o : Oracle) (s : MachineState) (k p hi dst : Nat) (l r : Bool) (input : Before s k p hi dst l r)
    (wk : k+1<1024) (wp : p≤256) (wh : hi≤1024) (wd : dst<1024) :
    ∃ n≤18,∃ t, Segment o n s t [] ∧ After s t k p hi dst l r := by
  let b:=flag dst
  let t:=(CheckCapScanFlags.marked s l r b).setPC (addr 452)
  have before:=CheckCapScanFlags.positive o s l r input.pc (input.lo ▸ input.lval) (input.hiPtr ▸ input.rval)
    (input.lo ▸ CheckCapScanData.flag_valid _ (by omega)) (input.hiPtr ▸ CheckCapScanData.flag_valid _ wk)
    b input.parent (CheckCapScanData.flag_valid _ wd) input.unit
  have tr (q : Reg) (fresh : q∉[Reg.x17,.x5,.x6]) : t.getReg q=s.getReg q := CheckCapScanFlags.keep _ _ _ _ q fresh
  have tl : t.getReg .x17=W l.toNat := (CheckCapScanFlags.registers s l r b .x17).trans rfl
  have th : t.getReg .x5=W r.toNat := (CheckCapScanFlags.registers s l r b .x5).trans rfl
  let pp : Fin 257:=⟨p,by omega⟩
  let kk : Fin 1024:=⟨k,by omega⟩
  let u:=CheckCapScanMissing.result t scratch p k l r
  have missing:=CheckCapScanMissing.positive o t scratch k pp l r rfl tl th ((tr _ (by decide)).trans input.index)
    ((tr _ (by decide)).trans input.pending) ((tr _ (by decide)).trans input.scratchPtr) (by decide)
    (by change 68719473368+4*p+4≤68719476736;omega)
  have ur (q : Reg) (fresh : q∉[Reg.x17,.x5,.x12]) : u.getReg q=t.getReg q := CheckCapScanMissing.keep t scratch p k l r q fresh
  have atU : u.pc=addr 442 := by unfold u CheckCapScanMissing.result;split <;> rfl
  have uk : u.getReg .x16=W k := (ur _ (by decide)).trans ((tr _ (by decide)).trans input.index)
  have uh : u.getReg .x20=W hi := (ur _ (by decide)).trans ((tr _ (by decide)).trans input.endIdx)
  have advanced:=CheckCapScanAdvance.positive o u kk hi (by omega) atU uk uh
  obtain ⟨pc,mem,index,high,low,parent,carry⟩:=CheckCapScanAdvance.state u kk hi uk
  refine ⟨_,?_,_,compose (compose before missing) advanced,pc,?_,?_,?_,index,?_,?_,?_⟩
  · cases l <;> cases r <;> decide
  · rw [low,ur _ (by decide),tr _ (by decide),input.lo];exact flag_add ..
  · rw [high,ur _ (by decide),tr _ (by decide),input.hiPtr]
    change W (CheckCapScanData.active+(k+1))+W 2=W (CheckCapScanData.active+(k+2+1))
    rw [←BitVec.ofNat_add];congr 1
  · rw [parent,ur _ (by decide),tr _ (by decide),input.parent];exact flag_add ..
  · exact (carry .x12 (by decide)).trans (CheckCapScanMissing.count t scratch k pp l r ((tr _ (by decide)).trans input.pending))
  · rw [mem,CheckCapScanMissing.memory]
    have source : t.mem=(CapScanMemory.marked s b (l||r)).mem := CheckCapScanFlags.memory s l r b
    unfold scanned
    split
    · exact source
    · exact CapScanMemory.word_congr source _ _
  · intro q hn
    simp only [changed,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    exact (carry q (by simp_all)).trans ((ur q (by simp_all)).trans (tr q (by simp_all)))

end CommitGolfCandidate.Reconstruction.CheckCapScanPair
