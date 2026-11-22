import CommitGolfCandidate.Layout2Effects
import CommitGolfCandidate.Layout2Regions
import CommitGolfCandidate.Layout2Touched
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Layout2Helpers (access_ok)
def clearScratch : List Reg := [.x5,.x6]
def temps : List Reg := [.x5,.x6,.x7,.x28,.x29,.x30,.x31,.x8,.x9,.x18,.x19,.x20,.x21]
structure ClearCursor (s t : MachineState) (j : Nat) : Prop where
  next : t.pc=if j=267 then pc 745 else pc 742
  dest : t.getReg .x5=addr (scratchBase+8*j)
  stop : t.getReg .x6=addr (scratchBase+2136)
  wrote : Writes s t scratchBase (8*j) (fun _=>0)
  kept : Kept clearScratch s t

theorem clear_loop {I} (program : Program I) (s : MachineState) (here : s.pc=pc 739)
    (scratch : s.getReg .x10=addr scratchBase) :
    ∃ t, Runs I s t 804 804 ∧ ClearCursor s t 267 := by
  let m:=after .clearHead s
  obtain ⟨reg,mem,pos,valid⟩:=effects_clearHead s here
  have head : Runs I s m 3 3 := runBlock program .clearHead s here (valid.mpr trivial)
  have init : ClearCursor s m 0 := by
    refine ⟨pos,?_,?_,(writes_zero s _ _).move rfl mem,?_⟩
    · rw [reg];simpa [regOut] using scratch
    · rw [reg];simp [regOut,scratch,addr,scratchBase]
    · apply (kept_of_regs reg).weaken;intro q h;cases q <;> simp_all [clobbers,clearScratch]
  obtain ⟨t,ran,out⟩:=loop 267 3 3 (fun j u => ClearCursor s u j) m init (by
    intro j inside u h
    have start : u.pc=pc 742 := by simpa [show j≠267 by omega] using h.next
    obtain ⟨regU,memU,pcU,ok⟩:=effects_clearCell u start
    have alg : (scratchBase+8*j)%8=0 := by unfold scratchBase;omega
    have limit : scratchBase+8*j+8≤MEMORY_BYTES := by unfold scratchBase MEMORY_BYTES;omega
    have ready : Ready u Block.clearCell.ops := ok.mpr (by
      change accessValid (u.getReg .x5) 8=true;rw [h.dest];exact access_ok _ _ alg limit)
    refine ⟨after .clearCell u,runBlock program .clearCell u start ready,?_,?_,?_,?_,?_⟩
    · rw [pcU];simp only [pcOut,h.dest,h.stop,show addr (scratchBase+8*j)+8#64=addr (scratchBase+8*j+8) from addr_add _ _]
      by_cases e : j+1=267
      · have last : scratchBase+8*j+8=scratchBase+2136 := by omega
        simp [e,last]
      · have diff : addr (scratchBase+8*j+8)≠addr (scratchBase+2136) :=
          (addr_ne (by unfold scratchBase;omega) (by decide)).2 (by omega)
        simp [e,diff]
    · rw [regU];simp [regOut,h.dest,show addr (scratchBase+8*j)+8#64=addr (scratchBase+8*j+8) from addr_add _ _,Nat.mul_succ,Nat.add_assoc]
    · rw [regU];simpa [regOut] using h.stop
    · have same : (after .clearCell u).mem=(u.setMem (addr (scratchBase+8*j)) 0).mem := by
        simpa [memOut,h.dest] using memU
      simpa only [Nat.mul_succ] using (h.wrote.storeZeroWord alg limit).move rfl same
    · apply h.kept.trans
      apply (kept_of_regs regU).weaken;intro q hh;cases q <;> simp_all [clobbers,clearScratch])
  exact ⟨t,head.thenDo ran,out⟩

theorem restore {I} (program : Program I) (s : MachineState) (here : s.pc=pc 745) :
    ∃ t, Runs I s t 14 14 ∧ t.pc=pc 1 ∧ t.mem=s.mem ∧
      (∀ r, t.getReg r=if r=.x6 then 534 else if r∈temps then 0 else s.getReg r) := by
  obtain ⟨reg,mem,pos,ok⟩:=effects_restore s here
  refine ⟨after .restore s,runBlock program .restore s here (ok.mpr trivial),pos,mem,?_⟩
  intro r;rw [reg];cases r <;> rfl

end CommitGolfCandidate.Layout2
