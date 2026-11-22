import CommitGolfCandidate.Layout2EffectsCopy
import CommitGolfCandidate.Layout2Touched
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.GroupedOpening.Wide
open TwoPermutationPrototype.GroupedOpening (access_ok)
set_option maxHeartbeats 1500000
def copyScratch : List Reg := [.x5,.x6,.x7,.x28]

structure CopyCursor (B p : Nat) (s m : MachineState) (j : Nat) : Prop where
  next : m.pc=if j=B then pc 767 else pc 762
  src : m.getReg .x5=addr (p+j)
  dst : m.getReg .x6=addr (scratchBase+j)
  lim : m.getReg .x7=addr (p+B)
  wrote : Writes s m scratchBase j (fun i=>byte s (p+i))
  kept : Kept copyScratch s m

theorem copy_loop {I τ r p tb B} (program : Program I) (cfg : Span τ r p tb B)
    (s : MachineState) (here : s.pc=pc 759) (src : s.getReg .x8=addr p)
    (scratch : s.getReg .x10=addr scratchBase) (size : s.getReg .x18=addr (B)) :
    ∃ t, Runs I s t (3+5*(B)) (3+5*(B)) ∧ CopyCursor B p s t (B) := by
  let m0:=after .copyHead s
  obtain ⟨regs,mem,position,access⟩:=effects_copyHead s here
  have startRun : Runs I s m0 3 3 := runBlock program .copyHead s here (access.mpr trivial)
  have init : CopyCursor B p s m0 0 := by
    have pos:=cfg.nonempty
    refine ⟨by simpa [m0,pcOut,show 0≠B by omega] using position,?_,?_,?_,?_,?_⟩
    · rw [regs];simpa [regOut] using src
    · rw [regs];simpa [regOut] using scratch
    · rw [regs];simp [regOut,src,size,addr_add]
    · exact (writes_zero s _ _).move rfl mem
    · apply (kept_of_regs regs).weaken
      intro q h;cases q <;> simp_all [clobbers,copyScratch]
  obtain ⟨t,ran,done⟩:=loop (B) 5 5 (fun j m=>CopyCursor B p s m j) m0 init (by
    intro j inside m h
    have start : m.pc=pc 762 := by simpa [show j≠B by omega] using h.next
    obtain ⟨reg,memM,posM,ready⟩:=effects_copyByte m start
    have sep:=cfg.separated;have later:=cfg.tableAfter;have room:=cfg.room
    have ram : MEMORY_BYTES < 2^64 := by decide
    have valid : Ready m Block.copyByte.ops := by
      apply ready.mpr;change accessValid _ 1=true ∧ accessValid _ 1=true
      rw [h.src,h.dst];exact ⟨access_ok _ 1 (by omega) (by omega),access_ok _ 1 (by omega) (by omega)⟩
    refine ⟨after .copyByte m,runBlock program .copyByte m start valid,?_,?_,?_,?_,?_,?_⟩
    · rw [posM]
      simp only [pcOut,h.src,h.lim,show addr (p+j)+1#64=addr (p+j+1) from addr_add _ _]
      by_cases e : j+1=B
      · simp [Nat.add_assoc,e]
      · have diff : addr (p+j+1)≠addr (p+B) := (addr_ne (by omega) (by omega)).2 (by omega)
        simp [e,diff]
    · rw [reg];simp [regOut,h.src,show addr (p+j)+1#64=addr (p+j+1) from addr_add _ _,Nat.add_assoc]
    · rw [reg];simp [regOut,h.dst,show addr (scratchBase+j)+1#64=addr (scratchBase+j+1) from addr_add _ _,Nat.add_assoc]
    · rw [reg];simpa [regOut] using h.lim
    · have load : byte m (p+j)=byte s (p+j) := h.wrote.outside _ (by omega) (Or.inr (by omega))
      have same : (after .copyByte m).mem=(m.setByte (addr (scratchBase+j)) (byte m (p+j))).mem := by
        simpa [memOut,h.src,h.dst,byte] using memM
      exact (h.wrote.store _ load (by omega)).move rfl same
    · apply h.kept.trans
      apply (kept_of_regs reg).weaken
      intro q hh;cases q <;> simp_all [clobbers,copyScratch])
  exact ⟨t,startRun.thenDo ran,done⟩

end CommitGolfCandidate.Layout2
