import CommitGolfCandidate.Layout2ByteLoop
import CommitGolfCandidate.Layout2CopyLoop
import CommitGolfCandidate.Layout2Regions
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 1500000
def callScratch : List Reg := [.x5,.x6,.x7,.x19,.x28,.x29,.x30]

/-- One call copies its source to scratch, gathers every output bit from that snapshot,
and returns through the link register. The tables may duplicate or omit input bits. -/
theorem apply_span {I τ r p tb B} (program : Program I) (cfg : Span τ r p tb B)
    (s : MachineState) (ret : Nat) (here : s.pc=pc 759) (base : s.getReg .x8=addr p)
    (size : s.getReg .x18=addr (B)) (tab : s.getReg .x19=addr tb)
    (scratch : s.getReg .x10=addr scratchBase) (eight : s.getReg .x21=8)
    (link : (s.getReg .x31 &&& ~~~1#64)=pc ret) (table : SpanTable τ r tb B s) :
    ∃ t, Runs I s t (5+106*(B)) (5+106*(B)) ∧ t.pc=pc ret ∧
      (∃ m, Writes s m scratchBase B (fun q=>byte s (p+q)) ∧ Writes m t p B (gather τ r (fun q=>byte s (p+q)))) ∧ Kept callScratch s t := by
  obtain ⟨m,ranCopy,copy⟩:=copy_loop program cfg s here base scratch size
  have memRoom:=cfg.room;have below:=cfg.tableAfter;have sep:=cfg.separated
  have tabM := table.writes cfg copy.wrote (by omega)
  obtain ⟨u,ranBytes,writes⟩:=byte_loop program cfg m (fun q=>byte s (p+q)) (by simpa using copy.next)
    ((copy.kept _ (by decide)).trans base) copy.lim ((copy.kept _ (by decide)).trans tab)
    ((copy.kept _ (by decide)).trans scratch) ((copy.kept _ (by decide)).trans eight) tabM
    (fun q hq=>copy.wrote.atIndex q hq (by omega))
  have last : u.pc=pc 785 := by simpa using writes.next
  obtain ⟨regs,memret,pcR,valid⟩:=effects_ret u last
  have runRet : Runs I u (after .ret u) 1 1 := runBlock program .ret u last (valid.mpr trivial)
  refine ⟨after .ret u,?_,?_,?_,?_⟩
  · have chain:=(ranCopy.thenDo ranBytes).thenDo runRet
    have cost : 3+5*(B)+(1+101*(B))+1=5+106*(B) := by omega
    simpa only [cost] using chain
  · rw [pcR];change (u.getReg .x31 &&& ~~~1#64)=_
    rw [writes.kept _ (by decide),copy.kept _ (by decide),link]
  · exact ⟨m,copy.wrote,writes.wrote.move rfl memret⟩
  · apply (copy.kept.weaken (b:=callScratch) (by intro q h;cases q <;> simp_all [copyScratch,callScratch])).trans
    apply (writes.kept.weaken (b:=callScratch) (by intro q h;cases q <;> simp_all [byteScratch,callScratch])).trans
    apply (kept_of_regs regs).weaken
    intro q h;simpa [clobbers] using h

theorem apply_table {I τ r p tb} (program : Program I) (cfg : Config τ r p tb)
    (s : MachineState) (ret : Nat) (here : s.pc=pc 759) (base : s.getReg .x8=addr p)
    (size : s.getReg .x18=addr (534*r)) (tab : s.getReg .x19=addr tb)
    (scratch : s.getReg .x10=addr scratchBase) (eight : s.getReg .x21=8)
    (link : (s.getReg .x31 &&& ~~~1#64)=pc ret) (table : Table τ r tb s) :
    ∃ t, Runs I s t (5+106*(534*r)) (5+106*(534*r)) ∧ t.pc=pc ret ∧
      Records s t p (534*r) (gather τ r (fun q=>byte s (p+q))) ∧ Kept callScratch s t := by
  obtain ⟨t,ran,land,⟨m,cp,emit⟩,stable⟩ :=
    apply_span program cfg.span s ret here base size tab scratch eight link table.span
  exact ⟨t,ran,land,copied_then_emitted cp (by have:=cfg.small;omega) emit,stable⟩

end CommitGolfCandidate.Layout2
