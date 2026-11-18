import CommitGolfCandidate.GroupOpenHeaderParts

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

attribute [local irreducible] setupPrefix walkRows keyCopy header

structure HeaderRegisters (s : MachineState) (p : Positions) where
  pc : s.pc=address 739
  r : Registers s 0 p.card
  b : Base s p

theorem header_core (init : MachineState) (p : Positions) (pc : init.pc=address 0) (nr : init.getReg .x16≠0#64)
    (base0 : Base (setupPrefix init 15) p)
    (salt0 : (setupPrefix init 15).getReg .x22=6979325984) (marks0 : (setupPrefix init 15).getReg .x26=4096)
    (sel0 : (setupPrefix init 15).getReg .x5=0)
    (mem0 : (setupPrefix init 15).mem=init.mem) :
    legal headerRows init ∧ Nonempty (HeaderRegisters (header init) p) ∧ (header init).mem=(keyCopy init).mem := by
  let l:=walkRows init layoutRows
  let c:=walkRows l configRows
  let t:=walkRows c keyRows
  have eq : l=(setupPrefix init 15).setPC (address 725) := layout_sem init pc nr
  have base : Base l p := by rw [eq];exact base_at_pc _ _ _ base0
  have lpc : l.pc=address 725 := by rw [eq];rfl
  have salt : l.getReg .x22=6979325984 := by rw [eq,MachineState.getReg_setPC];exact salt0
  have marks : l.getReg .x26=4096 := by rw [eq,MachineState.getReg_setPC];exact marks0
  have lm : l.mem=init.mem := by rw [eq];exact mem0
  have sel : l.getReg .x5=0 := by rw [eq,MachineState.getReg_setPC];exact sel0
  obtain ⟨cp,cm,cb,cr⟩:=config_frame l lpc p base salt marks sel
  have cMem : c.mem=init.mem := cm.trans lm
  obtain ⟨tpc,tm,keep⟩:=key_frame c p cp cr
  have mem : t.mem=(keyCopy init).mem := tm.trans (by simp only [keyCopy,MachineState.setMem,MachineState.getMem,cMem])
  have join (s : MachineState) (xs ys : List Row) : walkRows s (xs++ys)=walkRows (walkRows s xs) ys := by
    simp only [walkRows,List.foldl_append]
  have header_eq : header init=t := by unfold header headerRows;rw [join,join]
  refine ⟨?_,?_,header_eq ▸ mem⟩
  · unfold headerRows
    apply legal_append
    · exact legal_append init _ _ (layout_ok init pc nr) (config_ok l lpc)
    · rw [join];exact key_ok c p cp cr
  · rw [header_eq]
    exact ⟨⟨tpc,⟨(keep _ (by decide)).trans cr.input,(keep _ (by decide)).trans cr.output,
      (keep _ (by decide)).trans cr.selector,(keep _ (by decide)).trans cr.width,(keep _ (by decide)).trans cr.primitive,
      (keep _ (by decide)).trans cr.index,(keep _ (by decide)).trans cr.leftReg,(keep _ (by decide)).trans cr.salt,
      (keep _ (by decide)).trans cr.base,(keep _ (by decide)).trans cr.divReg,(keep _ (by decide)).trans cr.mult⟩,
      ⟨(keep _ (by decide)).trans cb.indices,(keep _ (by decide)).trans cb.heap,(keep _ (by decide)).trans cb.count,
       (keep _ (by decide)).trans cb.leaves,(keep _ (by decide)).trans cb.start,(keep _ (by decide)).trans cb.dest,
       (keep _ (by decide)).trans cb.mark,(keep _ (by decide)).trans cb.slots,(keep _ (by decide)).trans cb.cap,
       (keep _ (by decide)).trans cb.capLeaves⟩⟩⟩

end TwoPermutationPrototype.GroupedOpening
