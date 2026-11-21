import CommitGolfCandidate.GroupOpenHeaderParts

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

attribute [local irreducible] setupPrefix walkRows keyCopy header

structure HeaderRegisters (s : MachineState) (p : Positions) where
  pc : s.pc=address 740
  r : Registers s 0 p.card
  b : Base s p
  quartet : s.getReg .x4=BitVec.ofNat 64 (2^64-1)
  gp : s.getReg .x3=374
  sp : s.getReg .x2=4352
  mask : s.getReg .x1=4095

theorem header_core (init : MachineState) (p : Positions) (pc : init.pc=address 0) (nr : init.getReg .x16≠0#64)
    (base0 : Base (setupPrefix init 15) p)
    (salt0 : (setupPrefix init 15).getReg .x22=9126809632) (marks0 : (setupPrefix init 15).getReg .x26=4096)
    (shift0 : (setupPrefix init 15).getReg .x25=BitVec.ofNat 64 (8*p.card)) (nz : 0<p.card)
    (mem0 : (setupPrefix init 15).mem=init.mem) (selector0 : init.getReg .x5=0) :
    legal headerRows init ∧ Nonempty (HeaderRegisters (header init) p) ∧ (header init).mem=(keyCopy init).mem := by
  let l:=walkRows init layoutRows
  let c:=walkRows l configRows
  let t:=walkRows c keyRows
  have eq : l=(setupPrefix init 15).setPC (address 725) := layout_sem init pc nr
  have base : Base l p := by rw [eq];exact base_at_pc _ _ _ base0
  have lpc : l.pc=address 725 := by rw [eq];rfl
  have salt : l.getReg .x22=9126809632 := by rw [eq,MachineState.getReg_setPC];exact salt0
  have marks : l.getReg .x26=4096 := by rw [eq,MachineState.getReg_setPC];exact marks0
  have lm : l.mem=init.mem := by rw [eq];exact mem0
  have shiftl : l.getReg .x25=BitVec.ofNat 64 (8*p.card) := by rw [eq,MachineState.getReg_setPC];exact shift0
  have selector : l.getReg .x5=0 := by
    rw [eq,MachineState.getReg_setPC]
    simpa [setupPrefix,setupInstructions,execInstrBr,Opening.getReg_setReg,
      MachineState.getReg_setPC,open_zero,beq_iff_eq,nr] using selector0
  obtain ⟨cp,cm,cb,cr,c10⟩:=config_frame l lpc p base salt marks shiftl nz selector
  have cMem : c.mem=init.mem := cm.trans lm
  obtain ⟨tpc,tm,keep0⟩:=key_frame c p cp cr c10
  let m:=walkRows t markRows
  have quartet : t.getReg .x4=BitVec.ofNat 64 (2^64-1) := by
    rw [keep0 _ (by decide)]
    simp [c,configRows,walkRows,execInstrBr,Opening.getReg_setReg,
      MachineState.getReg_setPC,open_zero]
    all_goals decide
  obtain ⟨mpc,mm,m4,m3,m2,m1,mkeep⟩:=mark_frame t tpc ((keep0 _ (by decide)).trans cr.base) quartet
  have keep (k : Reg) (h31 : k≠.x31) (h4 : k≠.x4 := by decide) (h3 : k≠.x3 := by decide) (h2 : k≠.x2 := by decide)
      (h1 : k≠.x1 := by decide) :
      m.getReg k=c.getReg k := (mkeep k h4 h3 h2 h1).trans (keep0 k h31)
  have mem : m.mem=(keyCopy init).mem := mm.trans (tm.trans (by simp only [keyCopy,MachineState.setMem,MachineState.getMem,cMem]))
  have join (s : MachineState) (xs ys : List Row) : walkRows s (xs++ys)=walkRows (walkRows s xs) ys := by
    simp only [walkRows,List.foldl_append]
  have header_eq : header init=m := by unfold header headerRows;rw [join,join,join]
  refine ⟨?_,?_,header_eq ▸ mem⟩
  · unfold headerRows
    apply legal_append
    · apply legal_append
      · exact legal_append init _ _ (layout_ok init pc nr) (config_ok l lpc)
      · rw [join];exact key_ok c p cp cr c10
    · rw [join,join];exact mark_ok t tpc
  · rw [header_eq]
    exact ⟨⟨mpc,⟨(keep _ (by decide)).trans cr.output,
      (keep _ (by decide)).trans cr.selector,(keep _ (by decide)).trans cr.width,(keep _ (by decide)).trans cr.primitive,
      (keep _ (by decide)).trans cr.index,(keep _ (by decide)).trans cr.endReg,
      (by rw [keep .x25 (by decide) (by decide), cr.shift, keep .x9 (by decide) (by decide)]),
      (keep _ (by decide)).trans cr.salt,
      (keep _ (by decide)).trans cr.base,(keep _ (by decide)).trans cr.divReg⟩,
      ⟨(keep _ (by decide)).trans cb.indices,(keep _ (by decide)).trans cb.heap,(keep _ (by decide)).trans cb.count,
       (keep _ (by decide)).trans cb.leaves,(keep _ (by decide)).trans cb.start,(keep _ (by decide)).trans cb.dest,
       (keep _ (by decide)).trans cb.mark,(keep _ (by decide)).trans cb.slots,
       (keep _ (by decide)).trans cb.capLeaves⟩,m4,m3,m2,m1⟩⟩

end TwoPermutationPrototype.GroupedOpening
