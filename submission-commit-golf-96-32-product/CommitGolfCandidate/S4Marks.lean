import CommitGolfCandidate.S4NormalOpen
import CommitGolfCandidate.S4Stores
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Trapdoor pcAt pc_succ)
open Machine (W Runs Wrote byte proofBase)

def Marked (ps : Positions) (r : Nat) (s : MachineState) :=
  ∀ u<342,byte s (512+u)=if marks ((indices ps).take r) u then 1 else 0

theorem marksNext (ps : Positions) (r u : Nat) (br : r<ps.card) :
    marks ((indices ps).take (r+1)) u=(marks ((indices ps).take r) u || (nodeIndex (recordIndex ps r).val 15==u)) := by
  have b : r<(indices ps).length:=by simpa only [indices,Finset.length_sort] using br
  have i : recordIndex ps r=(indices ps)[r]:=by change (indices ps)[r]?.getD _=_;rw [List.getElem?_eq_getElem b];rfl
  unfold marks;rw [List.take_succ_eq_append_getElem b,i,List.any_append,List.any_cons,List.any_nil,Bool.or_false]

theorem markChanged {ps : Positions} {r : Nat} {s t : MachineState} (br : r<ps.card) (old : Marked ps r s)
    (w : Wrote s t (512+nodeIndex (recordIndex ps r).val 15) 1 (fun _=>1)) : Marked ps (r+1) t := by
  intro u bu;rw [marksNext ps r u br,w _ (by omega)]
  by_cases hit : nodeIndex (recordIndex ps r).val 15=u
  · rw [hit,if_pos (by omega),beq_self_eq_true,Bool.or_true] <;> rfl
  · rw [if_neg (by omega),beq_eq_false_iff_ne.mpr hit,Bool.or_false,old u bu]

theorem untouchedFlags {ps : Positions} {r : Nat} {s t : MachineState} {out n : Nat}
    (old : Marked ps r s) (w : Machine.SameOutside s t out n) (high : proofBase≤out) : Marked ps r t := by
  intro u bu;have low : 512+u<out:=by unfold proofBase at high;omega
  exact (w _ (by omega) (Or.inl low)).trans (old u bu)

theorem initialFlags (td : Trapdoor) (ps : Positions) : Marked ps 0 (initial td ps) := by
  intro u bu;change byte (initial td ps) (512+u)=0
  apply (initial_input_byte Late.submission .opening (td,ps) (512+u) (by omega)).trans
  let b:=fixedBuffer tdBase td;let p:=positionsBuffer Machine.indexBase ps
  have absent (buf : InputBuffer) (lo : 1024≤buf.address) :
      decide (buf.address≤512+u ∧ 512+u<buf.address+buf.length)=false:=decide_eq_false (by omega)
  have inputs : [b,p].find? (fun a=>decide (a.address≤512+u ∧ 512+u<a.address+a.length))=none:=by
    simp only [List.find?_cons,absent b (show 1024≤4294971424 by decide),absent p (show 1024≤7650414624 by decide),List.find?_nil]
  unfold inputByte
  change (match [b,p].find? _ with | some buf=>_ | none=>_)=_
  rw [inputs];exact if_neg (show ¬68719476736≤512+u by omega)

def markPC (l : Nat) := fieldPC true l 17
def markedState (s : MachineState) := execInstrBr (execInstrBr s (.ADD .x6 .x24 .x8)) (.SB .x6 .x25 0)
private theorem markSites : ∀ l : Fin 8,markPC l+2≤16359 ∧
    Machine.stands .opening (markPC l) (.ADD .x6 .x24 .x8) ∧ Machine.stands .opening (markPC l+1) (.SB .x6 .x25 0) := by decide

theorem markRun (l : Fin 8) (i : Index) (s : MachineState) (pc : s.pc=pcAt (markPC l))
    (base : s.getReg .x24=512) (one : s.getReg .x25=1) (slot : s.getReg .x8=W (nodeIndex i.val 15)) :
    let t:=markedState s
    Runs .opening s t 2 2 ∧ t.pc=pcAt (markPC l+2) ∧ (∀ r,Reg.x6≠r → t.getReg r=s.getReg r) ∧
      Wrote s t (512+nodeIndex i.val 15) 1 (fun _=>1) := by
  obtain ⟨bound,add,put⟩:=markSites l
  let u:=execInstrBr s (.ADD .x6 .x24 .x8)
  have m : Runs .opening s u 1 1:=Machine.one (by change markPC l<16359;omega) pc _ (Machine.stood add) rfl
  have ptr : u.getReg .x6+signExtend12 0=W (512+nodeIndex i.val 15):=by
    change (s.getReg .x24+s.getReg .x8)+0=_
    rw [base,slot];exact (BitVec.add_zero _).trans (BitVec.ofNat_add ..).symm
  have next : u.pc=pcAt (markPC l+1):=(congrArg (·+4) pc).trans (pc_succ ..).symm
  have num : nodeIndex i.val 15<342:=indexInside i 15
  obtain ⟨store,endPC,regs,write⟩:=Machine.flagRun (by change markPC l+1<16359;omega) next (Machine.stood put) ptr (by unfold MEMORY_BYTES;omega)
  have keep (r : Reg) (ne : Reg.x6≠r) : u.getReg r=s.getReg r:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne)
  refine ⟨m.trans store,endPC,fun r ne=>(regs r).trans (keep r ne),?_⟩
  have flag : (u.getReg .x25).truncate 8=1:=by rw [keep _ (by decide),one];rfl
  intro q h;change byte (execInstrBr u (.SB .x6 .x25 0)) q=_;rw [write q h,flag]
  rfl
end CommitGolfCandidate.S4.Open
