import CommitGolfCandidate.ReconstructedCapLowAligned
import CommitGolfCandidate.ReconstructedCapLowMerged
import CommitGolfCandidate.ReconstructedCapLowLast

namespace CommitGolfCandidate.Reconstruction.CapEmit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor OpeningPut CapLowCore
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

def encode (m : Model) (c w : Nat) := put (lowThree m c) (c+192) w (top m)

structure Result (m t : Model) (c w : Nat) : Prop where
  memory : t.mem=encode m c w
  cursor : t.reg .x7=W (c+192+w)
  advance : t.reg .x24=m.reg .x24+4
  keep : ∀ r∈fixed, r≠.x24 → t.reg r=m.reg r

theorem merge (m : Model) (c w : Nat) (t : Model) (q : Prepared m t c)
    (small : w≤64) (zero : t.reg .x0=0) (width : m.reg .x23=W w) :
    Result m (CapLowLast.result t (c+192) w) c w := by
  have offset : t.reg .x26=W ((c+192)%64) := by rw [show (c+192)%64=c%64 by omega];exact q.offset
  have first : t.reg .x14=first t.mem (c+192) (t.reg .x30) := q.regTop ▸ q.firstWord
  obtain ⟨cursor,advance,frame⟩ := CapLowLast.registers t (c+192) w q.cursor ((q.keep _ (by decide)).trans width)
  refine ⟨?_,cursor,?_,?_⟩
  · rw [CapLowLast.memory _ _ _ small zero offset first,q.memory,q.regTop];rfl
  · exact advance.trans (congrArg (·+4) (q.keep _ (by decide)))
  · intro r mem ne
    have a : r≠.x12 := fun h => by subst r;exact (by decide : Reg.x12 ∉ fixed) mem
    have b : r≠.x7 := fun h => by subst r;exact (by decide : Reg.x7 ∉ fixed) mem
    exact (frame r a b ne).trans (q.keep r mem)

theorem one (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 1521) (fit : Fits s m) (c w : Nat)
    (small : w≤64) (room : (c+192)/64<capacity) (cursor : m.reg .x7=W c) (width : m.reg .x23=W w)
    (baseReg : m.reg .x17=wordAddress base) (thresh : m.reg .x28=65) :
    ∃ (n : Nat) (t : MachineState) (out : Model), n≤50 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧
      t.pc=addr 1511 ∧ Fits t out ∧ Result m out c w := by
  let a := after m CapLowStart.ops
  have cap : c<2^64 := by unfold capacity at room;omega
  have pre := arrive m c cap cursor baseReg
  obtain ⟨u,seg,loc,f⟩ := CapLowStart.run o m s pc fit c cap cursor baseReg
  have core : ∃ (n : Nat) (v : MachineState) (b : Model), n≤34 ∧ CommitExact.Segment o OpeningStraight.image n u v ∧
      v.pc=addr 1574 ∧ Fits v b ∧ Prepared a b c := by
    by_cases align : c%64=0
    · rw [ite_eq_left align] at loc
      obtain ⟨v,g,locV,fV,h⟩ := CapLowAligned.run o a c room pre align u loc f
      exact ⟨12,v,_,by decide,g,locV,fV,h⟩
    · rw [ite_eq_right align] at loc
      have zeroA : a.reg .x0=0 := (f.registers _).symm.trans rfl
      obtain ⟨v,g,locV,fV,h⟩ := CapLowMerged.run o a c room pre align zeroA u loc f
      exact ⟨34,v,_,by decide,g,locV,fV,h⟩
  obtain ⟨steps,v,b,stepBound,span,here,fb,h⟩ := core
  have rest : b.reg .x26=W ((c+192)%64) := by rw [show (c+192)%64=c%64 by omega];exact h.offset
  have wA : a.reg .x23=W w := width
  have wB := (h.keep .x23 (by decide)).trans wA
  have tB : b.reg .x28=65 := (h.keep _ (by decide)).trans (show a.reg .x28=65 from thresh)
  obtain ⟨k,t,kBound,endRun,endPC,endFit⟩ := CapLowLast.run o b v here fb (c+192) w small (CapLowCore.room c room 192 (by decide))
    rest wB h.topAddr tB
  have framed := merge a c w b h small ((fb.registers _).symm.trans rfl) wA
  refine ⟨7+steps+k,t,_,by omega,CommitExact.compose (CommitExact.compose seg span) endRun,endPC,endFit,?_,framed.cursor,?_,?_⟩
  · exact framed.memory
  · exact framed.advance
  · intro r mem ne
    exact (framed.keep r mem ne).trans (sameReg m CapLowStart.ops r (by
      simp only [fixed,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl))

end CommitGolfCandidate.Reconstruction.CapEmit
