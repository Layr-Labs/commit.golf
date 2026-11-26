import CommitGolfCandidate.ReconstructedCheckGroupFrame
import CommitGolfCandidate.ReconstructedCheckGroupEdge

namespace CommitGolfCandidate.Reconstruction.CheckGroupLoop
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckGroupRadix CheckGroupControl CheckGroupWalk
open CheckGroupPlan CheckGroupFrame CheckGroupPiece
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 14000
set_option maxHeartbeats 1750000

def changed := Reg.x13::scratch

theorem loop (o : Oracle) (xs : List Nat) (s : MachineState) (m : Memory) (stream c proof base n j : Nat)
    (non : xs≠[]) (joint : j+xs.length=n) (pc : s.pc=addr 554)
    (total : s.getReg .x12=W n) (ord : s.getReg .x13=W j) (small : n≤512)
    (cur : s.getReg .x24=W c) (sourceReg : s.getReg .x27=W proof) (stackReg : s.getReg .x29=W base)
    (source : Sources s proof stream c xs) (sep : 528384≤proof/8)
    (ids : Access (memoryView s) base j xs) (aligned : base%8=0) (room : base+4*n≤MEMORY_BYTES)
    (stack : 528384≤base/8) (validIds : ∀ a∈xs,a<1024) (heap : s.getReg .x23=W cap)
    (radix : s.getReg .x21=W 211) (magicReg : s.getReg .x26=W magic) (mem : LeafMemory.Agrees (memoryView s) m) :
    ∃ ticks t,ticks≤45*xs.length ∧ Segment o ticks s t [] ∧
      t.pc=addr (if (decode m xs stream c).valid then 598 else 672) ∧
      t.getReg .x24=W (decode m xs stream c).cursor ∧ LeafMemory.Agrees (memoryView t) (decode m xs stream c).data ∧
      Kept changed s t := by
  let ys:=xs.take 4
  let tail:=xs.drop 4
  let v:=value stream c
  let after:=patch m ys v
  have pos:=List.length_pos_iff.mpr non
  have len : ys.length=min (n-j) 4 := by dsimp [ys];rw [List.length_take,Nat.min_comm];congr 1;omega
  have positive : 0<ys.length:=by omega
  have rem : tail.length=xs.length-4:=List.length_drop
  have src:=source 0 (by unfold groups;omega)
  simp only [Nat.mul_zero,Nat.add_zero] at src
  obtain ⟨a,u,ac,first,arrived,cs,ramA,keepA⟩:=CheckGroupPiece.run o s ys stream c proof base n j
    (List.length_pos_iff.mp positive) len pc total ord (by omega) small cur sourceReg stackReg src.1 src.2
    (takeAccess _ _ _ _ ids) aligned (by omega) stack (fun a ha=>validIds a (List.mem_of_mem_take ha)) heap radix magicReg
  have am : LeafMemory.Agrees (memoryView u) after:=fun i hi=>(ramA i hi).trans (congruence _ _ ys v mem i hi)
  have plan:=cons m xs stream c non
  change decode m xs stream c=(if (CapDigits.extract ys.length v).2=0 then decode after tail stream (c+31) else ⟨false,c+31,after⟩) at plan
  by_cases good : (CapDigits.extract ys.length v).2=0
  · rw [ite_eq_left good] at plan arrived
    have cnt:= (keepA .x12 (by decide)).trans total
    have jreg:= (keepA .x13 (by decide)).trans ord
    obtain ⟨b,t,bc,advance,atEnd,newJ,m2,keepB⟩:=CheckGroupEdge.advance o u n j arrived cnt jreg small (by omega)
    have sofar:=compose first advance
    have stable : Kept changed s t := by
      intro r h
      have hf : r≠.x13 ∧ r∉scratch := by simpa only [changed,List.mem_cons,not_or] using h
      exact (keepB r (by simpa using hf.1)).trans (keepA r hf.2)
    have newC := (keepB .x24 (by decide)).trans cs
    have stm := view_eq m2
    have effect : LeafMemory.Agrees (memoryView t) (patch (memoryView s) ys v):=stm ▸ ramA
    have atMem : LeafMemory.Agrees (memoryView t) after:=stm ▸ am
    by_cases more : j+4<n
    · rw [ite_eq_left more] at atEnd
      have tailpos : tail≠[]:=List.length_pos_iff.mp (by omega)
      obtain ⟨k,z,kc,body,halted,cursor,actual,keep⟩:=loop o tail t after stream (c+31) proof base n (j+4)
        tailpos (by omega) atEnd ((stable .x12 (by decide)).trans total) newJ small newC
        ((stable .x27 (by decide)).trans sourceReg) ((stable .x29 (by decide)).trans stackReg)
        (sources s t xs proof stream c v non source sep validIds effect) sep
        (dropAccess s t xs j base v ids (by omega) stack validIds effect) aligned room stack
        (fun a ha=>validIds a (List.mem_of_mem_drop ha)) ((stable .x23 (by decide)).trans heap)
        ((stable .x21 (by decide)).trans radix) ((stable .x26 (by decide)).trans magicReg) atMem
      rw [plan]
      exact ⟨_,z,by omega,compose sofar body,halted,cursor,actual,fun r h=>(keep r h).trans (stable r h)⟩
    · have te : tail=[]:=List.length_eq_zero_iff.mp (by omega)
      rw [ite_eq_right more] at atEnd
      rw [plan,te,nil]
      exact ⟨_,t,by omega,sofar,atEnd,newC,atMem,stable⟩
  · rw [ite_eq_right good] at arrived plan
    rw [plan]
    refine ⟨a,u,by omega,first,arrived,cs,am,?_⟩
    intro r h
    exact keepA r (fun hr=>h (List.mem_cons_of_mem _ hr))
termination_by xs.length
decreasing_by simp only [List.length_drop];omega

end CommitGolfCandidate.Reconstruction.CheckGroupLoop

