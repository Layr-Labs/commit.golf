import CommitGolfCandidate.ReconstructedCheckGroupLoop

namespace CommitGolfCandidate.Reconstruction.CheckCapHeaders
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckGroupRadix CheckGroupControl
open CheckGroupWalk CheckGroupPlan CheckGroupFrame CheckGroupPiece
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 14000
set_option maxHeartbeats 1400000

def result (d : Nat) (m : Memory) (ids : List Nat) (stream c : Nat) :=
  if d<8 then (⟨true,c,m⟩ : Result) else decode m ids stream c
def changed := Reg.x29::CheckGroupLoop.changed

/-- The real checker repairs every ordered sibling and rejects a nonzero quotient after the
last allocated digit of any group. All other physical RAM words retain their exact values. -/
theorem run (o : Oracle) (s : MachineState) (ids : List Nat) (d fp proof stream c : Nat)
    (non : ids≠[]) (bounded : ids.length≤512) (depthBound : d≤9) (pc : s.pc=addr 549)
    (depth : s.getReg .x9=W d) (frame : s.getReg .x8=W fp) (fit : 2360≤fp)
    (total : s.getReg .x12=W ids.length) (cursor : s.getReg .x24=W c) (proofReg : s.getReg .x27=W proof)
    (source : 8≤d→Sources s proof stream c ids) (apart : 528384≤proof/8)
    (slots : CheckCapSlots.Contains (memoryView s) (fp-2360) ids)
    (align : (fp-2360)%8=0) (room : fp-2360+4*ids.length≤MEMORY_BYTES) (stack : 528384≤(fp-2360)/8)
    (small : ∀ a∈ids,a<1024) (heap : s.getReg .x23=W cap) (radix : s.getReg .x21=W 211)
    (magicReg : s.getReg .x26=W magic) :
    let out:=result d (memoryView s) ids stream c
    ∃ ticks t,ticks≤5+45*ids.length ∧ Segment o ticks s t [] ∧ t.pc=addr (if out.valid then 598 else 672) ∧
      t.getReg .x24=W out.cursor ∧ t.getReg .x29=W (fp-2360) ∧ LeafMemory.Agrees (memoryView t) out.data ∧ Kept changed s t := by
  dsimp only
  obtain ⟨n,u,nc,enter,atStart,base,initial,ram,keep⟩:=CheckGroupEdge.enter o s d fp pc depth depthBound frame fit
  have same:=view_eq ram
  by_cases early : d<8
  · simp only [result,early,ite_true] at atStart ⊢
    refine ⟨n,u,by omega,enter,atStart,(keep .x24 (by decide)).trans cursor,base,fun w _=>congrFun same w,?_⟩
    intro r h;apply keep
    cases r <;> first | decide | exact False.elim (h (by decide))
  · simp only [result,ite_eq_right early] at atStart ⊢
    have src : Sources u proof stream c ids:=by
      intro i hi
      have ref:=source (by omega) i hi
      exact ⟨ref.1,fun k hk=>(congrFun ram _).trans (ref.2 k hk)⟩
    have acc : Access (memoryView u) (fp-2360) 0 ids := by
      intro i hi;rw [same,Nat.zero_add];exact slots ⟨i,hi⟩
    obtain ⟨m,t,mc,body,done,bits,mem,kt⟩:=CheckGroupLoop.loop o ids u (memoryView s) stream c proof (fp-2360) ids.length 0 non
      (Nat.zero_add _) atStart ((keep .x12 (by decide)).trans total) (initial (by omega)) bounded
      ((keep .x24 (by decide)).trans cursor) ((keep .x27 (by decide)).trans proofReg) base src apart acc align room stack small
      ((keep .x23 (by decide)).trans heap) ((keep .x21 (by decide)).trans radix) ((keep .x26 (by decide)).trans magicReg)
      (fun w _=>congrFun same w)
    refine ⟨_,t,by omega,compose enter body,done,bits,(kt .x29 (by decide)).trans base,mem,?_⟩
    intro r h
    have hf : r∉CheckGroupLoop.changed ∧ r∉[Reg.x13,.x29] := by
      cases r <;> first | decide | exact False.elim (h (by decide))
    exact (kt r hf.1).trans (keep r hf.2)

theorem cursor (d : Nat) (m : Memory) (xs : List Nat) (stream c : Nat)
    (valid : (result d m xs stream c).valid=true) :
    (result d m xs stream c).cursor=c+(if 8≤d then 31*groups xs else 0) := by
  by_cases small : d<8
  · simp [result,small,show ¬8≤d by omega]
  · simp only [result,ite_eq_right small,ite_eq_left (by omega : 8≤d)] at valid ⊢
    exact CheckGroupPlan.cursor _ _ _ _ valid

end CommitGolfCandidate.Reconstruction.CheckCapHeaders

