import CommitGolfCandidate.ReconstructedCheckGroupControl

namespace CommitGolfCandidate.Reconstruction.CheckGroupEdge
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapArith CheckGroupRadix CheckGroupControl
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def pivot : List Line := [(.x13,.op (.addi .x0 8))]
def setBase : List Line := [(.x29,.op (.addi .x8 2048)),(.x29,.op (.addi .x29 3784))]
def paid : List Line := (.x13,.op (.addi .x0 0))::setBase

private theorem scratch (fp : Nat) (bound : 2360≤fp) : W fp+signExtend12 2048+signExtend12 3784 = W (fp-2360) := by
  have h : W fp=W (fp-2360)+W 2360 := by rw [←BitVec.ofNat_add];congr 1;omega
  rw [h,BitVec.add_assoc,BitVec.add_assoc,show W 2360+(signExtend12 2048+signExtend12 3784)=0#64 by decide,BitVec.add_zero]

theorem enter (o : Oracle) (s : MachineState) (d fp : Nat) (pc : s.pc=addr 549) (depth : s.getReg .x9=W d)
    (bounded : d≤9) (frame : s.getReg .x8=W fp) (fit : 2360≤fp) :
    ∃ n t,n≤5 ∧ Segment o n s t [] ∧ t.pc=addr (if d<8 then 598 else 554) ∧
      t.getReg .x29=W (fp-2360) ∧ (8≤d→t.getReg .x13=0) ∧ t.mem=s.mem ∧ Kept [.x13,.x29] s t := by
  let u:=effect s pivot
  have a:=CheckCapArith.positive o s 549 pivot pc (by decide)
  have test:=less o u 550 596 .x9 .x13 d 8 184 (by decide) (location s 549 pivot pc) rfl (by decide)
    ((outside s pivot .x9 (by decide)).trans depth) (by rw [register];rfl) (by omega) (by decide)
  by_cases early : d<8
  · rw [ite_eq_left early] at test
    let v:=u.setPC (addr 596)
    let t:=effect v setBase
    have z:=CheckCapArith.positive o v 596 setBase rfl (by decide)
    refine ⟨4,t,by decide,compose (compose a test) z,?_,?_,by omega,?_,?_⟩
    · rw [ite_eq_left early];exact location v 596 setBase rfl
    · rw [register];change u.getReg .x8+signExtend12 2048+signExtend12 3784=_
      rw [outside s pivot .x8 (by decide),frame,scratch _ fit]
    · exact (memory v setBase).trans (memory s pivot)
    · intro r h
      have pair : r≠.x13 ∧ r≠.x29:=by simpa using h
      exact (outside v setBase r (by simpa [setBase] using pair.2)).trans (outside s pivot r (by simpa [pivot] using pair.1))
  · rw [ite_eq_right early] at test
    let v:=u.setPC (addr 551)
    let t:=effect v paid
    have z:=CheckCapArith.positive o v 551 paid rfl (by decide)
    refine ⟨5,t,by decide,compose (compose a test) z,?_,?_,?_,?_,?_⟩
    · rw [ite_eq_right early];exact location v 551 paid rfl
    · rw [register];change u.getReg .x8+signExtend12 2048+signExtend12 3784=_
      rw [outside s pivot .x8 (by decide),frame,scratch _ fit]
    · intro _;rw [register];rfl
    · exact (memory v paid).trans (memory s pivot)
    · intro r h
      have pair : r≠.x13 ∧ r≠.x29:=by simpa using h
      exact (outside v paid r (by simpa [paid,setBase] using pair)).trans (outside s pivot r (by simpa [pivot] using pair.1))

def increment : List Line := [(.x13,.addiw .x13 4)]

private theorem add4 (j : Fin 513) : ((W j.val).truncate 32+(signExtend12 4).truncate 32).signExtend 64=W (j.val+4) :=
  (by decide +kernel : ∀ i : Fin 513,((W i.val).truncate 32+(signExtend12 4).truncate 32).signExtend 64=W (i.val+4)) j

theorem advance (o : Oracle) (s : MachineState) (n j : Nat) (pc : s.pc=addr 593) (count : s.getReg .x12=W n)
    (index : s.getReg .x13=W j) (small : n≤512) (bound : j≤512) :
    ∃ k t,k≤3 ∧ Segment o k s t [] ∧ t.pc=addr (if j+4<n then 554 else 598) ∧
      t.getReg .x13=W (j+4) ∧ t.mem=s.mem ∧ Kept [.x13] s t := by
  let u:=effect s increment
  have a:=CheckCapArith.positive o s 593 increment pc (by decide)
  have val : u.getReg .x13=W (j+4) := by
    rw [register]
    change ((s.getReg .x13).truncate 32+(signExtend12 4).truncate 32).signExtend 64=_
    rw [index];exact add4 ⟨j,by omega⟩
  have test:=less o u 594 554 .x13 .x12 (j+4) n 8032 (by decide) (location s 593 increment pc) rfl (by decide)
    val ((outside s increment .x12 (by decide)).trans count) (by omega) (by omega)
  have keep : Kept [.x13] s u := fun r h=>outside s increment r (by simpa [increment] using h)
  by_cases more : j+4<n
  · rw [ite_eq_left more] at test
    exact ⟨2,_,by decide,compose a test,by rw [ite_eq_left more];rfl,val,memory ..,keep⟩
  · rw [ite_eq_right more] at test
    have z:=CheckBranch.jump o (u.setPC (addr 595)) 595 598 12 (by decide) rfl rfl (by decide)
    exact ⟨3,_,by decide,compose (compose a test) z,by rw [ite_eq_right more];rfl,val,memory ..,keep⟩

end CommitGolfCandidate.Reconstruction.CheckGroupEdge

