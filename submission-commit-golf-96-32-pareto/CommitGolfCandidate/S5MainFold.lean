import CommitGolfCandidate.S5MainStep
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem positions_le (d : Height) (j n : Nat) (simple : ¬chained d) (hi : j+n≤tileSize d) :
    bodyPC d j≤bodyPC d (j+n) := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [Nat.add_succ,←body_advance d (j+n) simple (by omega)];exact (ih (by omega)).trans (Nat.le_add_right ..)

theorem main_lanes (o : Oracle) (d : Height) (b j n ctr : Nat) (s : MachineState) (base : Nat→Output) (salt : Late.SaltTape)
    (frame : MainFrame d b j ctr s) (simple : ¬chained d) (even : b%2=0) (fit : j+n≤tileSize d)
    (available : b+j+n≤count d) (tree : TreeState o.compression base salt d.val s) (done_ : doneRows o.compression base d.val (b+j) s) :
    ∃ u,MainFrame d b (j+n) ctr u ∧ TreeState o.compression base salt d.val u ∧
      doneRows o.compression base d.val (b+(j+n)) u ∧
      Runs .commit true o s u (bodyPC d (j+n)-bodyPC d j) (bodyPC d (j+n)-bodyPC d j+7*n) n := by
  induction n generalizing j s with
  | zero=>exact ⟨s,frame,tree,done_,by simpa using runs_id .commit true o s⟩
  | succ n ih=>
    have room : j<tileSize d:=by omega
    obtain ⟨run,atNext,eff⟩:=main_step o frame simple room even (by omega) tree.pads
    have t:=mainResult o d b j s
    have nextTree:=node_frame tree eff (by omega)
    have used:=grow_row tree done_ eff (by omega)
    rw [show b+j+1=b+(j+1) by omega] at used
    obtain ⟨u,uf,ut,ud,tail⟩:=ih (j+1) _ atNext (by omega) (by omega) nextTree used
    rw [show j+(n+1)=j+1+n by omega]
    refine ⟨u,uf,ut,ud,?_⟩
    have monotone:=positions_le d (j+1) n simple (by omega)
    have step:=body_advance d j simple room
    have joined:=runs_comp run tail
    convert joined using 1 <;> omega
end CommitGolfCandidate.S5Machine
