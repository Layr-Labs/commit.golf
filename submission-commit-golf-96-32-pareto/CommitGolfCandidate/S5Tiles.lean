import CommitGolfCandidate.S5StageLaw
import CommitGolfCandidate.S5TileEnd
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def tilesPrice (d : Height) (n : Nat) := n*(mainExit d-mainPC d)-
  (if n≠0 ∧ tileSize d=252 then 1 else 0)

private theorem tile_price (d : Height) (simple : ¬chained d) (used : 0<tileSize d) :
    bodyPC d (tileSize d)-bodyPC d 0+tileControl d true=mainExit d-mainPC d ∧
    bodyPC d (tileSize d)-bodyPC d 0+tileControl d false=mainExit d-mainPC d-(if tileSize d=252 then 1 else 0) ∧
    0<mainExit d-mainPC d :=
  (by decide +kernel : ∀ k : Height, ¬chained k → 0<tileSize k →
    bodyPC k (tileSize k)-bodyPC k 0+tileControl k true=mainExit k-mainPC k ∧
    bodyPC k (tileSize k)-bodyPC k 0+tileControl k false=mainExit k-mainPC k-(if tileSize k=252 then 1 else 0) ∧
    0<mainExit k-mainPC k) d simple used

theorem many_tiles (o : Oracle) (d : Height) (n b : Nat) (s : MachineState) (base : Nat→Output) (salt : Late.SaltTape)
    (simple : ¬chained d) (used : 0<tileSize d) (even : b%2=0)
    (room : b+n*tileSize d≤count d) (frame : Boundary d b n s)
    (tree : TreeState o.compression base salt d.val s) (done_ : doneRows o.compression base d.val b s) :
    ∃ t,Boundary d (b+n*tileSize d) 0 t ∧ TreeState o.compression base salt d.val t ∧
      doneRows o.compression base d.val (b+n*tileSize d) t ∧
      Runs .commit true o s t (tilesPrice d n) (tilesPrice d n+7*(n*tileSize d)) (n*tileSize d) := by
  induction n generalizing s b with
  | zero=>exact ⟨s,by simpa using frame,tree,by simpa using done_,by simpa [tilesPrice] using runs_id .commit true o s⟩
  | succ k ih=>
    have fit : b+tileSize d≤count d := by rw [Nat.succ_mul] at room;omega
    have ctr : k+1<2^64 := by
      have bound : count d≤16777216:=level_count_le _
      have positive:=Nat.mul_le_mul_left (k+1) (show 1≤tileSize d from used)
      simp only [Nat.mul_one] at positive;omega
    obtain ⟨middle,frame',tree',rows',first⟩:=main_lanes o d b 0 (tileSize d) (k+1) s base salt (begin_tile frame (by omega))
      simple even (by omega) (by omega) tree (by simpa using done_)
    simp only [Nat.zero_add] at frame' rows' first
    obtain ⟨next,mem,finish⟩:=tile_end o frame' simple used ctr
    have evenNext : (b+tileSize d)%2=0 := by rcases main_shape d simple used with e|e <;> omega
    have total : b+(k+1)*tileSize d=(b+tileSize d)+k*tileSize d := by rw [Nat.succ_mul];omega
    obtain ⟨t,last,treeEnd,rowsEnd,rest⟩:=ih (b+tileSize d) _ evenNext (total ▸ room) next (transfer_tree tree' mem) (transfer_rows rows' mem)
    refine ⟨t,total ▸ last,treeEnd,total ▸ rowsEnd,?_⟩
    have price : tilesPrice d (k+1)=bodyPC d (tileSize d)-bodyPC d 0+tileControl d (decide (0<k))+tilesPrice d k := by
      obtain ⟨more,final,positive⟩:=tile_price d simple used
      cases k with
      | zero=>simp [tilesPrice,final]
      | succ k=>
        simp only [Nat.zero_lt_succ,decide_true,more,tilesPrice,Nat.succ_ne_zero,not_false_eq_true,true_and,Nat.succ_mul]
        split_ifs <;> omega
    have all:=runs_comp (runs_comp first finish) rest
    rw [price,Nat.succ_mul]
    convert all using 1 <;> omega
end CommitGolfCandidate.S5Machine
