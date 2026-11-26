import CommitGolfCandidate.TruncBlockLayout
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 200000

def prefixMoves (b f : Bool) (n : Nat) := (List.range n).map (item b f)

theorem pivot (b f : Bool) (r j : Nat) (hi : j<count b f) :
    let d:=destStart b f r+(item b f j).dest
    boundary b f r j=(if b then d+2 else d) ∧ boundary b f r (j+1)=(if b then d else d+2) := by
  cases b with
  | false=>
    change sBase f r+2*j=sBase f r+2*j ∧ sBase f r+2*(j+1)=(sBase f r+2*j)+2
    constructor <;> omega
  | true=>
    cases f <;> change _ ∧ _ <;>
      simp only [boundary,destStart,item,count,wide,short,Bool.false_eq_true,ite_false,ite_true] at hi ⊢ <;> omega

theorem boundaryZero (b f : Bool) (r : Nat) : boundary b f r 0 =
    destStart b f (if b then r+1 else r) := by
  cases b <;> cases f <;> simp [boundary,destStart,wBase,sBase,wide] <;> omega

theorem boundaryDone (b f : Bool) (r : Nat) : boundary b f r (count b f)=
    destStart b f (if b then r else r+1) := by
  cases b <;> cases f <;> simp [boundary,count,destStart,wBase,sBase,wide,short] <;> omega

theorem prefixFrame (b f : Bool) (r : Nat) (hr : r<128) (old s : MachineState)
    (sr : s.getReg .x18=BitVec.ofNat 64 (base+sourceStart b f r))
    (dr : s.getReg .x19=BitVec.ofNat 64 (base+destStart b f r))
    (before : Frame b old s (boundary b f r 0)) (n : Nat) (hn : n≤count b f) :
    Frame b old (moveList (prefixMoves b f n) s) (boundary b f r n) := by
  induction n with
  | zero => exact before
  | succ n ih =>
    let m:=item b f n
    let t:=moveList (prefixMoves b f n) s
    have bn : n<count b f := by omega
    have current : Frame b old t (boundary b f r n) := ih (by omega)
    obtain ⟨lim,even,source,mapping⟩ := absoluteFacts b f r n hr bn
    have ind:=pivot b f r n bn
    rw [ind.1] at current
    have next := advanceBytes b old t (destStart b f r+m.dest) (m.source.map (sourceStart b f r+·))
      lim even source mapping current
    have inList : m∈moves b f := List.mem_map_of_mem (List.mem_range.mpr bn)
    have leg:=movesLegal b f m inList
    have memory := moveMem t (base+sourceStart b f r) (base+destStart b f r) m leg.1
      (fun i h=>(leg.2.2 i h).1)
      ((listKept _ s .x18 (by decide)).trans sr) ((listKept _ s .x19 (by decide)).trans dr)
    have maps : (m.source.map (sourceStart b f r+·)).map (base+·) = m.source.map ((base+sourceStart b f r)+·) := by
      cases m.source <;> simp [Nat.add_assoc]
    rw [maps,←Nat.add_assoc] at next
    have stored:=frameMem next memory
    rw [ind.2]
    change Frame b old (moveList ((List.range (n+1)).map (item b f)) s) _
    rw [List.range_succ,List.map_append,List.map_singleton]
    simpa only [moveList,List.flatMap_append,List.flatMap_singleton,List.foldl_append,t,prefixMoves,m,after] using stored

theorem bodyBytes (b f : Bool) (r : Nat) (hr : r<128) (old s : MachineState)
    (sr : s.getReg .x18=BitVec.ofNat 64 (base+sourceStart b f r))
    (dr : s.getReg .x19=BitVec.ofNat 64 (base+destStart b f r))
    (before : Frame b old s (destStart b f (if b then r+1 else r))) :
    Frame b old (moveList (moves b f) s) (destStart b f (if b then r else r+1)) := by
  rw [←boundaryZero] at before
  rw [←boundaryDone]
  exact prefixFrame b f r hr old s sr dr before (count b f) le_rfl

end CommitGolfCandidate.Trunc.Wire
