import CommitGolfCandidate.S4BatchRecord
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (W Runs proofBase indexBase)
open Late (Trapdoor pcAt)
def rowTotal (price : Nat→Nat) : Nat→Nat | 0=>0 | n+1=>rowTotal price n+price n
def rowSteps (r : Nat) := laneSteps r+recordLatch r
def rowCost (r : Nat) := laneCost r+recordLatch r

theorem batchStep (td : Trapdoor) (ps : Positions) (s : MachineState) (r : Nat) (batch : ps.card=128)
    (br : r<128) (f : BatchCursor td ps s r) : ∃ t,BatchCursor td ps t (r+1) ∧ Runs .opening s t (rowSteps r) (rowCost r) := by
  obtain ⟨z,data,pc,idx,tiles,run⟩:=oneBatchRecord td ps s r batch br f
  have l : r%8<8:=Nat.mod_lt _ (by decide)
  have endOf :=recordEnd ⟨r%8,l⟩
  change markPC (r%8)+2=(if r%8+1<8 then recordPC true (r%8+1) else 4888) at endOf
  have ireg:=idx.trans f.ix;have treg:=tiles.trans f.tiles
  by_cases last : r%8=7
  · rw [if_neg (by omega)] at endOf
    have rowPC : z.pc=pcAt 4888:=pc.trans (congrArg pcAt endOf)
    obtain ⟨tail,ip,ix,cnt,mem,regs⟩:=tileLatch (r/8) (by omega) z rowPC ireg treg
    let t:=tileEnd z (r/8)
    have next : tileDest (r/8)=batchNext (r+1):=by
      unfold tileDest batchNext
      by_cases e:r+1<128
      · rw [if_pos e,if_neg (by omega),show (r+1)%8=0 by omega];rfl
      · rw [if_neg e,if_pos (by omega)]
    refine ⟨t,⟨data.preserve mem (fun k a b=>regs k b a),ip.trans (congrArg pcAt next),?_,?_⟩,?_⟩
    · exact ix.trans (congrArg W (by omega))
    · exact cnt.trans (congrArg W (by omega))
    · unfold rowSteps rowCost recordLatch;rw [if_pos last];exact run.trans tail
  · have inRow : r%8+1<8:=by omega
    have next : r+1<128:=by omega
    have div : (r+1)/8=r/8:=by omega
    rw [if_pos inRow] at endOf
    refine ⟨z,⟨data,?_,by rw [div];exact ireg,by rw [div];exact treg⟩,?_⟩
    · rw [batchNext,if_pos next,show (r+1)%8=r%8+1 by omega];exact pc.trans (congrArg pcAt endOf)
    · simpa only [rowSteps,rowCost,recordLatch,if_neg last,Nat.add_zero] using run

theorem rows (td : Trapdoor) (ps : Positions) (s : MachineState) (batch : ps.card=128) (f : BatchCursor td ps s 0)
    (n : Nat) (limit : n≤128) :
    ∃ t,BatchCursor td ps t n ∧ Runs .opening s t (rowTotal rowSteps n) (rowTotal rowCost n) := by
  induction n with
  | zero=>exact ⟨s,f,Runs.refl .opening s⟩
  | succ n ih=>
    obtain ⟨t,cur,h⟩:=ih (by omega)
    obtain ⟨u,next,tail⟩:=batchStep td ps t n batch (by omega) cur
    exact ⟨u,next,h.trans tail⟩

end CommitGolfCandidate.S4.Open
