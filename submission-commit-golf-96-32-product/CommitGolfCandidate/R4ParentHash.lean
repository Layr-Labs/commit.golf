import CommitGolfCandidate.R4ParentCall
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ rowAddress nodeAddress)
attribute [local irreducible] DetRun writeBits readBuffer submission
set_option maxHeartbeats 300000
theorem callAndMask (o : Oracle) (s : MachineState) (n p : Nat) (d : Width)
    (hi : p<nodes d) (f : Pointers d p s) (pc : s.pc=pcAt n) (code : LaneCode n (extra d) (destInc p)) :
    let a:=nodeAddress (d.val+1) p
    let w:=o.compression (readBuffer s (rowAddress d p) 96)
    ∃ v,Masked o s v a (n+1) (extra d) w (Late.retain (23-d.val) w) ∧ MRun o s 1 (writeBits s (Z a) w) 8 1 := by
  let a:=nodeAddress (d.val+1) p
  let b:=rowAddress d p
  let w:=o.compression (readBuffer s b 96)
  let raw:=writeBits s (Z a) w
  have ba : a+32≤MEMORY_BYTES:=(Late.parent_below_salts (d.val+1) p hi).trans (by decide)
  have alg : a%8=0:=Late.nodeAligned _ _
  have call:=simpleCall o s n p d hi f pc code.compress
  have ip : raw.pc=pcAt (n+1):=(pc_writeBits ..).trans ((congrArg (·+4) pc).trans (pc_succ _).symm)
  have masked : ∃ v,Masked o s v a (n+1) (extra d) w (Late.retain (23-d.val) w) := by
    rw [retFor d w]
    rcases extras d with e|e|e
    · rw [e];exact ⟨raw,⟨DetRun.refl ..,rfl,ip,fun _ _=>writeBits_register ..⟩⟩
    · rw [e];exact maskWide o s (n+1) a w ip f.dst alg ba (code.short e)
    · rw [e];exact maskNarrow o s (n+1) a w ip f.dst f.mask alg ba (code.load e) (code.cut e) (code.store e)
  obtain ⟨v,h⟩:=masked
  exact ⟨v,h,call⟩
end CommitGolfCandidate.R4
