import CommitGolfCandidate.TruncPhaseControl
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 300000

theorem phaseStep (b f : Bool) (k : Nat) (hk : k<128) (s : MachineState) (cs : Cursors b f k s) :
    Runs (im b) s (regStep b f (loc (rowPC b f)) s) ((sequence b f).length+4) ((sequence b f).length+4) := by
  have pc:=cs.pc;rw [if_neg (by omega : k≠128)] at pc
  obtain ⟨src,dst⟩:=beforePtrs b f k hk s cs
  have hr : ordinal b k<128 := by cases b <;> simp [ordinal] <;> omega
  have prePC : (before b f s).pc=loc (bodyPC b f) := by
    cases b
    · exact pc
    · change s.pc+8=_;rw [pc];unfold loc;exact ofNat64_add_eq _ 8 _ (by simp [bodyPC];omega)
  have body : Runs (im b) (before b f s) (moved b f s) (sequence b f).length (sequence b f).length :=
    runBody b f (ordinal b k) hr (before b f s) prePC src dst
  have movedPC : (moved b f s).pc=loc (bodyPC b f+(sequence b f).length) := by
    have lengthPC : (moved b f s).pc=(before b f s).pc+BitVec.ofNat 64 (4*(sequence b f).length) :=
      listPC (moves b f) (before b f s)
    rw [lengthPC,prePC]
    unfold loc sequence;rw [←BitVec.ofNat_add];congr 1;omega
  have readyPC : (ready b f s).pc=loc (rowPC b f+(sequence b f).length+2) := by
    cases b
    · change (moved false f s).pc+8=_;rw [movedPC];unfold loc bodyPC;apply ofNat64_add_eq _ 8 _;simp;omega
    · rw [show (ready true f s).pc=_ from movedPC];unfold bodyPC;congr 1;simp;omega
  have latch:=latchRun b f (ready b f s) readyPC
  cases b
  · have p:=pointerRun false f (moved false f s) movedPC
    have all:=chain (chain body p) latch
    rw [show (sequence false f).length+2+2=(sequence false f).length+4 by omega] at all
    simpa only [regStep,show before false f s=s from rfl] using all
  · have p:=pointerRun true f s pc
    have all:=chain (chain p body) latch
    rw [show 2+(sequence true f).length+2=(sequence true f).length+4 by omega] at all
    simpa only [regStep] using all

theorem phaseLoop (b f : Bool) (left k : Nat) (tot : k+left=128) (s : MachineState) (cs : Cursors b f k s) :
    Runs (im b) s ((regStep b f (loc (rowPC b f)))^[left] s) (((sequence b f).length+4)*left) (((sequence b f).length+4)*left) := by
  induction left generalizing k s with
  | zero => exact runRefl _ s
  | succ n ih =>
    have first:=phaseStep b f k (by omega) s cs
    have rest:=ih (k+1) (by omega) _ (stepCursors b f k (by omega) s cs)
    rw [Function.iterate_succ_apply,Nat.mul_succ,Nat.add_comm (((sequence b f).length+4)*n)]
    exact chain first rest
end CommitGolfCandidate.Trunc.Wire
