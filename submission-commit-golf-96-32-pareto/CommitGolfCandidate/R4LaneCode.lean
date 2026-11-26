import CommitGolfCandidate.R4ParentCode
import CommitGolfCandidate.R4Mask
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ rowAddress nodeAddress)

structure Env (s : MachineState) : Prop where
  mode : s.getReg .x5=0
  kind : s.getReg .x13=0
  width : s.getReg .x11=96
  root : s.getReg .x26=4294971392

structure Pointers (d : Width) (p : Nat) (s : MachineState) extends Env s : Prop where
  src : s.getReg .x10=Z (rowAddress d p)
  dst : s.getReg .x12=Z (nodeAddress (d.val+1) p)
  mask : s.getReg .x28=16383

structure LaneCode (n e inc : Nat) : Prop where
  compress : Site n .ECALL
  short : e=1 → Site (n+1) (.SH .x12 .x0 30)
  load : e=3 → Site (n+1) (.LHU .x6 .x12 28)
  cut : e=3 → Site (n+2) (.AND .x6 .x6 .x28)
  store : e=3 → Site (n+3) (.SW .x12 .x6 28)
  nextSrc : Site (n+1+e) (.ADDI .x10 .x10 96)
  nextDst : Site (n+1+e+1) (.ADDI .x12 .x12 (BitVec.ofNat 12 inc))

theorem extras (d : Width) : extra d=0 ∨ extra d=1 ∨ extra d=3 := by unfold extra;split_ifs <;> simp
theorem laneCode {n : Nat} {d : Width} {j : Nat} (h : listed n (laneOps d j)) :
    LaneCode n (extra d) (destInc j) := by
  have c:=listHere h
  rcases extras d with e|e|e <;> rw [e] <;>
    simp only [laneOps,e,maskOps,ite_true,ite_false,List.nil_append,List.cons_append,List.singleton_append,
      show ¬(1=0) by decide,show ¬(3=0) by decide,show ¬(3=1) by decide] at c
  · exact ⟨c 0 (by simp),(by intro h;contradiction),(by intro h;contradiction),(by intro h;contradiction),(by intro h;contradiction),c 1 (by simp),c 2 (by simp)⟩
  · exact ⟨c 0 (by simp),fun _=>c 1 (by simp),(by intro h;contradiction),(by intro h;contradiction),(by intro h;contradiction),c 2 (by simp),c 3 (by simp)⟩
  · exact ⟨c 0 (by simp),(by intro h;contradiction),fun _=>c 1 (by simp),fun _=>c 2 (by simp),fun _=>c 3 (by simp),c 4 (by simp),c 5 (by simp)⟩

theorem retFor (d : Width) (w : Digest) : Late.retain (23-d.val) w =
    if extra d=3 then Trunc.pad238 w else if extra d=1 then Trunc.padLow w else w := by
  fin_cases d <;> rfl

theorem addrSrc (d : Width) (p : Nat) : rowAddress d p+96=rowAddress d (p+1) := by unfold rowAddress;omega
theorem addrDst (d : Width) (p : Nat) : nodeAddress (d.val+1) p+destInc p=nodeAddress (d.val+1) (p+1) := by
  simp only [Late.binaryAddress,Late.gapOffset,destInc];split <;> omega

end CommitGolfCandidate.R4
