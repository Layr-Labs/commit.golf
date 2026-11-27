import CommitGolfCandidate.Stage3cOrdinaryLoop
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape record)
def ordinaryCost (xs : List Index) : Nat→Nat→Nat
  | _,0=>0
  | r,n+1=>(475)+ordinaryCost xs (r+1) n

theorem ordinary_cost_bound (xs : List Index) (r n : Nat) : ordinaryCost xs r n≤475*n := by
  induction n generalizing r with
  | zero=>simp [ordinaryCost]
  | succ n ih=>have tail:=ih (r+1);rw [ordinaryCost,Nat.mul_succ];omega

structure OrdinaryRegs (s : MachineState) (r k dst : Nat) : Prop where
  pc : s.pc=pcAt (if r<k then 460 else 935)
  table : s.getReg .x3=W 2048
  indices : s.getReg .x9=W (indexBase+8*r)
  remaining : s.getReg .x22=W (k-r)
  salts : s.getReg .x20=W rowBase
  proof : s.getReg .x18=W proofBase
  dest : s.getReg .x19=W dst

attribute [local irreducible] afterLatch readBuffer ix
set_option maxHeartbeats 180000
set_option Elab.async false

def perRecord (xs : List Index) (r : Nat) := 475

private theorem advance_frame {s u v : MachineState} {r k dst : Nat} (old : OrdinaryRegs s r k dst)
    (pc : v.pc=pcAt (if r+1<k then 460 else 935))
    (remain : v.getReg .x22=W (k-(r+1)))
    (keep : ∀ q,q∉([.x4,.x6,.x7,.x9,.x14,.x19,.x28] : List Reg)→u.getReg q=s.getReg q)
    (last : ∀ q,q≠.x22→v.getReg q=u.getReg q)
    (ix : u.getReg .x9=W (indexBase+8*(r+1))) (dest : u.getReg .x19=W (dst+792)) :
    OrdinaryRegs v (r+1) k (dst+792) :=
  ⟨pc,(last .x3 (by decide)).trans ((keep .x3 (by decide)).trans old.table),
    (last .x9 (by decide)).trans ix,remain,(last .x20 (by decide)).trans ((keep .x20 (by decide)).trans old.salts),
    (last .x18 (by decide)).trans ((keep .x18 (by decide)).trans old.proof),(last .x19 (by decide)).trans dest⟩

private theorem frame_relabel (s t : MachineState) (eq : t.mem=s.mem) (tab : Capacity s) : Capacity t :=
  fun j hj=>(congrFun eq (W (2048+8*j))).trans (tab j hj)

theorem record_cycle (xs : List Index) (tree : Levels) (salt : SaltTape) (r dst : Nat) (s : MachineState)
    (lt : r<xs.length) (size : xs.length≤LENGTH) (reg : OrdinaryRegs s r xs.length dst) (tab : Capacity s)
    (src : Sources s xs tree salt) (high : proofBase≤dst) (valid : AddrOK dst 792) :
    ∃ v,Runs s v (perRecord xs r) (perRecord xs r+3) ∧ OrdinaryRegs v (r+1) xs.length (dst+792) ∧
      Capacity v ∧ Sources v xs tree salt ∧ Written s v dst (record tree salt LOG_LENGTH (ix xs r)) := by
  obtain ⟨u,head,ip,dest,ix',table,sources,keep,data⟩:=ordinary_record s r dst xs tree salt lt size
    (reg.pc.trans (by rw [if_pos lt])) reg.table tab reg.indices reg.salts reg.dest high valid src
  let n:=xs.length-(r+1)
  have left : n<LENGTH := by dsimp [n];omega
  have cnt : u.getReg .x22=W (n+1) :=
    (keep .x22 (by decide)).trans (reg.remaining.trans (congrArg W (by dsimp [n];omega)))
  obtain ⟨back,pc,rem,same,regs⟩:=latch u n left ip cnt
  let v:=afterLatch u
  have mode : (if 0<n then 460 else 935)=(if r+1<xs.length then 460 else 935) := by dsimp [n];split <;> split <;> omega
  have next:=advance_frame reg (pc.trans (congrArg pcAt mode)) rem keep regs ix' dest
  have c:=frame_relabel u v same table
  refine ⟨v,?_,next,c,sources.same_mem same,data.congr_mem rfl same⟩
  exact head.trans back
end CommitGolfCandidate.Chained.BinaryMachine.Open
