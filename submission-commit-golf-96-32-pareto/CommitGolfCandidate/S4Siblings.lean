import CommitGolfCandidate.S4NodeCode
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest)
def siblingCode (b : Bool) (h : Nat) := loadCode 352 (nodeLength b h)++extraLoad h
def otherSize (h : Nat) := if h=0 then 32 else 0
def siblingsCost (b : Bool) (h : Nat) := fieldSteps (nodeLength b h)+(if h=0 then fieldSteps 32 else 0)
def peersBefore (s : MachineState) (src n : Nat) (h : Nat) : Peers :=
  ((readBuffer s src n).setWidth 256,if h=0 then readBuffer s (src+n) 32 else 0)
abbrev siblingKeep (r : Reg) := r≠.x6 ∧ r≠.x14 ∧ r≠.x18

structure Siblings (s t : MachineState) (src site n h steps : Nat) : Prop where
  run : Runs .check s t steps steps
  pc : t.pc=pcAt (site+steps)
  cursor : t.getReg .x18=W (src+n+otherSize h)
  keep : ∀ r,siblingKeep r → t.getReg r=s.getReg r
  outside : SameOutside s t 352 64
  a : readBuffer t 352 32=(peersBefore s src n h).1
  b : h=0 → readBuffer t 384 32=(peersBefore s src n h).2

theorem siblingsRun (s : MachineState) (site src h : Nat) (b : Bool) (bh : h<pathLevels b)
    (pc : s.pc=pcAt site) (room : site+siblingsCost b h≤Code.check.count)
    (code : Matches .check site (siblingCode b h)) (cursor : s.getReg .x18=W src)
    (low : 32768≤src) (high : src+nodeLength b h+otherSize h≤MEMORY_BYTES) :
    ∃ t,Siblings s t src site (nodeLength b h) h (siblingsCost b h) := by
  let n:=nodeLength b h
  have size : n=30 ∨ n=32:=(nodeSize b h bh).1
  have body:=loadField s site src 352 n (Or.inr size) code.left (by dsimp only [n];unfold siblingsCost at room;omega)
    pc cursor (by decide) (by exact ⟨by decide,by decide⟩) (by dsimp only [n];omega) (by omega)
  let u:=loaded s 352 n
  by_cases z : h=0
  · subst h
    have room2 : site+fieldSteps n+fieldSteps 32≤Code.check.count:=by
      simpa only [siblingsCost,n,ite_true,Nat.add_assoc] using room
    have second : Matches .check (site+fieldSteps n) (loadCode 384 32):=by
      have e:=code.right;rw [codeLength] at e;exact e
    have extra:=loadField u (site+fieldSteps n) (src+n) 384 32 (Or.inr (Or.inr rfl)) second room2 body.pc body.cursor
      (by decide) (by exact ⟨by decide,by decide⟩) high (by omega)
    let v:=loaded u 384 32
    have original:=body.outside.read (a:=352) (n:=32) (b:=src+n) (m:=32)
      (by have:=high;change src+n+32≤2^36 at this;omega) (Or.inr (by omega))
    refine ⟨v,⟨?_,?_,extra.cursor,fun r ok=>(extra.keep r ok.1 ok.2.1 ok.2.2).trans (body.keep r ok.1 ok.2.1 ok.2.2),
      body.outside.combined extra.outside (by decide),?_,?_⟩⟩
    · exact body.run.trans extra.run
    · exact extra.pc.trans (congrArg pcAt (Nat.add_assoc ..))
    · exact (extra.outside.read (b:=352) (m:=32) (by decide) (Or.inl (by decide))).trans (body.digest size)
    · intro _;exact extra.low.trans original
  · have sizeEq : siblingsCost b h=fieldSteps n:=by simp only [siblingsCost,if_neg z,Nat.add_zero,n]
    refine ⟨u,⟨sizeEq.symm ▸ body.run,?_,?_,fun r ok=>body.keep r ok.1 ok.2.1 ok.2.2,?_,body.digest size,fun e=>False.elim (z e)⟩⟩
    · rw [sizeEq];exact body.pc
    · rw [otherSize,if_neg z,Nat.add_zero];exact body.cursor
    · intro q bound out;exact body.outside q bound (by omega)
end CommitGolfCandidate.S4.Machine
