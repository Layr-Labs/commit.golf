import CommitGolfCandidate.S5CheckPeerRead
import CommitGolfCandidate.S5CheckRowHeader
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def peerTarget (b : Bool) := if b then Reg.x10 else .x6
private theorem peer_values (s : MachineState) (p : RowSite) (digit : Nat) (bound : digit<p.radix)
    (old : s.getReg .x4=W digit) (gp : s.getReg .x3=3) (row : s.getReg .x25=W rowBuf) :
    let f:=p.peerOps.foldl Sym.bump Sym.original
    let next:=(digit+1)%p.radix
    (f .x4).eval s=W next ∧ (f (peerTarget p.batch)).eval s=W (rowCell next) := by
  have addr (k : Nat) : s.getReg .x25+(W k <<< 5)=W (rowCell k):=by
    rw [row];unfold W;rw [Open.shifted];apply (BitVec.ofNat_add ..).symm.trans;apply congrArg W;dsimp [rowCell];omega
  rcases p with ⟨b,h⟩
  by_cases tri : h.val=0
  · have rad : (RowSite.mk b h).radix=3:=if_pos tri
    have small : digit<3:=rad ▸ bound
    have next : rv64_remu (s.getReg .x4+signExtend12 1) (s.getReg .x3)=W ((digit+1)%3):=by
      rw [old,gp];change rv64_remu (BitVec.ofNat 64 digit+BitVec.ofNat 64 1) _=_
      rw [←BitVec.ofNat_add];exact (Open.div_three (digit+1) (by omega)).2
    simp only [RowSite.peerOps,tri,ite_true,rad,List.cons_append,List.nil_append]
    cases b <;> constructor
    all_goals first | exact next | (change s.getReg .x25+(rv64_remu (s.getReg .x4+signExtend12 1) (s.getReg .x3) <<< 5)=_;rw [next];exact addr _)
  · have rad : (RowSite.mk b h).radix=2:=if_neg tri
    have small : digit<2:=rad ▸ bound
    have flip : s.getReg .x4 ^^^ 1#64=W ((digit+1)%2):=by rw [old];interval_cases digit <;> rfl
    simp only [RowSite.peerOps,tri,ite_false,rad,List.cons_append,List.nil_append]
    cases b <;> constructor
    all_goals first | exact flip | (change s.getReg .x25+((s.getReg .x4 ^^^ 1#64) <<< 5)=_;rw [flip];exact addr _)

private theorem peer_expr_keeps (s : MachineState) (p : RowSite) (q : Reg) (safe : q∉([.x4,.x6,.x10] : List Reg)) :
    ((p.peerOps.foldl Sym.bump Sym.original) q).eval s=s.getReg q := by
  rcases p with ⟨b,h⟩;unfold RowSite.peerOps;split <;> cases b <;> cases q <;> first | (exfalso;apply safe;decide) | rfl

structure PeerChoice (o : Oracle) (s t : MachineState) (p : RowSite) (k digit : Nat) : Prop where
  run : Flow o s t p.peerOps.length 0
  pc : t.pc=pcAt (p.peerPC k+p.peerOps.length)
  lane : t.getReg .x4=W ((digit+1)%p.radix)
  address : t.getReg (peerTarget p.batch)=W (rowCell ((digit+1)%p.radix))
  mem : t.mem=s.mem
  keep : ∀ q,q∉([.x4,.x6,.x10] : List Reg)→t.getReg q=s.getReg q

theorem pick_peer (o : Oracle) (s : MachineState) (p : RowSite) (k : Fin 2) (digit : Nat) (valid : p.allowed=true)
    (needed : k.val<p.radix-1) (bound : digit<p.radix) (pc : s.pc=pcAt (p.peerPC k.val)) (old : s.getReg .x4=W digit)
    (gp : s.getReg .x3=3) (row : s.getReg .x25=W rowBuf) : ∃ t,PeerChoice o s t p k.val digit := by
  have site:=((row_sites p valid).2.2.2.2.2.2 k needed).1
  obtain ⟨run,regs,mem,ep⟩:=Sym.compiled o p.peerOps _ s pc site (by
    rcases p with ⟨b,h⟩;unfold RowSite.peerOps;split <;> cases b <;> change ∀ e∈([] : List (Sym.Expr×Nat)),_ <;> simp)
  obtain ⟨next,addr⟩:=peer_values s p digit bound old gp row
  exact ⟨_,⟨run,ep,(regs _).trans next,(regs _).trans addr,mem,fun q h=>(regs q).trans (peer_expr_keeps s p q h)⟩⟩
end CommitGolfCandidate.S5Machine.Check
