import CommitGolfCandidate.Stage3cCheckFetchPeer
import CommitGolfCandidate.Stage3cCheckRowBounds
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
private theorem cell_frame {s t} (digit : Nat) (small : digit<3) (local_ : Open.Outside s t (rowCell digit) 32) : RowFrame s t :=
  RowFrame.enlarge local_ (by unfold rowCell;omega) (by unfold rowCell;omega)
private theorem keep_header (q : Reg) (hq : q∈rowRegs) : q∉([.x4,.x6,.x7,.x14] : List Reg):=by cases q <;> simp_all [rowRegs]
private theorem initial_keep {o s t p j v} (start : Placed o s t p j v) : RowKeeps s t:=fun q h=>start.keep q (keep_header q h)
private theorem next_cursor {p : RowSite} {x t r b off} (bit : b=peerBit r p.height.val+(p.radix-1)*Pw.bits p.height.val)
    (byte : off=peerOffset r p.height.val+32*(p.radix-1)) (cur : WireCursor p.batch x t b off) :
    WireCursor p.batch x t (peerBit r (p.height.val+1)) (peerOffset r (p.height.val+1)) := by
  rw [bit,byte,peer_bit_next,peer_offset_next] at cur;exact cur

structure Assembled (o : Oracle) (x : CheckInput) (s t : MachineState) (p : RowSite) (j r steps : Nat) (v : Late.Digest) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt p.hashPC
  cursor : WireCursor p.batch x t (peerBit r (p.height.val+1)) (peerOffset r (p.height.val+1))
  parent : t.getReg .x14=W (j/p.radix)
  cells : CellData t (pickedCells p.height.val j v ((view p.batch x).peers r p.height.val))
  frame : RowFrame s t
  keep : RowKeeps s t

attribute [local irreducible] readBuffer Pw.bits Pw.layerBits
set_option maxRecDepth 12000 in
theorem assemble (o : Oracle) (x : CheckInput) (s u : MachineState) (p : RowSite) (j r : Nat) (v : Late.Digest)
    (size : InputSize x p r) (put : Placed o s u p j v) (high : HighInput x s)
    (cur : WireCursor p.batch x s (peerBit r p.height.val) (peerOffset r p.height.val))
    (gp : s.getReg .x3=3) (row : s.getReg .x25=W rowBuf) :
    ∃ t steps,steps≤24+(p.radix-1)*peerLimit p ∧ Assembled o x s t p j r steps v := by
  let b:=peerBit r p.height.val
  let a:=peerOffset r p.height.val
  let w:=Pw.bits p.height.val
  let digit:=j%p.radix
  let next:=(digit+1)%p.radix
  have ku:=initial_keep put
  have uh:=high.after put.frame (by decide)
  have uc:=cur.frame put.frame (by decide) (by decide) (by decide) (put.keep _ (by decide)) (put.keep _ (by decide))
    (put.keep _ (by decide)) (put.keep _ (by decide))
  have radix:=rowNumbers p
  have bound : digit<p.radix:=Nat.mod_lt _ (by omega)
  have first :=size.budget (k:=0) (by omega)
  simp only [Nat.zero_mul,Nat.mul_zero,Nat.add_zero] at first
  obtain ⟨z,n,nlim,one⟩:=fetch_peer o x u p 0 b a digit size.allowed (by omega) bound put.pc put.digit
    ((ku _ (by decide)).trans gp) ((ku _ (by decide)).trans row) uc uh first.1 first.2.1 first.2.2
  have nextSmall : next<3:=(Nat.mod_lt _ (by omega : 0<p.radix)).trans_le radix.2.2.1
  have f1:=cell_frame _ nextSmall one.mem
  have data1:=put_cell put.cells next nextSmall _ (one.data.trans (wire_peer x p.batch r p.height.val)) one.mem
  have all1:=put.run.trans one.run
  have kz:=ku.trans one.keep
  have mf:=put.frame.trans f1
  have rad : p.radix=2:=rfl
  have cells : CellData z (pickedCells p.height.val j v ((view p.batch x).peers r p.height.val)):=by unfold pickedCells;exact data1
  refine ⟨z,24+n,by rw [rad];omega,⟨all1,one.pc.trans (congrArg pcAt (if_neg (by rw [rad];omega))),?_,one.parent.trans put.parent,cells,mf,kz⟩⟩
  apply next_cursor (r:=r) _ _ one.cursor <;> rw [rad] <;> dsimp only [a,b,w] <;> omega
end CommitGolfCandidate.Chained.BinaryMachine.Check
