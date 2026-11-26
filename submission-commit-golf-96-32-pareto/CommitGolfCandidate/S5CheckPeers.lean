import CommitGolfCandidate.S5CheckFetchPeer
import CommitGolfCandidate.S5CheckRowBounds
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
private theorem cell_frame {s t} (digit : Nat) (small : digit<3) (local_ : Open.Outside s t (rowCell digit) 32) : RowFrame s t :=
  RowFrame.enlarge local_ (by unfold rowCell;omega) (by unfold rowCell;omega)
private theorem keep_header (q : Reg) (hq : q∈rowRegs) : q∉([.x4,.x6,.x7,.x14] : List Reg):=by cases q <;> simp_all [rowRegs]
private theorem initial_keep {o s t p j v} (start : Placed o s t p j v) : RowKeeps s t:=fun q h=>start.keep q (keep_header q h)
private theorem next_cursor {p : RowSite} {x t r b off} (bit : b=peerBit r p.height.val+(p.radix-1)*S5.bits p.height.val)
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

attribute [local irreducible] readBuffer S5.bits S5.layerBits
set_option maxRecDepth 12000 in
theorem assemble (o : Oracle) (x : CheckInput) (s u : MachineState) (p : RowSite) (j r : Nat) (v : Late.Digest)
    (size : InputSize x p r) (put : Placed o s u p j v) (high : HighInput x s)
    (cur : WireCursor p.batch x s (peerBit r p.height.val) (peerOffset r p.height.val))
    (gp : s.getReg .x3=3) (row : s.getReg .x25=W rowBuf) :
    ∃ t steps,steps≤24+(p.radix-1)*peerLimit p ∧ Assembled o x s t p j r steps v := by
  let b:=peerBit r p.height.val
  let a:=peerOffset r p.height.val
  let w:=S5.bits p.height.val
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
  by_cases top : p.height.val=0
  · have rad : p.radix=3:=if_pos top
    have need : (1 : Nat)<p.radix-1:=by omega
    have ip : z.pc=pcAt (p.peerPC 1):=one.pc.trans (congrArg pcAt (if_pos need))
    have second:=size.budget (k:=1) need
    simp only [Nat.one_mul,Nat.mul_one] at second
    obtain ⟨t,m,mlim,two⟩:=fetch_peer o x z p 1 (b+w) (a+32) next size.allowed need (Nat.mod_lt _ (by omega)) ip one.digit
      ((kz _ (by decide)).trans gp) ((kz _ (by decide)).trans row) one.cursor (uh.after f1 (by decide)) second.1 second.2.1 second.2.2
    have finalDigit : (next+1)%p.radix=cellPeer j p.height.val 1:=by dsimp [next,digit,cellPeer,cell0];rw [rad,show S4.radix p.height.val=3 from rad];omega
    have held : wireValue p.batch x (b+w) (a+32) w=((view p.batch x).peers r p.height.val).2:=by
      dsimp only [a,b,w];rw [top,show S5.bits 0=256 by unfold S5.bits;rfl];exact wire_bottom_peer x p.batch r
    have finalSmall : (next+1)%p.radix<3:=by rw [rad];exact Nat.mod_lt _ (by decide)
    have data2:=put_cell data1 _ finalSmall _ (two.data.trans held) two.mem
    have cells : CellData t (pickedCells p.height.val j v ((view p.batch x).peers r p.height.val)):=by
      unfold pickedCells;rw [if_pos top,←finalDigit];exact data2
    refine ⟨t,24+n+m,by rw [rad];omega,⟨all1.trans two.run,two.pc.trans (congrArg pcAt (if_neg (by omega))),?_,
      two.parent.trans (one.parent.trans put.parent),cells,mf.trans (cell_frame _ finalSmall two.mem),kz.trans two.keep⟩⟩
    apply next_cursor (r:=r) _ _ two.cursor <;> rw [rad] <;> dsimp only [a,b,w] <;> omega
  · have rad : p.radix=2:=if_neg top
    have cells : CellData z (pickedCells p.height.val j v ((view p.batch x).peers r p.height.val)):=by unfold pickedCells;rw [if_neg top];exact data1
    refine ⟨z,24+n,by rw [rad];omega,⟨all1,one.pc.trans (congrArg pcAt (if_neg (by omega))),?_,one.parent.trans put.parent,cells,mf,kz⟩⟩
    apply next_cursor (r:=r) _ _ one.cursor <;> rw [rad] <;> dsimp only [a,b,w] <;> omega
end CommitGolfCandidate.S5Machine.Check
