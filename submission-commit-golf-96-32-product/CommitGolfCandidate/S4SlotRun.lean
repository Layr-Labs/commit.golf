import CommitGolfCandidate.S4SlotFields
import CommitGolfCandidate.S4Marks
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (W Runs Moved proofBase indexBase Safe)
open Late (Trapdoor Digest pcAt pc_succ)
def slotEnd (s : MachineState) (l : Nat) :=
  let u:=Machine.Sym.evaluated (slotOps l) s
  let v:=Machine.copyBlock .x12 .x19 0 0 (slotMoves l).widths u
  execInstrBr v (.ADDI .x19 .x19 30)
def slotOut (j : Nat) := proofBase+65280+30*j
abbrev slotKeep (r : Reg) := r∉[Reg.x6,.x7,.x12,.x19,.x21,.x30]
structure SlotEnd (tail : Bool) (l j : Nat) (xs : List Index) (s t : MachineState) : Prop where
  run : Runs .opening s t (slotPrice l) (slotPrice l)
  pc : t.pc=pcAt (slotPC tail (l+1))
  cursor : t.getReg .x19=W (slotOut (j+1))
  keep : ∀ r,slotKeep r → t.getReg r=s.getReg r
  moved : Moved s t (slotAddress xs j) (slotOut j) 30

theorem slotBounds (xs : List Index) (j : Nat) (bj : j<171) :
    tdBase≤slotAddress xs j ∧ slotAddress xs j+32 ≤ indexBase ∧ slotAddress xs j%8=0 := by
  have base (h i : Nat) (lim : i<Late.levelCount h) :
      tdBase≤Late.nodeAddress h i ∧ Late.nodeAddress h i+32 ≤ indexBase ∧ Late.nodeAddress h i%8=0:=by
    have top:=Late.parent_below_salts _ _ lim
    exact ⟨by unfold tdBase Late.nodeAddress;omega,top.trans (by decide),Late.nodeAligned _ _⟩
  unfold slotAddress;split
  · exact base 15 _ (show 2*j+1<342 by omega)
  · split
    · exact base 15 _ (show 2*j<342 by omega)
    · exact base 16 j bj

theorem runSlot (tile : Fin 22) (l : Fin 8) (tail : Bool) (existsLane : tail=false ∨ l.val<3)
    (ps : Positions) (batch : ps.card=128) (s : MachineState) (inside : 8*tile.val+l.val<171)
    (pc : s.pc=pcAt (slotPC tail l)) (flags : Marked ps 128 s)
    (srcFlags : s.getReg .x24=W (512+16*tile.val))
    (children : s.getReg .x22=W (Late.rowAddress 15 (8*tile.val)))
    (parents : s.getReg .x23=W (Late.nodeAddress 16 (8*tile.val)))
    (dest : s.getReg .x19=W (slotOut (8*tile.val+l.val))) :
    SlotEnd tail l (8*tile.val+l.val) (indices ps) s (slotEnd s l) := by
  let j:=8*tile.val+l.val;let xs:=indices ps
  let a:=slotAddress xs j;let b:=slotOut j
  let u:=Machine.Sym.evaluated (slotOps l) s
  let v:=Machine.copyBlock .x12 .x19 0 0 (slotMoves l).widths u
  have bl:=l.isLt;have bt:=tile.isLt;have bj : j<171:=inside
  have count : xs.length=128:=(Finset.length_sort ..).trans batch
  have marked (n : Nat) (bound : n<342) : Machine.byte s (512+n)=(if marks xs n then 1 else 0):=by
    have h:=flags n bound
    rw [List.take_of_length_le (by change xs.length≤128;omega)] at h;exact h
  have entry (off : Nat) : s.getReg .x24+W off=W (512+16*tile.val+off):=by
    rw [srcFlags];exact (BitVec.ofNat_add ..).symm
  have read (off : Nat) (lim : 16*tile.val+off<342) :
      (flagExpr off).eval s=flagWord (marks xs (16*tile.val+off)) := by
    simp only [flagExpr,plus,lit,Machine.Sym.eval_mkOp,Machine.Sym.Expr.eval,Machine.Sym.Bin.apply,entry]
    have eqv := marked _ lim
    change s.getByte (W (512+(16*tile.val+off)))=_ at eqv
    rw [Nat.add_assoc,eqv];cases marks xs (16*tile.val+off) <;> rfl
  have argL : (flagExpr (2*l.val)).eval s=flagWord (marks xs (2*j)):=by
    rw [show 2*j=16*tile.val+2*l.val by dsimp [j];omega];exact read _ (by dsimp [j] at bj;omega)
  have argR : (flagExpr (2*l.val+1)).eval s=flagWord (marks xs (2*j+1)):=by
    rw [show 2*j+1=16*tile.val+(2*l.val+1) by dsimp [j];omega];exact read _ (by dsimp [j] at bj;omega)
  obtain ⟨main,advance⟩:=Bool.and_eq_true_iff.mp (slotSite tail l existsLane)
  obtain ⟨prep,copy⟩:=Bool.and_eq_true_iff.mp main
  obtain ⟨form,reads,allowed,nz,len,layout⟩:=slotForm l
  have access (off : Nat) (bound : off<16) : accessValid (s.getReg .x24+W off) 1=true:=by
    rw [entry];apply Safe.valid;exact ⟨by unfold MEMORY_BYTES;omega,Nat.mod_one _⟩
  have safe : ∀ item∈Machine.Sym.requirements Machine.Sym.original (slotOps l),accessValid (item.1.eval s) item.2=true:=by
    rw [reads];intro item mem
    simp only [readAddresses,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl <;> simp only [plus,lit,Machine.Sym.eval_mkOp,Machine.Sym.Expr.eval,Machine.Sym.Bin.apply]
    · exact access _ (by omega)
    · exact access _ (by omega)
  obtain ⟨math,regs,mem,afterMath⟩:=Machine.evalMath .opening _ _ _ s pc prep
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp nz c h)) safe
  have arbitrary (r : Reg) (out : r∉[Reg.x6,.x7,.x12,.x21,.x30]) : u.getReg r=s.getReg r:=by
    rw [show u.getReg r=_ from regs r]
    rw [preserved _ r _ (fun c hc eqv=>out (eqv ▸ (List.contains_iff_mem.mp (List.all_eq_true.mp allowed c hc))))]
    cases r <;> rfl
  have src : u.getReg .x12=W a:=(regs .x12).trans ((congrArg (Machine.Sym.Expr.eval s) form).trans
    (slotAddressValue tile l inside s _ _ argL argR children parents))
  have dst : u.getReg .x19=W b:=(arbitrary _ (by decide)).trans dest
  obtain ⟨lo,hi,al⟩:=slotBounds xs j bj
  have db : b+30≤MEMORY_BYTES:=by dsimp [b,slotOut,proofBase,MEMORY_BYTES];omega
  have sb : a+30≤MEMORY_BYTES:=by change a+32≤7650414624 at hi;unfold MEMORY_BYTES;omega
  have apart : a+30≤b:=by change a+32≤7650414624 at hi;dsimp [b,slotOut,proofBase];omega
  have residue : b%8=(30*l.val)%8:=by dsimp [b,slotOut,proofBase,j];omega
  have ready:=safeActual (30*l.val) a b 30 0 _ layout al residue sb db
  have copied:=Machine.evalCopy .opening (slotMoves l) _ _ a b u afterMath copy
    (show Reg.x6≠.x12 by decide) (show Reg.x6≠.x19 by decide) src dst ready
    (by change a+0+Machine.bytesOf (slotMoves l).widths≤MEMORY_BYTES;rw [Nat.add_zero,len];exact sb)
    (Or.inl (by change a+0+Machine.bytesOf (slotMoves l).widths≤b+0;rw [Nat.add_zero,Nat.add_zero,len];exact apart))
  have ip : v.pc=pcAt (slotPC tail l+11+2*(slotMoves l).widths.length):=copied.endPC
  have fit : ∀ b : Bool,∀ l : Fin 8,slotPC b l+11+2*(slotMoves l).widths.length<16359:=by decide
  have bump:=Machine.stepAdd .opening v _ .x19 .x19 30 (fit tail l) ip (Machine.stood advance)
  refine ⟨(math.trans copied.run).trans bump,Machine.addPC _ _ _ ip,?_,?_,?_⟩
  · change v.getReg .x19+W 30=_
    rw [show v.getReg .x19=u.getReg .x19 from copied.regs .x19 (by decide),dst]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by dsimp [b,slotOut];omega))
  · intro r hr
    simp only [slotKeep,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    have sub : r∉[Reg.x6,.x7,.x12,.x21,.x30]:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or];exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.2⟩
    exact (Machine.keepAdd v .x19 .x19 r 30 (Ne.symm hr.2.2.2.1)).trans
      ((copied.regs r (Ne.symm hr.1)).trans (arbitrary r sub))
  · have h:=copied.bytes;change Moved u v (a+0) (b+0) (Machine.bytesOf (slotMoves l).widths) at h
    rw [Nat.add_zero,Nat.add_zero,len] at h;exact h.congr mem.symm rfl
end CommitGolfCandidate.S4.Open
