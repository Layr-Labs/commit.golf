import CommitGolfCandidate.S5CapPairHead
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)

namespace TrialPair
-- The first argument tells which branch was selected, the second which row cell is being written.
def cellPC (left right : Bool) : Nat :=
  if left then (if right then 1164 else 1154) else (if right then 1181 else 1173)
def cellSource (left right : Bool) : Nat :=
  if left != right then bucketAddress (340 + right.toNat) else slotAddr 170
private def addrOps (left right : Bool) : List Sym.Calc :=
  if left != right then [.lui .x6 19,.addi .x6 .x6 (if right then 672 else 640)] else []
private def cp (left right : Bool) : CopySpec :=
  ⟨.x7, if left != right then .x6 else .x9, .x25, 0, 32 * right.toNat⟩
def afterCell (left right : Bool) : Nat :=
  if right then (if left then 1172 else 1191) else cellPC left true

private theorem cell_sites : ∀ l r : Bool,
    Sym.Listed (addrOps l r) (cellPC l r) ∧
    CopySites (cp l r) (cellPC l r + (addrOps l r).length) 4 ∧
    cellPC l r + (addrOps l r).length + 8 = afterCell l r ∧ (addrOps l r).length ≤ 2 := by
  unfold CopySites; decide +kernel

private theorem keep_addr (s : MachineState) (l r : Bool) (k : Reg) (ne : k ≠ .x6) :
    (((addrOps l r).foldl Sym.bump Sym.original) k).eval s = s.getReg k := by
  cases l <;> cases r <;> cases k <;> first | contradiction | rfl

structure Cell (o : Oracle) (s t : MachineState) (l r : Bool) (value : Late.Digest) (n : Nat) : Prop where
  run : Flow o s t n 0
  pc : t.pc = pcAt (afterCell l r)
  data : readBuffer t (rowCell r.toNat) 32 = value
  mem : Outside s t (rowCell r.toNat) 32
  keep : ∀ k, k ≠ .x6 → k ≠ .x7 → t.getReg k = s.getReg k

attribute [local irreducible] Sym.evaluated readBuffer
theorem fill (o : Oracle) (s : MachineState) (l r : Bool) (value : Late.Digest)
    (pc : s.pc = pcAt (cellPC l r)) (ptr : s.getReg .x9 = W (slotAddr 170))
    (rp : s.getReg .x25 = W rowBuf) (data : readBuffer s (cellSource l r) 32 = value) :
    ∃ t n, n ≤ 10 ∧ Cell o s t l r value n := by
  obtain ⟨listed,sites,last,length⟩ := cell_sites l r
  obtain ⟨head,regs,mem,ip⟩ := Sym.compiled o _ _ s pc listed (by
    cases l <;> cases r <;> change ∀ e∈([] : List (Sym.Expr×Nat)),_ <;> simp)
  let u := Sym.evaluated (addrOps l r) s
  have keep (k : Reg) (ne : k ≠ .x6) : u.getReg k = s.getReg k :=
    (regs k).trans (keep_addr s l r k ne)
  have src : u.getReg (cp l r).src = W (cellSource l r) := by
    apply (regs _).trans
    cases l <;> cases r <;> first | exact ptr | rfl
  have bounds : Open.AddrOK (cellSource l r) 32 ∧ Open.AddrOK (rowCell r.toNat) 32 ∧
      rowCell r.toNat + 32 ≤ cellSource l r  := by
    unfold Open.AddrOK; cases l <;> cases r <;> decide
  obtain ⟨t,done_⟩ := copy_words o u _ (cellSource l r) rowBuf 4 (cp l r) sites
    (by cases l <;> cases r <;> decide) (by cases l <;> cases r <;> decide) ip src
    ((keep .x25 (by decide)).trans rp) bounds.1 bounds.2.1 (Or.inr bounds.2.2)
  refine ⟨t,(addrOps l r).length + 8,by omega,⟨head.trans done_.run,done_.pc.trans (congrArg pcAt last),?_,?_,?_⟩⟩
  · exact (copied_read (a:=cellSource l r) (b:=rowCell r.toNat) (n:=4) done_.data bounds.1.1 bounds.2.1.1).trans
      ((read_buffer_memory_congr u s mem _ _).trans data)
  · intro j h a e
    exact (done_.data.outside j h a e).trans (congrFun mem _)
  · intro k a b
    exact (done_.keep k b).trans (keep k a)

end TrialPair
end CommitGolfCandidate.S5Machine.Check
