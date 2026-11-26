import CommitGolfCandidate.S5PairRow
import CommitGolfCandidate.S5TrialPairCell
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
namespace TrialPair

private theorem kept (k : Reg) (ok : k ∈ capRegs ∨ k = .x4) : k ≠ .x6 ∧ k ≠ .x7 := by
  cases k <;> simp_all [capRegs]

private theorem to_hash (o : Oracle) (s : MachineState) (l : Bool) (pc : s.pc = pcAt (afterCell l true)) :
    ∃ t n, n ≤ 1 ∧ Flow o s t n 0 ∧ t.pc = pcAt 1191 ∧ t.mem = s.mem ∧ ∀ k, t.getReg k = s.getReg k := by
  cases l
  · exact ⟨s,0,by decide,Flow.refl o s,pc,rfl,fun _ => rfl⟩
  · exact ⟨_,1,by decide,jump o s 1172 1191 .x0 (by decide +kernel) pc,rfl,rfl,fun _ => MachineState.getReg_setPC⟩

attribute [local irreducible] readBuffer
set_option maxRecDepth 8000 in
theorem single (o : Oracle) (s : MachineState) (l : Bool) (a b : Late.Digest)
    (pc : s.pc = pcAt 1141) (dst : s.getReg .x4 = W (nodeAt 0 170))
    (ptr : s.getReg .x9 = W (slotAddr 170)) (rp : s.getReg .x25 = W rowBuf) (scratch : s.getReg .x26 = W chainBuf)
    (flag : Rel.eq.test (s.getReg .x21) (s.getReg .x0) = !l)
    (left : readBuffer s (cellSource l false) 32 = a) (right : readBuffer s (cellSource l true) 32 = b) :
    ∃ t n, n ≤ 214 ∧ Flow o s t n 16 ∧ t.pc = pcAt 1197 ∧
      readBuffer t (nodeAt 0 170) 32 = Chained.parentDigest o.compression (S5.height 15) a b ∧
      CapKeeps s t ∧ ChainOutside s t (nodeAt 0 170) := by
  obtain ⟨u,erase⟩ := clear_words o s 1141 rowBuf 12 .x25 (by unfold ZeroSites; decide +kernel)
    (by decide) pc rp (by decide) (by decide)
  have jump_ := branch o u 1153 1173 .eq .x21 .x0 (by decide +kernel) erase.last (!l) (by rw [erase.regs .x21,erase.regs .x0]; exact flag)
  have land : (if !l then 1173 else 1153+1) = cellPC l false := by cases l <;> rfl
  rw [land] at jump_
  let v := u.setPC (pcAt (cellPC l false))
  have vk (k : Reg) : v.getReg k = s.getReg k := MachineState.getReg_setPC.trans (erase.regs k)
  have saved (r : Bool) : readBuffer v (cellSource l r) 32 = readBuffer s (cellSource l r) 32 :=
    (read_buffer_memory_congr v u rfl _ _).trans (Open.outside_read erase.outside (by decide) (by decide)
      (cellSource l r) 32 (by cases l <;> cases r <;> decide) (Or.inr (by cases l <;> cases r <;> decide)))
  obtain ⟨w,m,ml,first⟩ := fill o v l false a rfl ((vk _).trans ptr) ((vk _).trans rp) ((saved false).trans left)
  have wk (k : Reg) (ok : k ∈ capRegs ∨ k = .x4) : w.getReg k = s.getReg k :=
    (first.keep k (kept k ok).1 (kept k ok).2).trans (vk k)
  have still : readBuffer w (cellSource l true) 32 = b :=
    (Open.outside_read first.mem (by decide) (by decide) _ _ (by cases l <;> decide)
      (Or.inr (by cases l <;> decide))).trans ((saved true).trans right)
  obtain ⟨z,j,jl,second⟩ := fill o w l true b first.pc ((wk _ (Or.inl (by decide))).trans ptr)
    ((wk _ (Or.inl (by decide))).trans rp) still
  have zk (k : Reg) (ok : k ∈ capRegs ∨ k = .x4) : z.getReg k = s.getReg k :=
    (second.keep k (kept k ok).1 (kept k ok).2).trans (wk k ok)
  have blank : CellData v (fun _ => 0) := (blank_cells u erase.zero).same rfl
  have cells := put_cell (put_cell blank 0 (by decide) _ first.data first.mem) 1 (by decide) _ second.data second.mem
  obtain ⟨h,k,kl,toHash,hpc,hm,hk⟩ := to_hash o z l second.pc
  have filled : readBuffer h rowBuf 96 = Late.parentBlock a b := pair_cells h a b (cells.same hm)
  obtain ⟨t,n,nl,hash,ep,out,same,frame⟩ := pair_hash o h true (nodeAt 0 170) a b hpc
    ((hk _).trans ((zk _ (Or.inl (by decide))).trans rp)) ((hk _).trans ((zk _ (Or.inr rfl)).trans dst))
    ((hk _).trans ((zk _ (Or.inl (by decide))).trans scratch)) (by decide) (by decide) filled
  have clearFrame : ChainOutside s v (nodeAt 0 170) :=
    (ChainOutside.inside erase.outside (by decide) (by decide)).trans (ChainOutside.same rfl)
  refine ⟨t,12+1+m+j+k+n,by omega,((((erase.run.trans jump_).trans first.run).trans second.run).trans toHash).trans hash,ep,out,?_,?_⟩
  · exact fun reg ok => (same reg ok).trans ((hk reg).trans (zk reg (Or.inl ok)))
  · exact (((clearFrame.trans (ChainOutside.inside first.mem (by decide) (by decide))).trans
      (ChainOutside.inside second.mem (by decide) (by decide))).trans (ChainOutside.same hm)).trans frame

end TrialPair
end CommitGolfCandidate.S5Machine.Check
