import CommitGolfCandidate.S5ClearWords
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside wordAt)
def OffsetSites (r : Reg) (pc off n : Nat) := ∀ j : Fin n,matchesWord .check (pc+j.val,zeroOp r (off+j.val))
theorem clear_offset (o : Oracle) (s : MachineState) (pc base off n : Nat) (r : Reg) (sites : OffsetSites r pc off n)
    (count : off+n≤32) (atPC : s.pc=pcAt pc) (addr : s.getReg r=W base) (space : base+8*off+8*n≤MEMORY_BYTES) (al : base%8=0) :
    ∃ t,Cleared o s t pc (base+8*off) n := by
  induction n with
  | zero=>exact ⟨s,⟨Flow.refl o s,atPC,fun _=>rfl,fun j hj=>by omega,fun _ _ _ _=>rfl⟩⟩
  | succ n ih=>
    obtain ⟨u,g⟩:=ih (fun j=>sites ⟨j.val,by omega⟩) (by omega) (by omega)
    let d:=base+8*off+8*n
    let t:=(store u d 0).setPC (pcAt (pc+n+1))
    have imm : signExtend12 (BitVec.ofNat 12 (8*(off+n)))=W (8*(off+n)):=
      (by decide +kernel : ∀ i : Fin 32,signExtend12 (BitVec.ofNat 12 (8*i.val))=W (8*i.val)) ⟨off+n,by omega⟩
    have loc : u.getReg r+signExtend12 (BitVec.ofNat 12 (8*(off+n)))=W d:=by rw [g.regs,addr,imm];apply (BitVec.ofNat_add ..).symm.trans;apply congrArg W;dsimp [d];omega
    have last:=store_step o u (pc+n) r .x0 _ d 0 g.last (known (sites ⟨n,by omega⟩)) loc rfl (by dsimp [d];omega) (by dsimp [d];omega)
    have out:=store_far u d 0 (by dsimp [d];omega)
    refine ⟨t,⟨g.run.trans last,rfl,?_,?_,?_⟩⟩
    · intro q;exact (show t.getReg q=u.getReg q by cases q <;> rfl).trans (g.regs q)
    · intro j hj
      by_cases eqv : j=n
      · subst j;exact store_word_read u d 0
      · have lt : j<n:=by omega
        exact (out _ (by omega) (by omega) (Or.inl (by dsimp [d];omega))).trans (g.zero j lt)
    · intro j bj aj away;exact (out _ bj aj (by dsimp [d];omega)).trans (g.outside j bj aj (by omega))
end CommitGolfCandidate.S5Machine.Check
