import CommitGolfCandidate.S4Compare
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)

theorem comparePrefix (p : CompareSite) (o : Oracle) (s : MachineState) (a b : Nat)
    (start : s.pc=pcAt p.start) (lp : s.getReg p.left=W a) (rp : s.getReg p.right=W b)
    (av : AddrOK a 32) (bv : AddrOK b 32) (k : Nat) (bound : k≤4) :
    ((∀ j<k,sameWord s a b j) ∧ ∃ t,CompareContinue o s t (p.wordPC k) (3*k)) ∨
    ((∃ j<k,¬sameWord s a b j) ∧ ∃ steps≤3*k+4,Finishes o s steps 0 .failure) := by
  induction k with
  | zero=>exact Or.inl ⟨fun _ h=>False.elim (by omega),s,⟨fun fuel=>by change obs o (0+fuel) s=((obs o fuel s).1,0+(obs o fuel s).2);rw [Nat.zero_add,Nat.zero_add],start,rfl,fun _ _ _=>rfl⟩⟩
  | succ k ih=>
    rcases ih (by omega) with ⟨valid,t,x⟩|⟨bad,steps,hs,final⟩
    · let j : Fin 4:=⟨k,by omega⟩
      have leftPtr : t.getReg p.left=W a:=(x.regs p.left (by cases p <;> decide) (by cases p <;> decide)).trans lp
      have rightPtr : t.getReg p.right=W b:=(x.regs p.right (by cases p <;> decide) (by cases p <;> decide)).trans rp
      have equal : sameWord t a b k ↔ sameWord s a b k:=by simp only [sameWord,MachineState.getMem,x.mem]
      rcases compareOne p j o t a b x.pc leftPtr rightPtr av bv with ⟨hit,u,y⟩|⟨ne,halt⟩
      · refine Or.inl ⟨fun i hi=>?_,u,⟨?_,?_,y.mem.trans x.mem,fun v h6 h7=>(y.regs v h6 h7).trans (x.regs v h6 h7)⟩⟩
        · by_cases e : i=k
          · subst i;exact equal.mp hit
          · exact valid i (by omega)
        · rw [Nat.mul_succ];exact x.run.trans y.run
        · exact y.pc.trans (congrArg pcAt (by change p.start+4*k+4=p.start+4*(k+1);omega))
      · exact Or.inr ⟨⟨k,by omega,fun e=>ne (equal.mpr e)⟩,3*k+7,by omega,x.run.finish halt⟩
    · exact Or.inr ⟨⟨bad.choose,by have:=bad.choose_spec.1;omega,bad.choose_spec.2⟩,steps,by omega,final⟩

theorem compareDigest (p : CompareSite) (o : Oracle) (s : MachineState) (a b : Nat)
    (pc : s.pc=pcAt p.start) (lp : s.getReg p.left=W a) (rp : s.getReg p.right=W b)
    (av : AddrOK a 32) (bv : AddrOK b 32) :
    (readBuffer s a 32=readBuffer s b 32 ∧ ∃ t,CompareContinue o s t (p.start+16) 12) ∨
    (readBuffer s a 32≠readBuffer s b 32 ∧ ∃ n≤16,Finishes o s n 0 .failure) := by
  have eqv:=read_digest_eq_iff s s a b av.1 bv.1
  rcases comparePrefix p o s a b pc lp rp av bv 4 le_rfl with ⟨all,t,h⟩|⟨⟨j,hj,bad⟩,n,bn,h⟩
  · exact Or.inl ⟨eqv.mpr all,t,h⟩
  · exact Or.inr ⟨fun e=>bad (eqv.mp e j hj),n,bn,h⟩
end CommitGolfCandidate.S4.Machine
