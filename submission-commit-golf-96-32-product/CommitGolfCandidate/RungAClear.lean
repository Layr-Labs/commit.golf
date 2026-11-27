import CommitGolfCandidate.RungACore
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxRecDepth 12000
attribute [local irreducible] execute readBuffer DetRun

theorem clearCell (o : Oracle) (s : MachineState) (p j : Nat) (bound : j<32)
    (code : listed p (clearOps j)) (pc : s.pc=pcAt p) :
    ∃ t,MRun o s 4 t 4 0 ∧ t.pc=pcAt (p+4) ∧ (∀ q,t.getReg q=s.getReg q) ∧
      MemPreservedOutside s t (32*j) (32*j+32) ∧ readBuffer t (32*j) 32=0 := by
  let base:=32*j
  have loop (k : Nat) (small : k≤4) :
      ∃ t,MRun o s k t k 0 ∧ t.pc=pcAt (p+k) ∧ (∀ q,t.getReg q=s.getReg q) ∧
        MemPreservedOutside s t base (base+8*k) ∧ ∀ i,i<8*k → t.getByte (Z (base+i))=0 := by
    induction k with
    | zero=>exact ⟨s,DetRun.refl o (R4.submission.image .commit) s,pc,fun _=>rfl,MemPreservedOutside.refl s base (base+8*0),fun _ h=>by omega⟩
    | succ k ih=>
      obtain ⟨u,run,ip,regs,fr,v⟩:=ih (by omega)
      let a:=base+8*k
      have al : a%8=0:=by dsimp [a,base];omega
      have room : a+8≤MEMORY_BYTES:=by dsimp [a,base,MEMORY_BYTES];omega
      have ab : u.getReg .x0+signExtend12 (BitVec.ofNat 12 a)=Z a:=
        by simpa only [c_getReg_x0,Nat.zero_add] using add_signExtend12_ofNat_small 0 a (by dsimp [a,base];omega)
      let t:=(u.setMem (Z a) 0).setPC (u.pc+4)
      have enc:=listHere code k (by simp [clearOps];omega)
      have site : Site (p+k) (.SD .x0 .x0 (BitVec.ofNat 12 a)) := by simpa [Site,Here,clearOps,a,base] using enc
      have safe : memoryArgumentsValid u (.SD .x0 .x0 (BitVec.ofNat 12 a))=true:=by
        change accessValid _ 8=true;rw [ab];exact c_accessValid_ofNat _ _ al room
      have step : MRun o u 1 t 1 0:= by
        apply DetRun.step1 (site _ ip)
        change ordinaryStep u (.base (.SD .x0 .x0 (BitVec.ofNat 12 a)))=_
        rw [ordinaryStep_SD _ _ _ _ safe]
        change some ((u.setMem (u.getReg .x0+signExtend12 _) 0).setPC (u.pc+4))=_
        rw [ab]
      have last : MemPreservedOutside u t a (a+8):=memPreserved_setMem u a 0 al (room.trans (by decide))
      have all : MemPreservedOutside s t base (base+8*(k+1)) :=
        (fr.mono (le_refl _) (by omega)).trans (last.mono (by dsimp [a];omega) (by dsimp [a];omega))
      refine ⟨t,run.trans step,pc_step_idx u (p+k) ip,fun q=>(getReg_setMem u (Z a) 0 q).trans (regs q),all,?_⟩
      intro i hi
      by_cases old : i<8*k
      · exact (last _ (by dsimp [base];omega) (Or.inl (by dsimp [a];omega))).trans (v i old)
      · have atByte:=setMem_getByte_inside u a (i-8*k) 0 al (by omega)
        rw [show a+(i-8*k)=base+i by dsimp [a];omega] at atByte
        exact atByte.trans (BitVec.extractLsb'_zero (w:=64) (len:=8) (start:=8*(i-8*k)))
  obtain ⟨t,run,ip,regs,fr,bytes⟩:=loop 4 le_rfl
  exact ⟨t,run,ip,regs,fr,readBuffer_zero_of_bytes _ _ _ bytes⟩
end CommitGolfCandidate.RungA.Kernel
