import CommitGolfCandidate.Stage3cCheckStore
import CommitGolfCandidate.Stage3cOpenWrites
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W wordAt Outside Copied AddrOK)
structure CopySpec where
  rd : Reg
  src : Reg
  dst : Reg
  so : Nat:=0
  doff : Nat:=0
def CopySpec.ld (p : CopySpec) (j : Nat) := Instr.LD p.rd p.src (BitVec.ofNat 12 (p.so+8*j))
def CopySpec.sd (p : CopySpec) (j : Nat) := Instr.SD p.dst p.rd (BitVec.ofNat 12 (p.doff+8*j))
def CopySites (p : CopySpec) (pc n : Nat) := ∀ j : Fin n,
    matchesWord .check (pc+2*j.val,p.ld j.val) ∧ matchesWord .check (pc+2*j.val+1,p.sd j.val)
structure CopyResult (o : Oracle) (s t : MachineState) (site src dst n : Nat) (tmp : Reg) : Prop where
  run : Flow o s t (2*n) 0
  pc : t.pc=pcAt (site+2*n)
  keep : ∀ q,q≠tmp→t.getReg q=s.getReg q
  data : Copied s t src dst n

theorem load_word (o : Oracle) (s : MachineState) (site addr : Nat) (rd rs : Reg) (imm : BitVec 12)
    (pc : s.pc=pcAt site) (enc : Site .check site (.LD rd rs imm)) (src : s.getReg rs+signExtend12 imm=W addr)
    (room : addr+8≤MEMORY_BYTES) (al : addr%8=0) :
    let t:=(s.setReg rd (wordAt s addr)).setPC (pcAt (site+1))
    Flow o s t 1 0 := by
  have ok : memoryArgumentsValid s (.LD rd rs imm)=true := by
    change accessValid (_+_) 8=true;rw [src];exact access_ok addr 8 room (by change addr+8≤2^36 at room;omega) al
  apply one_flow o pc enc
  simp only [ordinaryStep,ok,↓reduceIte,execInstrBr,src,pc,pc_succ];rfl

private theorem imm_addr (s : MachineState) (r : Reg) (a off j : Nat) (base : s.getReg r=W a)
    (bound : off+8*j<512) : s.getReg r+signExtend12 (BitVec.ofNat 12 (off+8*j))=W (a+off+8*j) := by
  rw [base,(by decide +kernel : ∀ q : Fin 512,signExtend12 (BitVec.ofNat 12 q.val)=W q.val) ⟨off+8*j,bound⟩]
  exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by change a+(off+8*j)=a+off+8*j;omega))

theorem copy_words (o : Oracle) (s : MachineState) (pc a b n : Nat) (p : CopySpec) (sites : CopySites p pc n)
    (valid : p.rd≠.x0 ∧ p.rd≠p.src ∧ p.rd≠p.dst) (imms : p.so+8*n≤512 ∧ p.doff+8*n≤512)
    (ip : s.pc=pcAt pc) (sp : s.getReg p.src=W a) (dp : s.getReg p.dst=W b)
    (sa : AddrOK (a+p.so) (8*n)) (da : AddrOK (b+p.doff) (8*n))
    (apart : a+p.so+8*n≤b+p.doff ∨ b+p.doff+8*n≤a+p.so) :
    ∃ t,CopyResult o s t pc (a+p.so) (b+p.doff) n p.rd := by
  induction n with
  | zero=>exact ⟨s,⟨Flow.refl o s,ip,fun _ _=>rfl,⟨fun _ _ _ _=>rfl,fun _ h=>by omega⟩⟩⟩
  | succ n ih=>
    obtain ⟨sm,ds⟩:=imms
    have sb:=sa.2;have db:=da.2;have sal:=sa.1;have dal:=da.1
    obtain ⟨u,old⟩:=ih (fun i=>sites ⟨i.val,by omega⟩) ⟨by omega,by omega⟩ ⟨sal,by omega⟩ ⟨dal,by omega⟩ (by omega)
    let src:=a+p.so+8*n
    let dst:=b+p.doff+8*n
    let temp:=wordAt u src
    let z:=(u.setReg p.rd temp).setPC (pcAt (pc+2*n+1))
    let t:=(store z dst temp).setPC (pcAt (pc+2*n+2))
    have pair:=sites ⟨n,by omega⟩
    have load:=load_word o u (pc+2*n) src p.rd p.src _ old.pc (known pair.1)
      (imm_addr u p.src a p.so n ((old.keep _ valid.2.1.symm).trans sp) (by omega)) (by dsimp [src];omega) (by dsimp [src];omega)
    have zkeep (q : Reg) (h : q≠p.rd) : z.getReg q=u.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.symm)
    have written:=store_step o z (pc+2*n+1) p.dst p.rd _ dst temp rfl (known pair.2)
      (imm_addr z p.dst b p.doff n ((zkeep _ valid.2.2.symm).trans ((old.keep _ valid.2.2.symm).trans dp)) (by omega))
      (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_eq valid.1)) (by dsimp [dst];omega) (by dsimp [dst];omega)
    have elsewhere:=store_far z dst temp (by dsimp [dst];omega)
    have source : temp=wordAt s src:=old.data.outside src (by dsimp [src];omega) (by dsimp [src];omega) (by dsimp [src,dst];omega)
    have before (q : Nat) : wordAt z q=wordAt u q:=by unfold z;cases p.rd <;> rfl
    have frame : Outside s t (b+p.doff) (8*(n+1)):=by
      intro q h align away;exact (elsewhere q h align (by dsimp [dst];omega)).trans ((before q).trans (old.data.outside q h align (by omega)))
    refine ⟨t,⟨?_,?_,?_,⟨frame,?_⟩⟩⟩
    · convert (old.run.trans load).trans written using 1 <;> omega
    · change pcAt (pc+2*n+2)=_;apply congrArg pcAt;omega
    · intro q h;exact (show t.getReg q=z.getReg q by cases q <;> rfl).trans ((zkeep q h).trans (old.keep q h))
    · intro j hj
      by_cases last : j=n
      · subst j;exact (store_word_read z dst temp).trans source
      · exact (elsewhere (b+p.doff+8*j) (by omega) (by omega) (Or.inl (by dsimp [dst];omega))).trans ((before _).trans (old.data.words j (by omega)))

theorem copied_read {s t : MachineState} {a b n : Nat} (data : Copied s t a b n) (sa : a%8=0) (da : b%8=0) :
    readBuffer t b (8*n)=readBuffer s a (8*n) := by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl;intro i hi
  exact congrArg (fun w : Byte=>w.toNat*2^(8*i)) (data.data sa da _ (Finset.mem_range.mp hi))
end CommitGolfCandidate.Chained.BinaryMachine.Check
