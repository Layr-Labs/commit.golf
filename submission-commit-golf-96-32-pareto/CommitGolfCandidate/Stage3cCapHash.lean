import CommitGolfCandidate.Stage3cCapData
import CommitGolfCandidate.Stage3cCheckEdges
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def parentSites (pc level : Nat) := matchesWord .check (pc,.ADDI .x29 .x0 (BitVec.ofNat 12 (level+1))) ∧
  matchesWord .check (pc+1,.ADDI .x30 .x0 (BitVec.ofNat 12 (levelCalls level))) ∧
  matchesWord .check (pc+2,.ADDI .x31 .x0 (BitVec.ofNat 12 (Pw.bits (level+1)))) ∧ JumpSite (pc+3) 173 .x1
instance (n h : Nat) : Decidable (parentSites n h):=inferInstanceAs (Decidable (_∧_∧_∧_))
def capRegs : List Reg:=[.x8,.x9,.x14,.x15,.x18,.x19,.x20,.x21,.x22,.x23,.x25,.x26]
def CapKeeps (s t : MachineState) :=∀ q∈capRegs,t.getReg q=s.getReg q
theorem CapKeeps.trans {s t u} (a : CapKeeps s t) (b : CapKeeps t u) : CapKeeps s u:=fun q h=>(b q h).trans (a q h)
private theorem saved (q : Reg) (h : q∈capRegs) : parentLive q ∧ q≠.x1 ∧ q≠.x31 ∧ q≠.x30 ∧ q≠.x29 :=by cases q <;> simp_all [capRegs,parentLive]

structure CapHashed (o : Oracle) (s t : MachineState) (pc level dst n : Nat) (raw : Late.Block) : Prop where
  run : Flow o s t n (levelCalls level)
  pc : t.pc=pcAt pc
  value : readBuffer t dst 32=Pw.Auth.compressRow o.compression (level+1) raw
  keep : CapKeeps s t
  frame : ChainOutside s t dst

attribute [local irreducible] readBuffer
theorem cap_hash (o : Oracle) (s : MachineState) (pc level src dst : Nat) (l r c : Late.Digest) (low : level<24) (back : pc+4<2147)
    (sites : parentSites pc level) (ip : s.pc=pcAt pc) (source : s.getReg .x10=W src) (dest : s.getReg .x12=W dst)
    (scratch : s.getReg .x26=W chainBuf) (ss : src+96≤MEMORY_BYTES) (sa : src%8=0) (ds : dst+32≤MEMORY_BYTES) (da : dst%8=0)
    (row : readBuffer s src 96=Pw.Auth.row level l r c) (work : 8≤level ∧ level<16→src=rowBuf) :
    ∃ t n,n≤4+parentFuel level ∧ CapHashed o s t (pc+4) level dst n (Pw.Auth.row level l r c) := by
  let a:=(s.setReg .x29 (W (level+1))).setPC (pcAt (pc+1))
  let b:=(a.setReg .x30 (W (levelCalls level))).setPC (pcAt (pc+2))
  let c':=(b.setReg .x31 (W (Pw.bits (level+1)))).setPC (pcAt (pc+3))
  let z:=(c'.setReg .x1 (pcAt (pc+4))).setPC (pcAt 173)
  obtain ⟨tag,cnt,width,_⟩:=kernel_immediates ⟨level,low⟩
  have xs : Flow o s a 1 0:=imm_step o s pc .x29 .x0 _ _ ip (known sites.1) ((BitVec.zero_add _).trans tag)
  have ys : Flow o a b 1 0:=imm_step o a (pc+1) .x30 .x0 _ _ rfl (known sites.2.1) ((BitVec.zero_add _).trans cnt)
  have zs : Flow o b c' 1 0:=imm_step o b (pc+2) .x31 .x0 _ _ rfl (known sites.2.2.1) ((BitVec.zero_add _).trans width)
  have move:=jump o c' (pc+3) 173 .x1 sites.2.2.2 rfl
  have head : Flow o s z 4 0:=((xs.trans ys).trans zs).trans move
  have keep (q : Reg) (qa : q≠.x1) (qb : q≠.x31) (qc : q≠.x30) (qd : q≠.x29) : z.getReg q=s.getReg q:=by
    have step (u : MachineState) (rd : Reg) (v : Word) (ip : Word) (neq : rd≠q) :
        ((u.setReg rd v).setPC ip).getReg q=u.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ neq)
    exact (step c' .x1 _ _ qa.symm).trans ((step b .x31 _ _ qb.symm).trans ((step a .x30 _ _ qc.symm).trans (step s .x29 _ _ qd.symm)))
  obtain ⟨t,n,lim,result⟩:=parent_node o z level src dst (pc+4) l r c low rfl rfl rfl rfl source dest scratch rfl back ss sa ds da
    ((read_buffer_memory_congr z s rfl _ _).trans row) work
  refine ⟨t,4+n,Nat.add_le_add_left lim _,⟨by simpa only [Nat.zero_add] using head.trans result.run,result.pc,result.value,?_,result.frame⟩⟩
  intro q h;obtain ⟨live,ra,r31,r30,r29⟩:=saved q h;exact (result.keep q live).trans (keep q ra r31 r30 r29)

theorem pair_hash (o : Oracle) (s : MachineState) (dst : Nat) (a b : Late.Digest)
    (ip : s.pc=pcAt 893) (rp : s.getReg .x25=W rowBuf) (dp : s.getReg .x4=W dst)
    (scratch : s.getReg .x26=W chainBuf) (da : dst%8=0) (space : dst+32≤MEMORY_BYTES)
    (row : readBuffer s rowBuf 96=Late.parentBlock a b) :
    ∃ t n,n≤180 ∧ Flow o s t n 16 ∧ t.pc=pcAt 899 ∧
      readBuffer t dst 32=Chained.parentDigest o.compression (Pw.height 15) a b ∧ CapKeeps s t ∧ ChainOutside s t dst := by
  let pc:=893
  have code : matchesWord .check (pc,.ADDI .x10 .x25 0) ∧ matchesWord .check (pc+1,.ADDI .x12 .x4 0) ∧ parentSites (pc+2) 15 := by decide +kernel
  let u:=(s.setReg .x10 (W rowBuf)).setPC (pcAt (pc+1))
  let z:=(u.setReg .x12 (W dst)).setPC (pcAt (pc+2))
  have a₀:=imm_step o s pc .x10 .x25 0 _ ip (known code.1) ((BitVec.add_zero _).trans rp)
  have b₀:=imm_step o u (pc+1) .x12 .x4 0 _ rfl (known code.2.1) ((BitVec.add_zero _).trans dp)
  obtain ⟨t,n,bound,h⟩:=cap_hash o z (pc+2) 15 rowBuf dst a b 0 (by decide) (by decide) code.2.2
    rfl rfl rfl scratch (by decide) (by decide) space da ((read_buffer_memory_congr z s rfl _ _).trans row) (fun _=>rfl)
  refine ⟨t,2+n,by change n≤178 at bound;omega,(a₀.trans b₀).trans h.run,h.pc,
    h.value.trans (Pw.Auth.row_parent o.compression 15 a b 0),?_,h.frame⟩
  intro q hq;apply (h.keep q hq).trans
  have neq : q≠.x12 ∧ q≠.x10:=by cases q <;> simp_all [capRegs]
  exact MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ neq.1.symm).trans
    (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ neq.2.symm)))
end CommitGolfCandidate.Chained.BinaryMachine.Check
