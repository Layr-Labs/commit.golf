import CommitGolfCandidate.S5CheckRowSites
import CommitGolfCandidate.S5CheckCursor
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
private theorem argument_kept (s : MachineState) (p : RowSite) (q : Reg) (h : q∉([.x10,.x12,.x29,.x30,.x31] : List Reg)) :
    ((p.hashOps.foldl Sym.bump Sym.original) q).eval s=s.getReg q:=by cases q <;> first | (exfalso;apply h;decide) | rfl
def callKeep (q : Reg) := parentLive q ∧ q≠.x1
private theorem call_safe (q : Reg) (h : callKeep q) : q∉([.x10,.x12,.x29,.x30,.x31] : List Reg):=by cases q <;> simp_all [parentLive,callKeep]

private structure CallReady (o : Oracle) (s z : MachineState) (p : RowSite) : Prop where
  run : Flow o s z 6 0
  pc : z.pc=pcAt 173
  ret : z.getReg .x1=pcAt (p.hashPC+6)
  src : z.getReg .x10=W rowBuf
  dst : z.getReg .x12=W digestBuf
  count : z.getReg .x30=W (levelCalls p.height.val)
  width : z.getReg .x31=W (S5.bits (p.height.val+1))
  level : z.getReg .x29=W (p.height.val+1)
  mem : z.mem=s.mem
  keep : ∀ q,callKeep q→z.getReg q=s.getReg q

private theorem call_sites : ∀ p : RowSite,p.allowed=true →
    matchesWord .check (p.hashPC,.ADDI .x10 .x25 0) ∧ matchesWord .check (p.hashPC+1,.ADDI .x12 .x27 0) ∧
    matchesWord .check (p.hashPC+2,.ADDI .x29 .x0 (BitVec.ofNat 12 (p.height.val+1))) ∧
    matchesWord .check (p.hashPC+3,.ADDI .x30 .x0 (BitVec.ofNat 12 (levelCalls p.height.val))) ∧
    matchesWord .check (p.hashPC+4,.ADDI .x31 .x0 (BitVec.ofNat 12 (S5.bits (p.height.val+1)))) := by decide +kernel

private def setArg (s : MachineState) (r : Reg) (v : Word) (next : Nat) := (s.setReg r v).setPC (pcAt next)
private theorem keep_arg (s : MachineState) (r : Reg) (v : Word) (next : Nat) (q : Reg) (ne : r≠q) :
    (setArg s r v next).getReg q=s.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne)
private theorem args_keep (s : MachineState) (n : Nat) (tag amount bits : Word) (q : Reg) (safe : callKeep q) :
    (setArg (setArg (setArg (setArg (setArg (setArg s .x10 (W rowBuf) (n+1)) .x12 (W digestBuf) (n+2))
      .x29 tag (n+3)) .x30 amount (n+4)) .x31 bits (n+5)) .x1 (pcAt (n+6)) 173).getReg q=s.getReg q := by
  cases q <;> first | (exfalso;apply safe.1;decide) | (exfalso;exact safe.2 rfl) | rfl
private theorem prepare_row_call (o : Oracle) (s : MachineState) (p : RowSite) (allowed : p.allowed=true)
    (pc : s.pc=pcAt p.hashPC) (row : s.getReg .x25=W rowBuf) (out : s.getReg .x27=W digestBuf) : ∃ z,CallReady o s z p := by
  let n:=p.hashPC
  let a:=setArg s .x10 (W rowBuf) (n+1)
  let b:=setArg a .x12 (W digestBuf) (n+2)
  let c:=setArg b .x29 (W (p.height.val+1)) (n+3)
  let d:=setArg c .x30 (W (levelCalls p.height.val)) (n+4)
  let e:=setArg d .x31 (W (S5.bits (p.height.val+1))) (n+5)
  let z:=setArg e .x1 (pcAt (n+6)) 173
  obtain ⟨wa,wb,wc,wd,we⟩:=call_sites p allowed
  obtain ⟨tag,cnt,width,_⟩:=kernel_immediates p.height
  have ra : Flow o s a 1 0:=imm_step o s n .x10 .x25 0 _ pc (known wa) ((BitVec.add_zero _).trans row)
  have rb : Flow o a b 1 0:=imm_step o a (n+1) .x12 .x27 0 _ rfl (known wb) ((BitVec.add_zero _).trans out)
  have rc : Flow o b c 1 0:=imm_step o b (n+2) .x29 .x0 _ _ rfl (known wc) ((BitVec.zero_add _).trans tag)
  have rd : Flow o c d 1 0:=imm_step o c (n+3) .x30 .x0 _ _ rfl (known wd) ((BitVec.zero_add _).trans cnt)
  have re : Flow o d e 1 0:=imm_step o d (n+4) .x31 .x0 _ _ rfl (known we) ((BitVec.zero_add _).trans width)
  have rz : Flow o e z 1 0:=jump o e (n+5) 173 .x1 (row_sites p allowed).2.2.2.2.1 rfl
  have left:=(ra.trans rb).trans rc
  have flow:=((left.trans rd).trans re).trans rz
  exact ⟨z,⟨flow,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,args_keep s n _ _ _⟩⟩

attribute [local irreducible] readBuffer S5.Auth.compressRow
theorem row_hash (o : Oracle) (s : MachineState) (p : RowSite) (j : Nat) (v : Late.Digest) (peers : S5.Peers)
    (allowed : p.allowed=true) (pc : s.pc=pcAt p.hashPC) (row : s.getReg .x25=W rowBuf)
    (scratch : s.getReg .x26=W chainBuf) (out : s.getReg .x27=W digestBuf)
    (data : CellData s (pickedCells p.height.val j v peers)) :
    ∃ t steps,steps≤6+parentFuel p.height.val ∧ Flow o s t steps (levelCalls p.height.val) ∧
      t.pc=pcAt (rowPC p.batch (p.height.val+1)) ∧ (∀ q,callKeep q→t.getReg q=s.getReg q) ∧ RowFrame s t ∧
      readBuffer t digestBuf 32=S5.Auth.compressRow o.compression (p.height.val+1) (S5.payload (S5.lane p.height.val j) v peers) := by
  obtain ⟨z,prep⟩:=prepare_row_call o s p allowed pc row out
  let g:=pickedCells p.height.val j v peers
  obtain ⟨r,eq⟩:=assembled_row s p.height.val j v peers data
  have zmem : z.mem=s.mem:=prep.mem
  have limit : p.hashPC+6<2336:= (by decide +kernel : ∀ q : RowSite,q.hashPC+6<2336) p
  obtain ⟨t,n,price,next⟩:=parent_node o z p.height.val rowBuf digestBuf (p.hashPC+6) (g 0) (g 1) (g 2) p.height.isLt prep.pc
    prep.count prep.width prep.level prep.src prep.dst ((prep.keep _ (by simp [callKeep,parentLive])).trans scratch)
    prep.ret limit (by decide) (by decide) (by decide) (by decide) ((read_buffer_memory_congr z s zmem _ _).trans r) (fun _=>rfl)
  refine ⟨t,6+n,by omega,by simpa only [Nat.zero_add] using prep.run.trans next.run,next.pc.trans (congrArg pcAt (row_sites p allowed).2.2.2.2.2.1),
    fun q h=>(next.keep q h.1).trans (prep.keep q h),?_,?_⟩
  · intro q h al far;apply (next.frame q h al (by omega) (by change q<65792 ∨ 65792+544≤q at far;change q<66304 ∨ 66304+32≤q;omega)).trans (congrFun zmem _)
  · exact next.value.trans (congrArg (S5.Auth.compressRow o.compression _) eq)
end CommitGolfCandidate.S5Machine.Check
