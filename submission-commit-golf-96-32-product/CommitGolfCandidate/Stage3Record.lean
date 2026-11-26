import CommitGolfCandidate.TruncCheckDigest
import CommitGolfCandidate.S3LateCheckEnter
import CommitGolfCandidate.TruncCap
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W AddrOK)
open CommitGolfCandidate.Late.Check3.Normal (obs Runs compBlock)
open CommitGolfCandidate.Late.Check.Normal (checkEvaluation check_evaluation_pure check_evaluation_public_bind check_evaluation_support)

private theorem pathCalls (o : Oracle) (s : MachineState) (n : Nat) :
    (Late.Check.Normal.checkEvaluation o (Check.rec_checkPathLoop s n)).2=n := by
  induction n generalizing s with
  | zero=>rw [Check.rec_checkPathLoop,Late.Check.Normal.check_evaluation_pure]
  | succ n ih=>
    rw [Check.rec_checkPathLoop,Late.Check.Normal.check_evaluation_public_bind]
    change 1+(Late.Check.Normal.checkEvaluation o (Check.rec_checkPathLoop _ n)).2=n+1;rw [ih];omega

structure RecordEnd (o : Oracle) (s t : MachineState) (d a p : Nat) (i : Index) (digest : Digest) (k : Nat) : Prop where
  run : Late.Check3.Normal.Runs o s t k (4+d)
  bound : k≤55+56*d
  pc : t.pc=5120
  index : t.getReg .x20=W (i.val/2^d)
  proof : t.getReg .x25=W (p+24+32*d)
  value : t.getReg .x8=W (a+256)
  keep : ∀ reg∈[Reg.x19,.x21,.x24,.x26,.x27,.x30],t.getReg reg=s.getReg reg
  high : Late.Check3.Micro.High s t
  data : readBuffer t 256 32=digest

theorem hashPosition (o : Oracle) (s : MachineState) (d a p : Nat) (i : Index) (salt : Late.Salt) (v : Entry)
    (sib : Nat → Digest) (pc : s.pc=4924) (idxOK : accessValid (s.getReg .x24) 8=true)
    (idx : s.getMem (s.getReg .x24)=W i.val) (vp : s.getReg .x8=W a) (pp : s.getReg .x25=W p)
    (sc : s.getReg .x21=256) (depth : s.getReg .x30=W d) (mode : d=16 ∨ d=24)
    (slots : s.getReg .x19=0 ↔ d=24) (va : AddrOK a 256) (pa : AddrOK p (24+32*d))
    (ah : 448≤a) (ph : 448≤p) (val : readBuffer s a 256=v) (sa : readBuffer s p 24=salt)
    (data : ∀ j<d,readBuffer s (p+24+32*j) 32=sib j) :
    ∃ t k, RecordEnd o s t d a p i (recordAncestor o.compression d v salt i sib) k := by
  have dh : d≤24 := by omega
  have pb:=pa.2;have aligned:=pa.1
  obtain ⟨u,k,leaf⟩:=Late.Check3.Micro.rowLeaf o .batch s a p i salt v pc idxOK idx vp pp sc va
    ⟨aligned,by omega⟩ ah ph val sa
  let r:=PairCap.rec_checkPathInitializedState u
  let op:=Check.rec_checkPathLoop r d
  let t:=(Late.Check.Normal.checkEvaluation o op).1
  let nodes:=recordPathPrefix d i sib
  have len : nodes.length=d := record_path_prefix_length .. 
  have scU : u.getReg .x21=256 := (leaf.keep _ (by decide)).trans sc
  have depU : u.getReg .x30=W d := (leaf.keep _ (by decide)).trans depth
  have ctr : r.getReg .x29=W d := depU
  have rc : r.getReg .x21=256 := (PairCap.rec_check_path_setup_register u .x21 (by decide)).trans scU
  have rp : r.getReg .x25=W (p+24) := (PairCap.rec_check_path_setup_register u .x25 (by decide)).trans leaf.proof
  have rx : r.getReg .x20=W i.val := (PairCap.rec_check_path_setup_register u .x20 (by decide)).trans leaf.idx
  have gf : Check.GFrame r d nodes.length := by
    rw [len];refine ⟨ctr,(PairCap.rec_check_path_setup_register u .x30 (by decide)).trans depU,?_⟩
    rw [PairCap.rec_check_path_setup_register u .x19 (by decide),leaf.keep _ (by decide)];exact slots
  have vals (j : Nat) (hj : j<nodes.length) : readBuffer r (p+24+32*j) 32=nodes[j].2 := by
    have fit : j<d := len ▸ hj
    have mem:=Late.read_congr_mem r u (p+24+32*j) 32 rfl
    rw [mem,leaf.high _ _ (by omega) (by omega),data j fit]
    simp only [nodes,recordPathPrefix,List.getElem_map,List.getElem_range]
  have dirs (j : Nat) (hj : j<nodes.length) : (r.getReg .x20).getLsbD j=nodes[j].1 := by
    have fit : j<d := len ▸ hj
    rw [rx,Late.Open.W,BitVec.getLsbD_ofNat];simp [nodes,recordPathPrefix,show j<64 by omega]
  have digest:=Check.rec_check_path_loop_digest o r (p+24) nodes i d mode gf (by rw [len]) rc rp
    (by omega) (by omega) (by rw [len];unfold MEMORY_BYTES at pb;omega) vals dirs
  rw [len,Nat.sub_self,Nat.pow_zero,Nat.div_one] at digest
  have reach:=Late.Check.Normal.check_evaluation_support o op
  have finish:=Check.rec_check_path_loop_finished r d dh ctr t reach
  obtain ⟨pEnd,iEnd,keep⟩:=Check.rec_check_path_loop_registers r d t reach
  have safe (j : Nat) (hj : j<4*d) : accessValid (u.getReg .x25+BitVec.ofNat 64 (8*j)) 8=true := by
    rw [leaf.proof,Late.Open.W,←BitVec.ofNat_add];exact Late.Open.access_at _ (by omega) (by omega)
  have run:=compBlock (s:=u) o (fun f=>Check.rec_check_path_subroutine d dh u leaf.pc depU scU safe f false)
  rw [pathCalls] at run
  let ks:=1+Check.pathInstructions (u.getReg .x20) d
  have carry (reg : Reg) (hr : reg∈[Reg.x8,.x19,.x21,.x24,.x26,.x27,.x30]) : t.getReg reg=u.getReg reg := by
    have nz : reg∉[Reg.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x20,.x25,.x29,.x14,.x15,.x16,.x17,.x31] ∧ reg≠.x29 :=
      (by intro j;cases j <;> decide : ∀ j : Reg,j∈[Reg.x8,.x19,.x21,.x24,.x26,.x27,.x30] → j∉[Reg.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x20,.x25,.x29,.x14,.x15,.x16,.x17,.x31] ∧ j≠.x29) reg hr
    exact (keep reg nz.1).trans (PairCap.rec_check_path_setup_register u reg nz.2)
  refine ⟨t,k+ks,leaf.run.trans run,by have:=leaf.budget;have:=(Check.path_instruction_bounds (u.getReg .x20) d).2;unfold ks;omega,
    finish.2 (by omega),?_,?_,(carry _ (by decide)).trans leaf.value,?_,?_,?_⟩
  · have ub:=i.isLt;change i.val<16777216 at ub
    rw [iEnd,rx,Late.Open.W,Late.Open.shr _ _ (by omega)] <;> rfl
  · rw [pEnd,rp];exact (BitVec.ofNat_add _ _).symm
  · intro reg hr
    have more : reg∈[Reg.x8,.x19,.x21,.x24,.x26,.x27,.x30] := List.mem_cons_of_mem _ hr
    exact (carry reg more).trans (leaf.keep reg hr)
  · have outside : Late.Open.Outside r t 256 64 := by
      intro x hx ax out;apply Check.rec_check_path_loop_outside o r d (W x) rc
      intro j hj e;have z:=congrArg BitVec.toNat e
      simp only [Late.Open.W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at hx;omega : x<2^64),
        Nat.mod_eq_of_lt (by omega : 256+8*j<2^64)] at z
      omega
    exact leaf.high.trans ((Late.Check3.Micro.High.memory (show r.mem=u.mem from rfl)).trans
      (Late.Check3.Micro.high_write outside (by decide) (by decide) (by decide)))
  · exact digest.trans (congrArg (fun w=>climb o.compression (LENGTH+i.val) w nodes)
      ((Late.read_congr_mem r u 256 32 rfl).trans leaf.digest))
end CommitGolfCandidate.Trunc
