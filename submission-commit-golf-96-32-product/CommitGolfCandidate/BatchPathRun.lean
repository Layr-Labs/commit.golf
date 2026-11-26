import CommitGolfCandidate.LateCheckEnter
import CommitGolfCandidate.PairPathValue
import CommitGolfCandidate.BatchModel

namespace CommitGolfCandidate.PairCap.BatchPath
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W wordAt indexBase proofBase)
open CommitGolfCandidate.Late
open CommitGolfCandidate.Late.Check (path)
open CommitGolfCandidate.Late.Check.Micro (High)
open CommitGolfCandidate.Late.Check.Normal (checkEvaluation check_evaluation_pure check_evaluation_public_bind check_evaluation_support pathInstructions path_instruction_bounds compBlock Runs)
attribute [local irreducible] rec_checkPathPreparedState rec_checkPathLoop checkEvaluation

private theorem pathQueries (o : Oracle) (s : MachineState) (n : Nat) : (checkEvaluation o (rec_checkPathLoop s n)).2=n := by
  induction n generalizing s with
  | zero => rw [rec_checkPathLoop,check_evaluation_pure]
  | succ n ih =>rw [rec_checkPathLoop,check_evaluation_public_bind];change 1+(checkEvaluation o (rec_checkPathLoop _ n)).2=n+1;rw [ih];omega

private theorem pathHigh (o : Oracle) (s : MachineState) (n : Nat) (scratch : s.getReg .x21=256) :
    High s (checkEvaluation o (rec_checkPathLoop s n)).1 := by
  have out : Open.Outside s (checkEvaluation o (rec_checkPathLoop s n)).1 256 64 := by
    intro a ha al away
    apply rec_check_path_loop_outside o s n (W a) scratch
    intro j hj e
    have z:=congrArg BitVec.toNat e
    simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a<2^64 by unfold MEMORY_BYTES at ha;omega),
      Nat.mod_eq_of_lt (show 256+8*j<2^64 by omega)] at z
    omega
  exact Late.Check.Micro.high_write out (by decide) (by decide) (by decide)

structure PathEnd (o : Oracle) (s t : MachineState) (i : Index) (p : Nat) (d : Digest) (n : Nat) : Prop where
  pc : t.pc=5120
  index : t.getReg .x20=W (i.val/65536)
  proof : t.getReg .x25=W (p+512)
  keep : ∀ reg∈[Reg.x8,.x19,.x21,.x24,.x26,.x27,.x30], t.getReg reg=s.getReg reg
  digest : readBuffer t 256 32=d
  high : High s t
  runs : Runs o s t n 16
  budget : n≤721

theorem fullPath (o : Oracle) (s : MachineState) (p : Nat) (i : Index) (siblings : Nat → Digest)
    (pc : s.pc=4968) (depth : s.getReg .x30=16) (scratch : s.getReg .x21=256)
    (pf : s.getReg .x25=W p) (idx : s.getReg .x20=W i.val)
    (bounds : Open.AddrOK p 512) (high : 448≤p)
    (data : ∀ j<16,readBuffer s (p+32*j) 32=siblings j) :
    ∃ t n, PathEnd o s t i p (climb o.compression (readBuffer s 256 32) (path i 16 siblings)) n := by
  let r:=rec_checkPathInitializedState s
  let result:=checkEvaluation o (rec_checkPathLoop r 16)
  let t:=result.1
  let nodes:=path i 16 siblings
  have nLen : nodes.length=16 := by simp [nodes,path]
  have sc : r.getReg .x21=256 := (rec_check_path_setup_register s .x21 (by decide)).trans scratch
  have ptr : r.getReg .x25=W p := (rec_check_path_setup_register s .x25 (by decide)).trans pf
  have ix : r.getReg .x20=W i.val := (rec_check_path_setup_register s .x20 (by decide)).trans idx
  have ub : p+512<2^64 := by have :=bounds.2;unfold MEMORY_BYTES at this;omega
  have di : ∀ j (hj : j<nodes.length), (r.getReg .x20).getLsbD j=nodes[j].1 := by
    intro j hj
    have fit : j<16 := nLen ▸ hj
    rw [ix,W,BitVec.getLsbD_ofNat];simp [nodes,path,show j<64 by omega]
  have dg:=rec_check_path_loop_digest o r p nodes sc ptr bounds.1 (by omega) (by rw [nLen];omega) (by
    intro j hj
    have d:=data j (nLen ▸ hj)
    change readBuffer s (p+32*j) 32=_
    simpa only [nodes,path,List.getElem_map,List.getElem_range] using d) di
  rw [nLen] at dg
  have reached:=check_evaluation_support o (rec_checkPathLoop r 16)
  have done:=rec_check_path_loop_finished r 16 (by decide) depth t reached
  obtain ⟨dp,idx2,keeps⟩:=rec_check_path_loop_registers r 16 t reached
  have ib : i.val<2^64 := by have v:=i.isLt;change i.val<16777216 at v;omega
  have doneIdx : t.getReg .x20=W (i.val/65536) := by rw [idx2,ix,Open.W,Open.shr _ _ ib];rfl
  have safe (j : Nat) (hj : j<4*16) : accessValid (s.getReg .x25+BitVec.ofNat 64 (8*j)) 8=true := by
    rw [pf,W,←BitVec.ofNat_add];exact Open.access_at _ (by have :=bounds.2;omega) (by have :=bounds.1;omega)
  let n:=1+pathInstructions (s.getReg .x20) 16
  have run:=compBlock (s:=s) o (fun f=>rec_check_path_subroutine 16 (by decide) s pc depth scratch safe f false)
  rw [pathQueries] at run
  refine ⟨t,n,done.2 (by decide),doneIdx,?_,?_,dg,?_,run,?_⟩
  · rw [dp,ptr];exact (BitVec.ofNat_add _ _).symm
  · intro reg hr
    have ok : reg ∉ [Reg.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x20,.x25,.x29,.x14,.x15,.x16,.x17,.x31] ∧ reg≠.x29 :=
      (by intro r;cases r <;> decide : ∀ reg : Reg, reg∈[Reg.x8,.x19,.x21,.x24,.x26,.x27,.x30] → reg ∉ [Reg.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x20,.x25,.x29,.x14,.x15,.x16,.x17,.x31] ∧ reg≠.x29) reg hr
    exact (keeps reg ok.1).trans (rec_check_path_setup_register s reg ok.2)
  · exact (Late.Check.Micro.High.memory (show r.mem=s.mem from rfl)).trans (pathHigh o r 16 sc)
  · have b:=(path_instruction_bounds (s.getReg .x20) 16).2;dsimp only [n];omega

end CommitGolfCandidate.PairCap.BatchPath
