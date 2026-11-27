import CommitGolfCandidate.Stage3cWriter
import CommitGolfCandidate.Stage3cOpeningCost
import CommitGolfCandidate.Stage3cOpenFrame
import CommitGolfCandidate.Stage3cOpenCode
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def chunkCode (short : Bool) (used : Nat) : PathCode :=
  fetchWord short ++ mix ++ if used<64 then [] else spill (used=64)

private theorem ready_append {s : MachineState} {xs ys : PathCode} (x : pathReady s xs) (y : pathReady (pathEnd s xs) ys) :
    pathReady s (xs++ys) := by
  induction xs generalizing s with
  | nil=>exact y
  | cons v xs ih=> exact ⟨x.1,x.2.1,x.2.2.1,ih x.2.2.2 y⟩

theorem end_append (s : MachineState) (xs ys : PathCode) :
    pathEnd s (xs++ys)=pathEnd (pathEnd s xs) ys := by
  induction xs generalizing s with
  | nil=>rfl
  | cons v xs ih=>exact ih _

private theorem fetch_keeps (s : MachineState) (b : Bool) (r : Reg) (keep : r≠.x10 ∧ r≠.x28 ∧ r≠.x31) :
    (pathEnd s (fetchWord b)).getReg r=s.getReg r := by
  apply path_keeps_reg
  cases b <;> cases r <;> first | decide | simp at keep

private theorem mix_keeps (s : MachineState) (r : Reg) (keep : r≠.x11 ∧ r≠.x29 ∧ r≠.x23 ∧ r≠.x24) :
    (pathEnd s mix).getReg r=s.getReg r := by
  apply path_keeps_reg
  cases r <;> first | decide | simp at keep

private theorem chunk_sites (short : Bool) (used : Nat) : (chunkCode short used).all (matchesWord .opening) := by
  simp only [chunkCode,List.all_append,fetch_sites,mix_sites,Bool.true_and]
  split <;> first | rfl | exact spill_sites _

structure ChunkProgress (s t : MachineState) (n k : Nat) : Prop where
  pc : t.pc=pcAt 21
  remaining : t.getReg .x11=BitVec.ofNat 64 (n-min n 64)
  bits : t.getReg .x24=BitVec.ofNat 64 ((k+min n 64)%64)
  source : t.getReg .x10=s.getReg .x10+8
  dest : t.getReg .x19=if k+min n 64<64 then s.getReg .x19 else s.getReg .x19+8

theorem chunk_run (s : MachineState) (pc : s.pc=pcAt 21) (n k : Nat) (hn : 0<n) (nBound : n≤256) (hk : k<64)
    (remaining : s.getReg .x11=BitVec.ofNat 64 n) (bits : s.getReg .x24=BitVec.ofNat 64 k) (threshold : s.getReg .x27=64)
    (src : accessValid (s.getReg .x10) 8=true) (dst : accessValid (s.getReg .x19) 8=true) :
    let code:=chunkCode (n<64) (k+min n 64)
    pathReady s code ∧ Open.Runs s (pathEnd s code) code.length code.length ∧ ChunkProgress s (pathEnd s code) n k := by
  let short := decide (n<64)
  let width := min n 64
  let used := k+width
  let t:=pathEnd s (fetchWord short)
  let u:=pathEnd t mix
  have below : n<2^64 := by omega
  have wBound : width≤64 := Nat.min_le_right .. 
  have uBound : used<2^64 := by dsimp [used];omega
  have npos : s.getReg .x11≠0 := by rw [remaining];intro eq;have h:=congrArg BitVec.toNat eq;simp [Nat.mod_eq_of_lt below] at h;omega
  have f:=fetch_ready s pc npos src short (by rw [remaining];simp [BitVec.ult,short,Nat.mod_eq_of_lt (show n<18446744073709551616 by omega)])
  obtain ⟨rf,pt,_,nextSource,wt,_⟩:=f
  have widthReg : t.getReg .x31=BitVec.ofNat 64 width := by
    rw [show t.getReg .x31=_ from wt,remaining]
    by_cases h : n<64
    · simp [short,width,h,min_eq_left h.le]
    · simp [short,width,h,min_eq_right (Nat.le_of_not_lt h)]
  have mixRun:=mix_ready t pt ((fetch_keeps s short .x27 (by decide)).trans threshold)
  obtain ⟨rm,pu,rem,_,count,_⟩:=mixRun
  have occ : occupied t=BitVec.ofNat 64 used := by
    unfold occupied;rw [fetch_keeps s short .x24 (by decide),bits,widthReg,←BitVec.ofNat_add]
  have pos : u.pc=pcAt (if used<64 then 21 else 32) := by
    rw [show u.pc=_ from pu,occ];simp [BitVec.ult,Nat.mod_eq_of_lt (show used<18446744073709551616 by omega)]
  have data : u.getReg .x24=BitVec.ofNat 64 used := count.trans occ
  have dvalid : accessValid (u.getReg .x19) 8=true := by
    rw [show u.getReg .x19=t.getReg .x19 from mix_keeps t .x19 (by decide),fetch_keeps s short .x19 (by decide)];exact dst
  have main : pathReady s (fetchWord short++mix) := ready_append rf rm
  have eq : pathEnd s (fetchWord short++mix)=u := end_append ..
  have remainder : u.getReg .x11=BitVec.ofNat 64 (n-width) := by
    rw [show u.getReg .x11=_ from rem,fetch_keeps s short .x11 (by decide),remaining,widthReg]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (min_le_left ..)
  have input : u.getReg .x10=s.getReg .x10+8 := (mix_keeps t .x10 (by decide)).trans nextSource
  have dest : u.getReg .x19=s.getReg .x19 := (mix_keeps t .x19 (by decide)).trans (fetch_keeps s short .x19 (by decide))
  have ok : pathReady s (chunkCode short used) ∧ ChunkProgress s (pathEnd s (chunkCode short used)) n k := by
    by_cases low : used<64
    · simp only [chunkCode,low,if_true,List.append_nil,eq]
      exact ⟨main,by simpa [low] using pos,remainder,by change u.getReg .x24=BitVec.ofNat 64 (used%64);rw [Nat.mod_eq_of_lt low];exact data,input,by change u.getReg .x19=if used<64 then _ else _;rw [if_pos low];exact dest⟩
    · have fit : ((u.getReg .x24+signExtend12 4032)==0)=decide (used=64) := by
        have imm : signExtend12 4032= -64#64 := by decide
        rw [data,imm,←BitVec.sub_eq_add_neg]
        rw [show (64#64 : Word)=BitVec.ofNat 64 64 by rfl,BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
        by_cases hit : used=64
        · simp [hit]
        · have h : BitVec.ofNat 64 (used-64)≠0#64 := by intro z; have h:=congrArg BitVec.toNat z;simp [Nat.mod_eq_of_lt (show used-64<2^64 by omega)] at h;omega
          simp [hit,h]
      obtain ⟨sp,last,dptr,finalBits,_,_⟩:=spill_ready u (by simpa [low] using pos) dvalid _ fit
      simp only [chunkCode,low,if_false]
      refine ⟨ready_append main (eq ▸ sp),?_⟩
      rw [end_append,eq]
      have keep (r : Reg) (h : r=.x10 ∨ r=.x11) :
          (pathEnd u (spill (used=64))).getReg r=u.getReg r := by
        apply path_keeps_reg
        have f : ∀ b : Bool, ∀ x : Reg, x=.x10 ∨ x=.x11 → (spill b).all (fun z=>keepsReg x z.2) := by intro b x hx;rcases hx with rfl|rfl <;> cases b <;> decide
        exact f _ _ h
      refine ⟨last,(keep _ (Or.inr rfl)).trans remainder,?_,(keep _ (Or.inl rfl)).trans input,?_⟩
      · rw [finalBits,data,show signExtend12 4032= -64#64 by decide,←BitVec.sub_eq_add_neg]
        rw [show (64#64 : Word)=BitVec.ofNat 64 64 by rfl,BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
        apply congrArg (BitVec.ofNat 64);change used-64=used%64;dsimp [used] at *;omega
      · rw [if_neg low,dptr,dest]
  exact ⟨ok.1,path_run _ _ _ _ (chunk_sites ..) ok.1,ok.2⟩
end CommitGolfCandidate.Chained.BinaryMachine.Writer
