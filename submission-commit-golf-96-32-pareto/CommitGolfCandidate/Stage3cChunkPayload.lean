import CommitGolfCandidate.Stage3cFieldRun
import CommitGolfCandidate.Stage3cPackedWords
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)

def appendedWord (s : MachineState) (k : Nat) :=s.getReg .x23 ||| (s.getMem (s.getReg .x10) <<< k)

structure ChunkPayload (s t : MachineState) (k w : Nat) : Prop where
  memory : t.mem=if k+w<64 then s.mem else (s.setMem (s.getReg .x19) (appendedWord s k)).mem
  held : t.getReg .x23=if k+w<64 then appendedWord s k else if k+w=64 then 0 else s.getMem (s.getReg .x10) >>> (64-k)

private theorem written_imm (used : Nat) (hi : used<128) (lo : 64≤used) :
    W used + signExtend12 4032=W (used-64) := by
  rw [show signExtend12 4032 = -64#64 by decide,←BitVec.sub_eq_add_neg]
  exact BitVec.ofNat_sub_ofNat_of_le _ 64 (by decide) lo

private theorem shift_count (w k : Nat) (sum : 64<k+w) (hk : k<64) (hw : w≤64) :
    ((W w - (W (k+w)+signExtend12 4032)).toNat%64)=64-k := by
  rw [written_imm (k+w) (by omega) (by omega)]
  unfold W
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega),show w-(k+w-64)=64-k by omega,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]

theorem chunk_payload (s : MachineState) (n k : Nat) (npos : 0<n) (nsmall : n≤256) (ksmall : k<64)
    (pc : s.pc=pcAt 21) (remaining : s.getReg .x11=W n) (count : s.getReg .x24=W k) (sixty : s.getReg .x27=64)
    (src : accessValid (s.getReg .x10) 8=true) (dst : accessValid (s.getReg .x19) 8=true) :
    ChunkPayload s (pathEnd s (chunkCode (n<64) (k+min n 64))) k (min n 64) := by
  let short:=decide (n<64);let w:=min n 64;let used:=k+w
  let z:=pathEnd s (fetchWord short);let u:=pathEnd z mix
  have nlim : n<18446744073709551616 := by omega
  have klim : k<18446744073709551616 := by omega
  have wlim : w≤64 := min_le_right .. 
  have bound : used<128 := by dsimp [used];omega
  have positive : s.getReg .x11≠0 := by rw [remaining];intro e;have :=congrArg BitVec.toNat e;simp [W,Nat.mod_eq_of_lt nlim] at this;omega
  obtain ⟨_,fp,word,_,wr,fmem⟩:=fetch_ready s pc positive src short (by rw [remaining];simp [W,short,BitVec.ult,Nat.mod_eq_of_lt nlim])
  have fkeep (r : Reg) (ok : r∈([.x23,.x24,.x27,.x19] : List Reg)) : z.getReg r=s.getReg r := by
    apply path_keeps_reg;cases short <;> cases r <;> first | decide | simp at ok
  have fw : z.getReg .x31=W w := by
    rw [show z.getReg .x31=_ from wr,remaining]
    by_cases h : n<64
    · simp [w,short,h,min_eq_left h.le]
    · simp [w,short,h,min_eq_right (by omega : 64≤n),W]
  obtain ⟨_,up,_,buf,occ,mmem⟩:=mix_ready z fp ((fkeep _ (by decide)).trans sixty)
  have mkeep (r : Reg) (ok : r∈([.x19,.x28,.x31] : List Reg)) : u.getReg r=z.getReg r := by
    apply path_keeps_reg;cases r <;> first | decide | simp at ok
  have data : buffered z=appendedWord s k := by
    unfold buffered appendedWord
    rw [fkeep .x23 (by decide),fkeep .x24 (by decide),count,show z.getReg .x28=_ from word]
    simp [W,Nat.mod_eq_of_lt klim,Nat.mod_eq_of_lt ksmall]
  have usedEq : occupied z=W used := by
    unfold occupied;rw [fkeep _ (by decide),count,fw];exact (BitVec.ofNat_add ..).symm
  have ip : u.pc=pcAt (if used<64 then 21 else 32) := by rw [show u.pc=_ from up,usedEq];simp [W,BitVec.ult,Nat.mod_eq_of_lt (show used<18446744073709551616 by omega)]
  have dstEq : u.getReg .x19=s.getReg .x19 := (mkeep _ (by decide)).trans (fkeep _ (by decide))
  have uMem : u.mem=s.mem:=mmem.trans fmem
  have uHeld : u.getReg .x23=appendedWord s k := buf.trans data
  have uUsed : u.getReg .x24=W used := occ.trans usedEq
  have startEnd : pathEnd s (fetchWord short++mix)=u := end_append ..
  change ChunkPayload s (pathEnd s (chunkCode short used)) k w
  by_cases low : used<64
  · simp only [chunkCode,low,ite_true,List.append_nil,startEnd]
    exact ⟨(if_pos low).symm ▸ uMem,(if_pos low).symm ▸ uHeld⟩
  · have fit : ((u.getReg .x24+signExtend12 4032)==0)=decide (used=64) := by
      rw [uUsed,written_imm used bound (by omega)]
      by_cases eq : used=64
      · simp [W,eq]
      · have ne : W (used-64)≠0#64 := by intro z;have :=congrArg BitVec.toNat z;simp [W,Nat.mod_eq_of_lt (show used-64<18446744073709551616 by omega)] at this;omega
        simp [eq,ne]
    obtain ⟨_,_,_,_,held,mem⟩:=spill_ready u (by simpa [low] using ip) (dstEq ▸ dst) _ fit
    simp only [chunkCode,low,ite_false,end_append,startEnd]
    constructor
    · rw [if_neg (show ¬k+w<64 from low)]
      apply mem.trans;simp only [MachineState.setMem,dstEq,uHeld,uMem]
    · apply held.trans
      rw [if_neg (show ¬k+w<64 from low)]
      by_cases eq : used=64
      · simp [eq,show k+w=64 from eq]
      · simp only [eq,decide_false,Bool.false_eq_true,ite_false,if_neg (show k+w≠64 from eq)]
        rw [mkeep .x28 (by decide),show z.getReg .x28=_ from word,mkeep .x31 (by decide),fw,uUsed]
        exact congrArg (fun z : Nat=>s.getMem (s.getReg .x10) >>> z) (shift_count w k (by change 64<used;omega) ksmall wlim)
end CommitGolfCandidate.Chained.BinaryMachine.Writer
