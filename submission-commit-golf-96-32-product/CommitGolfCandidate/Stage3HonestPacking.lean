import CommitGolfCandidate.Stage3HonestTree
import CommitGolfCandidate.LateHonestFields
import CommitGolfCandidate.TruncCanonical
namespace CommitGolfCandidate.Late.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem highByte (v : Digest) (k : Nat) (lo : 30≤k) (hi : k<32) :
    (Trunc.padLow v).extractLsb' (8*k) 8=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp [Trunc.padLow,BitVec.getLsbD_extractLsb',hb]
  apply (BitVec.getLsbD_append (x:=0#16) (y:=low240 v) (i:=8*k+b)).trans
  rw [if_neg (by omega : ¬8*k+b<240)]
  simp

private theorem fieldByte (x : CheckInput) (a k : Nat) (range : a+k<x.proof.length) (size : x.proof.length=72704) (small : k<32) :
    x.proof[a+k]=(proofAt x a 32).extractLsb' (8*k) 8 := by
  have read:=proof_byte x (a+k) range (by unfold Open.proofBase;omega)
  have bit:=read_buffer_byte (initial x) (Open.proofBase+a) 32 k small
  rw [Nat.add_assoc] at bit
  exact read.symm.trans bit.symm

theorem pack_canonical (H : Compression) (m : Message) (s : SaltTape) (ps : Positions) (batch : ps.card=BATCH) :
    let t:=treeM (M:=Id) H m s
    Trunc.unpack (Trunc.pack (wideOpening t s ps))=wideOpening t s ps := by
  let t:=treeM (M:=Id) H m s
  let x:=canonicalInput m ps t s
  have len : x.proof.length=72704 := by change (wideOpening t s ps).length=_;rw [wide_size,if_pos batch]
  apply Trunc.unpackPack x.proof len
  intro j hj hole
  rcases Trunc.omitted j (len ▸ hj) hole with ⟨r,hr,l,lo,hl,k,kl,hk,rfl⟩|⟨p,hp,k,kl,hk,rfl⟩
  · let ix:=recordIndex ps r
    have depthEq : depth x=16 := by change (if ps.card=BATCH then 16 else 24)=_;rw [if_pos batch]
    have str : start x r=536*r := by unfold start;rw [depthEq];omega
    have sib:=honest_sibling m ps t s r l (by rw [batch];exact hr) (by change l<depth x;rw [depthEq];exact hl)
    change proofAt x (start x r+24+32*l) 32=node t l (Open.mate ix l) at sib
    rw [str] at sib
    obtain ⟨v,eq⟩:=layerIsPadded H m s l (Open.mate ix l) lo (by omega)
      (Open.mate_bound ix l (by change l<24;omega))
    rw [fieldByte x _ k hj len hk,sib,eq,highByte v k kl hk]
  · have slot:=honest_slot m ps t s p batch hp
    change proofAt x (68608+32*p) 32=capSlot t (ps.sort (·≤·)) p at slot
    have cap : ∃ v, capSlot t (ps.sort (·≤·)) p=Trunc.padLow v := by
      unfold capSlot;split
      · exact layerIsPadded H m s 17 p (by decide) (by decide) hp
      · rename_i ix _
        exact layerIsPadded H m s 16 (Open.mate ix 16) (by decide) (by decide) (Open.mate_bound _ _ (by decide))
    obtain ⟨v,eq⟩:=cap
    rw [fieldByte x _ k hj len hk,slot,eq,highByte v k kl hk]

end CommitGolfCandidate.Late.Check
