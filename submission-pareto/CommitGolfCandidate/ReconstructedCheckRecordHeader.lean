import CommitGolfCandidate.ReconstructedCheckRecordStart
import CommitGolfCandidate.ReconstructedCheckStream
import CommitGolfCandidate.ReconstructedHonestDivision

namespace CommitGolfCandidate.Reconstruction.CheckRecordHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel CheckRecorded CheckRecordStart CheckStream CheckEntry
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 16000
set_option maxHeartbeats 1550000

def model (s : MachineState) : Model := ⟨s.getReg,memoryView s⟩
theorem fits (s : MachineState) : Fits s (model s) := ⟨fun _=>rfl,fun _ _=>rfl⟩

def salt (stream c : Nat) : Words 2 := ![W (HonestStream.get stream c 64),W (HonestStream.get stream (c+64) 56)]
def header (stream c : Nat) := HonestDivision.fromFields (HonestStream.get stream (c+120) 64) (HonestStream.get stream (c+184) 38)
def limbs (s : MachineState) := [(s.getReg .x27).toNat,(s.getReg .x18).toNat,(s.getReg .x20).toNat,(s.getReg .x25).toNat]

private theorem clip (x : Word) (n : Nat) (room : n≤64) : ((x <<< (64-n)) >>> (64-n)).toNat=x.toNat%2^n := by
  rw [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq,
    show 2^64=2^n*2^(64-n) by rw [←pow_add];congr 1;omega,Nat.mul_mod_mul_right,Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

private theorem same_contents (s u : MachineState) (fp ord : Nat) (idx : Index) (msg : Words 32)
    (data : Contents (model s) fp ord idx msg) (memory : ∀ p,u.getMem p=s.getMem p)
    (regs : ∀ r∈CheckHeaderPlan.preserve,u.getReg r=s.getReg r) : Contents (model u) fp ord idx msg := by
  have m (w : Nat) : (model u).mem w=(model s).mem w:=memory _
  refine ⟨⟨data.entry.fpRoom,data.entry.slot,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,data.apart⟩
  · exact (regs .x8 (by decide)).trans data.entry.frame
  · exact (regs .x17 (by decide)).trans data.entry.ordinal
  · exact (m _).trans data.entry.indexRegion
  · exact (m _).trans data.entry.valuesRegion
  · exact (m _).trans data.index
  · exact (m _).trans data.marker
  · intro j;exact (m _).trans (data.message j)
  · exact (regs .x6 (by decide)).trans data.beginCopy
  · exact (regs .x7 (by decide)).trans data.endCopy

theorem complete (o : Oracle) (s : MachineState) (g : Reader) (r : Fin 64) (stream fp ord : Nat) (idx : Index) (msg : Words 32)
    (good : CheckStream.Placed g) (source : CheckStream.Source s g stream) (pc : s.pc=CommitBlocks.addr 122)
    (cursor : s.getReg .x24=W (64*g.block+r.val)) (baseReg : s.getReg .x19=W g.proofBase)
    (data : Contents (model s) fp ord idx msg) :
    let c:=64*g.block+r.val
    ∃ t, Segment o ((CheckHeaderPlan.done r).ticks+218) s t (CheckLeaf.rows o idx (salt stream c) msg) ∧
      t.pc=CommitBlocks.addr 238 ∧ t.getReg .x23=W idx.val+16777216#64 ∧ t.getReg .x24=W (c+222) ∧
      limbs t=header stream c ∧
      let leaf:=leafDigestW 240 (o.permutation (CheckLeafCall.request o idx (salt stream c) msg 1))
      t.getReg .x12=leaf.extractLsb' 0 64 ∧ t.getReg .x13=leaf.extractLsb' 64 64 ∧
      t.getReg .x14=leaf.extractLsb' 128 64 ∧ t.getReg .x11=leaf.extractLsb' 192 64 ∧
      t.getReg .x2=s.getReg .x2 ∧ t.getReg .x8=s.getReg .x8 ∧ t.getReg .x19=s.getReg .x19 ∧
      t.getMem (wordAddress (fp-297))=W ord ∧
      (∀ w,w<2^33→w≠fp-297→(w<fp-295 ∨ fp-14≤w)→t.getMem (wordAddress w)=s.getMem (wordAddress w)) := by
  let c:=64*g.block+r.val
  obtain ⟨u,pre,pos,sl,sh,hl,hh,memory,regs⟩:=CheckStream.header o s g r stream good source pc cursor baseReg
  have keep:=same_contents s u fp ord idx msg data memory regs
  obtain ⟨v,t,run,vf,post,heap,endCursor,h1,h0,h2,h3⟩:=CheckRecordStart.positive o (model u) fp ord idx msg keep u pos (fits u)
  have salts : CheckRecordStart.nonce (model u)=salt stream c := by
    funext i;fin_cases i
    · change u.getReg .x14=W _;rw [←sl];simp
    · change ((u.getReg .x10 <<< (8 : Nat)) >>> (8 : Nat))=W _
      apply BitVec.eq_of_toNat_eq
      change (((u.getReg .x10) <<< (64-56 : Nat)) >>> (64-56 : Nat)).toNat=_
      rw [clip _ 56 (by decide),BitVec.toNat_ofNat,←sh];omega
  rw [salts] at run post
  refine ⟨t,by simpa only [List.nil_append] using compose pre run,post.pc,heap,?_,?_,post.low,post.mid,post.upper,post.high,?_,?_,?_,?_,?_⟩
  · change t.getReg .x24=W (c+222)
    rw [endCursor];change u.getReg .x24+222#64=_
    rw [regs .x24 (by decide),cursor];exact (BitVec.ofNat_add (n:=64) c 222).symm
  · simp only [limbs,header,HonestDivision.fromFields,HonestDivision.limb]
    rw [h3,h2,h1,h0]
    change [((u.getReg .x12 >>> (32 : Nat)) &&& 63#64).toNat,(((u.getReg .x12) <<< (64-32 : Nat)) >>> (64-32 : Nat)).toNat,
      (u.getReg .x11 >>> (32 : Nat)).toNat,(((u.getReg .x11) <<< (64-32 : Nat)) >>> (64-32 : Nat)).toNat] = _
    rw [clip _ 32 (by decide),clip _ 32 (by decide)]
    simp only [BitVec.toNat_and,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    change [(u.getReg .x12).toNat/2^32 &&& (2^6-1),_,_,_]=_
    rw [Nat.and_two_pow_sub_one_eq_mod,←hl,←hh]
    have small:=(u.getReg .x11).isLt
    simp only [List.cons.injEq,and_true]
    repeat' apply And.intro
    all_goals omega
  · rw [post.saved .x2 (by decide),vf.registers];exact regs .x2 (by decide)
  · rw [post.fp,vf.registers];exact regs .x8 (by decide)
  · rw [post.saved .x19 (by decide),vf.registers];exact regs .x19 (by decide)
  ·
    have room:=data.entry.fpRoom
    have rel (w : Nat) (small : w<2^33) (far : w<fp-295 ∨ fp-14≤w) : t.getMem (wordAddress w)=v.getMem (wordAddress w) := by
      apply post.compactFrame
      intro k lower higher clash
      have addresses:=congrArg BitVec.toNat clash
      change (8*w)%2^64=(8*(fp-300)+8*k.val)%2^64 at addresses
      have h:=k.isLt;rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at addresses;omega
    rw [rel (fp-297) (by omega) (Or.inl (by omega))]
    have eq:=vf.memory (fp-297) (by omega)
    change v.getMem (wordAddress (fp-297))=TwoPermutationPrototype.writeWord (model u).mem (fp-297) ((model u).reg .x17) (fp-297) at eq
    rw [eq,TwoPermutationPrototype.writeWord,ite_eq_left rfl];exact keep.entry.ordinal
  · intro w small other far
    have room:=data.entry.fpRoom
    have rel (w : Nat) (small : w<2^33) (far : w<fp-295 ∨ fp-14≤w) : t.getMem (wordAddress w)=v.getMem (wordAddress w) := by
      apply post.compactFrame
      intro k lower higher clash
      have addresses:=congrArg BitVec.toNat clash
      change (8*w)%2^64=(8*(fp-300)+8*k.val)%2^64 at addresses
      have h:=k.isLt;rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at addresses;omega
    rw [rel w small far]
    have eq:=vf.memory w small
    change v.getMem (wordAddress w)=TwoPermutationPrototype.writeWord (model u).mem (fp-297) ((model u).reg .x17) w at eq
    rw [eq,TwoPermutationPrototype.writeWord,ite_eq_right other];exact memory _

theorem positive (o : Oracle) (s : MachineState) (g : Reader) (r : Fin 64) (stream fp ord : Nat) (idx : Index) (msg : Words 32)
    (good : CheckStream.Placed g) (source : CheckStream.Source s g stream) (pc : s.pc=CommitBlocks.addr 122)
    (cursor : s.getReg .x24=W (64*g.block+r.val)) (baseReg : s.getReg .x19=W g.proofBase)
    (data : Contents (model s) fp ord idx msg) :
    let c:=64*g.block+r.val
    ∃ t, Segment o ((CheckHeaderPlan.done r).ticks+218) s t (CheckLeaf.rows o idx (salt stream c) msg) ∧
      t.pc=CommitBlocks.addr 238 ∧ t.getReg .x23=W idx.val+16777216#64 ∧ t.getReg .x24=W (c+222) ∧
      limbs t=header stream c ∧
      let leaf:=leafDigestW 240 (o.permutation (CheckLeafCall.request o idx (salt stream c) msg 1))
      t.getReg .x12=leaf.extractLsb' 0 64 ∧ t.getReg .x13=leaf.extractLsb' 64 64 ∧
      t.getReg .x14=leaf.extractLsb' 128 64 ∧ t.getReg .x11=leaf.extractLsb' 192 64 := by
  obtain ⟨t,seg,pc,heap,advance,limbs,low,mid,up,high,_⟩:=complete o s g r stream fp ord idx msg good source pc cursor baseReg data
  exact ⟨t,seg,pc,heap,advance,limbs,low,mid,up,high⟩

end CommitGolfCandidate.Reconstruction.CheckRecordHeader
