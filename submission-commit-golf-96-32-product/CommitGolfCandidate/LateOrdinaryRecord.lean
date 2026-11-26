import CommitGolfCandidate.LateOrdinaryPath
import CommitGolfCandidate.LateCheckFinish

namespace CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W wordAt indexBase proofBase)
open Micro (High)
attribute [local irreducible] checkEvaluation readBuffer lower

structure RowState (x : CheckInput) (r : Nat) (s : MachineState) : Prop where
  position : s.pc=if r=x.positions.card then 4420 else 4156
  left : s.getReg .x27=W (x.positions.card-r)
  cursor : s.getReg .x24=W (indexBase+8*r)
  value : s.getReg .x8=W (valueBase+256*r)
  proof : s.getReg .x25=W (proofBase+792*r)
  root : s.getReg .x26=W rootBase
  scratch : s.getReg .x21=256
  depth : s.getReg .x30=24
  high : High (initial x) s

structure Hashed (o : Oracle) (x : CheckInput) (r : Nat) (s : MachineState) : Prop where
  pc : s.pc=4352
  index : s.getReg .x20=0
  left : s.getReg .x27=W (x.positions.card-r)
  cursor : s.getReg .x24=W (indexBase+8*r)
  value : s.getReg .x8=W (valueBase+256*(r+1))
  proof : s.getReg .x25=W (proofBase+792*(r+1))
  root : s.getReg .x26=W rootBase
  scratch : s.getReg .x21=256
  depth : s.getReg .x30=24
  high : High (initial x) s
  digest : readBuffer s 256 32=lower o.compression x r 24

theorem hashed (o : Oracle) (x : CheckInput) (s : MachineState) (r : Nat) (st : RowState x r s)
    (hr : r<x.positions.card) (normal : x.positions.card≠BATCH) :
    ∃ t n,n≤1236 ∧ Runs o s t n 28 ∧ Hashed o x r t := by
  let i:=recordIndex x.positions r
  let v:=recordValue x r
  let a:=valueBase+256*r
  let p:=proofBase+792*r
  have k : x.positions.card≤LENGTH := by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at k
  have pc : s.pc=4156 := st.position.trans (if_neg (Nat.ne_of_lt hr))
  have fits : indexBase+8*r+8≤MEMORY_BYTES ∧ valueBase+256*r+256≤MEMORY_BYTES ∧ proofBase+792*r+792≤MEMORY_BYTES := by
    unfold indexBase valueBase proofBase MEMORY_BYTES;omega
  have va : Open.AddrOK a 256 := ⟨by unfold a valueBase;omega,fits.2.1⟩
  have pr : Open.AddrOK p 792 := ⟨by unfold p proofBase;omega,fits.2.2⟩
  have ah : 448≤a := by unfold a valueBase;omega
  have ph : 448≤p := by unfold p proofBase;omega
  have idxAl : (indexBase+8*r)%8=0 := by unfold indexBase;omega
  have safe : accessValid (s.getReg .x24) 8=true := by rw [st.cursor];exact Open.access_at _ fits.1 idxAl
  have ix : s.getMem (s.getReg .x24)=W i.val := by
    rw [st.cursor];exact (st.high.word _ idxAl (by unfold indexBase;omega) fits.1).trans (loaded_index x r hr)
  have fixed : start x r=792*r := by unfold start stride;rw [if_neg normal];omega
  have saltR : readBuffer s p 24=salt x r := by
    rw [st.high _ _ ph (by have :=pr.2;omega),salt,fixed];rfl
  have valueR : readBuffer s a 256=v := (st.high _ _ ah va.2).trans (loaded_value x r hr)
  obtain ⟨u,n,leafEnd⟩:=Micro.rowLeaf o .normal s a p i (salt x r) v pc safe ix st.value st.proof st.scratch va
    ⟨pr.1,by have :=pr.2;omega⟩ ah ph valueR saltR
  have high:=st.high.trans leafEnd.high
  have pathAddr : Open.AddrOK (p+24) 768 := ⟨by have :=pr.1;omega,by have :=pr.2;omega⟩
  have pathData (j : Nat) (hj : j<24) : readBuffer u (p+24+32*j) 32=sibling x r j := by
    rw [high _ _ (by omega) (by have :=pr.2;omega),sibling,if_neg (fun h => normal h.1),fixed]
    unfold proofAt p
    rw [show proofBase+792*r+24+32*j=proofBase+(792*r+24+32*j) by omega]
    rfl
  obtain ⟨t,d,done⟩:=fullPath o u (p+24) i (sibling x r) leafEnd.pc
    ((leafEnd.keep _ (by decide)).trans st.depth) ((leafEnd.keep _ (by decide)).trans st.scratch)
    leafEnd.proof leafEnd.idx pathAddr (by omega) pathData
  refine ⟨t,n+d,by have :=leafEnd.budget;have :=done.budget;omega,leafEnd.run.trans done.runs,
    done.pc,done.index,?_,?_,?_,?_,?_,?_,?_,high.trans done.high,?_⟩
  · exact (done.keep _ (by decide)).trans ((leafEnd.keep _ (by decide)).trans st.left)
  · exact (done.keep _ (by decide)).trans ((leafEnd.keep _ (by decide)).trans st.cursor)
  · exact (done.keep _ (by decide)).trans (leafEnd.value.trans (congrArg W (by dsimp [a];omega)))
  · exact done.proof.trans (congrArg W (by dsimp [p];omega))
  · exact (done.keep _ (by decide)).trans ((leafEnd.keep _ (by decide)).trans st.root)
  · exact (done.keep _ (by decide)).trans ((leafEnd.keep _ (by decide)).trans st.scratch)
  · exact (done.keep _ (by decide)).trans ((leafEnd.keep _ (by decide)).trans st.depth)
  · unfold lower
    exact done.digest.trans (congrArg (fun z=>climbAt o.compression 0 z (path i 24 (sibling x r))) leafEnd.digest)

theorem rowStart (x : CheckInput) (normal : x.positions.card≠BATCH) (size : x.proof.length=x.positions.card*792) :
    RowState x 0 (Micro.normalRows (initial x)) := by
  let s:=initial x
  have card : x.positions.card≤LENGTH := by simpa using Finset.card_le_univ x.positions
  have rd : s.getReg .x16=W x.positions.card := rfl
  have bound : x.positions.card<2^64 := by change x.positions.card≤16777216 at card;omega
  have nz : s.getReg .x16≠128 := by
    rw [rd];intro e;apply normal
    have z:=congrArg BitVec.toNat e
    rw [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] at z
    exact z.trans (by decide)
  have idem : W x.positions.card=0 ↔ x.positions.card=0 := by
    constructor
    · intro e;have z:=congrArg BitVec.toNat e
      rw [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] at z
      exact z.trans (by decide)
    · intro e;rw [e];rfl
  have q : s.getReg .x16*792=s.getReg .x17 := by
    change BitVec.ofNat 64 x.positions.card*BitVec.ofNat 64 792=BitVec.ofNat 64 x.proof.length
    rw [size,BitVec.ofNat_mul]
  obtain ⟨_,h⟩:=Micro.normalHeader s rfl nz q
  refine ⟨?_,h.left,h.idx,h.value,h.proof,h.root,h.scratch,h.depth,Micro.High.memory h.mem⟩
  rw [h.pc,rd];by_cases z:x.positions.card=0
  · rw [if_pos (idem.mpr z),if_pos z.symm];rfl
  · rw [if_neg (fun e=>z (idem.mp e)),if_neg (Ne.symm z)];rfl

end CommitGolfCandidate.Late.Check.Normal
