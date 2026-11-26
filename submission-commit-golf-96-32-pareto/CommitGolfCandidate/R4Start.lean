import CommitGolfCandidate.R4CommitLeaf
import CommitGolfCandidate.R4LaneCode
import CommitGolfCandidate.LateCachedTree
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Late (pcAt LevelsThrough Gaps sharedSaltAddr)
abbrev Coins := Fin (LENGTH/2) → PairRand
def baseLeaf (H : Compression) (m : Message) (r : Coins) (i : Nat) := (Late.initialList H m (pairSalts r))[i]?.getD 0

structure Seed (m : Message) (r : Coins) (s : MachineState) : Prop where
  pc : s.pc=pcAt 1051
  db : s.getReg .x2=Z C_DB
  mode : s.getReg .x5=0
  msg : s.getReg .x8=Z C_MSG
  td : s.getReg .x9=Z C_TD
  input : s.getReg .x10=Z (C_MSG-256)
  width : s.getReg .x11=96
  kind : s.getReg .x13=0
  row : s.getReg .x18=Z C_ROW
  endAddr : s.getReg .x19=Z (C_MSG+2^32-256)
  root : s.getReg .x26=Z C_CMT
  salts : ∀ j : Fin (LENGTH/2),readBuffer s (C_ROW+184*j.val+72) 24=pairSaltEven (r j) ∧
      readBuffer s (C_ROW+184*j.val+88) 24=pairSaltOdd (r j)
  mem : ∀ q,q<2^64 → (∀ j<LENGTH/2,q<C_ROW+184*j+72 ∨ C_ROW+184*j+112≤q) →
      s.getByte (Z q)=(submission.initialState .commit m).getByte (Z q)

attribute [local irreducible] List.finRange

private theorem sameLeaf (H : Compression) (i : Index) (s : Late.Salt) (v : Entry) :
    leafDigest (fun x=>H x) i s v=LateHiding.leafDigest H (i.val.testBit 0) s v := by
  let a:=leafA (fun x=>H x) v
  let b:=leafB (fun x=>H x) v
  change H (leafFinalInput i a b s)=H (Late.finalBlock (i.val.testBit 0) s a b)
  apply congrArg H
  by_cases h : i.val%2=0
  · have z : i.val.testBit 0=false:=by simp [Nat.testBit_eq_decide_div_mod_eq,h]
    simp only [leafFinalInput,if_pos h,Late.finalBlock,z,Bool.false_eq_true,ite_false,leafFinalEven]
    simp only [BitVec.append_assoc,BitVec.cast_eq,ite_true,ite_false] <;> rfl
  · have z : i.val.testBit 0=true:=by simp [Nat.testBit_eq_decide_div_mod_eq,show i.val%2=1 by omega]
    simp only [leafFinalInput,if_neg h,Late.finalBlock,z,ite_true,leafFinalOdd]
    simp only [BitVec.append_assoc,BitVec.cast_eq,ite_true,ite_false] <;> rfl

private theorem lookupLeaf (H : Compression) (m : Message) (r : Coins) (i : Index) :
    baseLeaf H m r i.val=LateHiding.leafDigest H (i.val.testBit 0) (pairSalts r i) (m i):=by
  have hit : (List.finRange LENGTH)[i.val]?=some i:=by
    rw [List.getElem?_eq_getElem (by simpa using i.isLt),List.getElem_finRange];rfl
  unfold baseLeaf Late.initialList LateHiding.leafLayer
  rw [List.getElem?_map,hit];rfl

private theorem leaf_agrees (H : Compression) (m : Message) (r : Coins) (i : Nat) (inside : i<LENGTH) :
    nodeVal (fun x=>H x) m (pairSalts r) 0 i=baseLeaf H m r i := by
  let idx : Index:=⟨i,inside⟩
  have node : nodeVal (fun x=>H x) m (pairSalts r) 0 i=leafDigest (fun x=>H x) idx (pairSalts r idx) (m idx):=by
    change (if h : i<LENGTH then leafDigest (fun x=>H x) ⟨i,h⟩ (pairSalts r ⟨i,h⟩) (m ⟨i,h⟩) else 0)=_
    rw [dif_pos inside]
  exact node.trans ((sameLeaf _ idx _ _).trans (lookupLeaf H m r idx).symm)

theorem start (o : Oracle) (m : Message) (r : Coins) (s : MachineState) (seed : Seed m r s) :
    ∃ t,MRun o s 201588752 t 671350800 67108864 ∧ t.pc=pcAt 3374 ∧ Env t ∧
      LevelsThrough o.compression (baseLeaf o.compression m r) 0 t ∧ Gaps t ∧
      ∀ i : Index,readBuffer t (sharedSaltAddr i) 24=pairSalts r i := by
  have htd : C_TD=4294971424:=rfl
  have hr : C_ROW=5905584160:=rfl
  have hmsg : C_MSG=4096:=rfl
  have readM (i : Index) (j : Nat) (hj : j<256) : s.getByte (Z (C_MSG+256*i.val+j))=(m i).extractLsb' (8*j) 8:=by
    have hi : i.val<16777216:=i.isLt
    rw [seed.mem _ (by omega) (fun _ _=>Or.inl (by omega))]
    exact commit_initial_msg_byte m i j hj 
  have zero (q : Nat) (lo : C_TD≤q) (hi : q<C_ROW) : s.getByte (Z q)=0:=by
    rw [seed.mem _ (by omega) (fun _ _=>Or.inl (by omega))]
    apply commit_initial_zero_byte;omega
  have empty (j : Fin (LENGTH/2)) (off : Nat) (ofst : off=64 ∨ off=112) : readBuffer s (C_ROW+184*j.val+off) 8=0:=by
    have bd : j.val<8388608:=j.isLt
    apply readBuffer_zero_of_bytes;intro k hk
    rw [seed.mem _ (by rcases ofst with rfl|rfl <;> omega) (fun p _=>by by_cases e:p=j.val <;> rcases ofst with rfl|rfl <;> omega)]
    apply commit_initial_zero_byte;rcases ofst with rfl|rfl <;> omega
  obtain ⟨t,run,ipc,_,md,_,w,k,rt,leaves,sa,still⟩:=commit_phase1 rfl o m r s
    seed.pc seed.db seed.mode seed.msg seed.td seed.input seed.width seed.kind seed.row seed.endAddr seed.root readM seed.salts
    (fun j=>⟨empty j 64 (Or.inl rfl),empty j 112 (Or.inr rfl)⟩)
  refine ⟨t,run,ipc,⟨md,k,w,rt⟩,?_,?_,?_⟩
  · intro h bh i bi
    rw [show h=0 by omega] at bi ⊢
    have small : i<LENGTH:=bi
    rw [Late.treeNode,if_pos bi,Late.leafAddress]
    exact (leaves i small).trans (leaf_agrees _ _ _ i small)
  · intro h p k g
    let a:=Late.unusedSlotAddr h p k
    have upper : a+32≤C_ROW:=Late.padValid _ _ _ g
    have lower : C_TD+536870912≤a:=by
      by_cases z:h=0
      · subst h;have absent:=g.missing;have lane:=g.lane
        change 3≤k ∨ 16777216≤3*p+k at absent
        dsimp [a,Late.unusedSlotAddr,Late.rowAddress,Late.levelOffset,S4.layerOffset];omega
      · have mono:=Late.levelOffset_mono (a:=1) (b:=h) (by omega)
        change 536870976≤_ at mono
        dsimp [a,Late.unusedSlotAddr,Late.rowAddress];omega
    apply readBuffer_zero_of_bytes;intro b hb
    change t.getByte (Z (a+b))=0
    have l1 : levelBase 1=536870912:=by decide
    rw [still _ (by omega) (Or.inl (by rw [l1];omega))]
    exact zero _ (by omega) (by omega)
  · intro i
    have addr : C_TD+saltOff i=sharedSaltAddr i:=by
      simp only [saltOff,rowOff,PAIR_STRIDE,Late.sharedSaltAddr,Late.rowBase,C_TD]
      split <;> omega
    exact addr ▸ sa i
end CommitGolfCandidate.R4
