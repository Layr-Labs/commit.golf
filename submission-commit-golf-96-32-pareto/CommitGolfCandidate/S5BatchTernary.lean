import CommitGolfCandidate.S5BatchPeers
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)

def bottomField (t : Levels) (i : Index) (j : Nat) : S5.Field := (256,(bottomSibling t i j).toNat)
def peerFields (t : Levels) (i : Index) := [bottomField t i 1,bottomField t i 2]

set_option maxRecDepth 16000
attribute [local irreducible] evaluated emitted
theorem batch_ternary (s : MachineState) (i : Index) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (fs : List S5.Field) (size : xs.length≤LENGTH) (limit : widths fs+512≤555170) (env : InputRows s xs seen tree salt)
    (cur : FieldCursor tree s fs) (pc : s.pc=pcAt 156) (gp : s.getReg .x3=W 2048)
    (three : s.getReg .x25=3) (idx : s.getReg .x14=W i.val) :
    let cost:=23+energy (widths fs) (peerFields tree i)
    ∃ t,Runs s t cost (cost+12) ∧ t.pc=pcAt 179 ∧ t.getReg .x14=W (indexAbove i 1) ∧
      FieldCursor tree t (fs++peerFields tree i) ∧ InputRows t xs seen tree salt ∧ OuterKeeps s t := by
  let u:=evaluated bottomOps s
  have firstBase : wordAt s 2048=W tdBase:=env.table 0 (by decide)
  obtain ⟨hdr,ip,mem,group,digit,parent,unused⟩:=bottom_lookup s true i pc gp firstBase idx three
  have stable (q : Reg) (h : q∉([.x4,.x6,.x7,.x14] : List Reg)) : u.getReg q=s.getReg q := by
    apply unused <;> intro e <;> subst q <;> simp at h
  have outer : OuterKeeps s u := by intro q h;apply stable;cases q <;> simp_all [outerRegs]
  have c:=cursor_same cur mem (stable _ (by decide)) (stable _ (by decide)) (stable _ (by decide)) (stable _ (by decide))
  have threeU:=(outer .x25 (by decide)).trans three
  obtain ⟨v,rA,ipA,digitA,grpA,idxA,curA,envA,keepA⟩:=pack_peer u i false xs seen tree salt fs (by omega) size
    (inputs_mem env mem) c ip group (by simpa [Nat.mod_mod] using digit) threeU
  let fsA:=fs++[bottomField tree i 1]
  have wA : widths fsA=widths fs+256:=by simp [fsA,widths,bottomField]
  obtain ⟨t,rB,ipB,_,_,idxB,curB,envB,keepB⟩:=pack_peer v i true xs seen tree salt fsA (by rw [wA];omega) size
    envA curA ipA (grpA.trans group) digitA ((keepA .x25 (by decide)).trans threeU)
  refine ⟨t,?_,ipB,idxB.trans (idxA.trans (by simpa [indexAbove,S4.nodeIndex,S4.span] using parent)),?_,envB,(outer.then keepA).then keepB⟩
  · have all:=(hdr.trans rA).trans rB
    rw [wA] at all
    unfold emitCycles at all
    rw [show (peerEmit false).width=256 from rfl,show (peerEmit true).width=256 from rfl] at all
    dsimp only [peerFields,energy,bottomField]
    convert all using 1 <;> omega
  · simpa only [fsA,peerFields,List.append_assoc,List.singleton_append,peerNumber,bottomField,ite_true,ite_false,Bool.false_eq_true] using curB
end CommitGolfCandidate.S5Machine.Open
