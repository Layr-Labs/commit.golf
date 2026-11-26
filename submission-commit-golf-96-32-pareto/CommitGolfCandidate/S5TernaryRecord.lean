import CommitGolfCandidate.S5OrdinaryPath
import CommitGolfCandidate.S5NormalPeer
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape bytes)

def twoPeers (t : Levels) (i : Index) :=
  bytes (n:=32) (bottomSibling t i 1) ++ bytes (n:=32) (bottomSibling t i 2)

theorem ternary_record (s : MachineState) (i : Index) (dst : Nat) (xs : List Index) (tree : Levels) (salt : SaltTape)
    (pc : s.pc=pcAt 517) (size : xs.length≤LENGTH) (src : Sources s xs tree salt) (cap : Capacity s)
    (gp : s.getReg .x3=W 2048) (three : s.getReg .x25=3) (idx : s.getReg .x14=W i.val)
    (ptr : s.getReg .x19=W dst) (high : proofBase≤dst) (valid : AddrOK dst 64) :
    ∃ t,Runs s t 33 45 ∧ t.pc=pcAt 550 ∧ t.getReg .x19=W (dst+64) ∧ t.getReg .x14=W (indexAbove i 1) ∧
      Sources t xs tree salt ∧ Capacity t ∧ PathKeeps s t ∧ Written s t dst (twoPeers tree i) := by
  let u:=evaluated bottomOps s
  have firstBase : wordAt s 2048=W tdBase:=cap 0 (by decide)
  obtain ⟨hdr,ip,mem,group,digit,parent,unused⟩:=bottom_lookup s false i pc gp firstBase idx three
  have tet : u.getReg .x25=3:=(unused _ (by decide) (by decide) (by decide) (by decide)).trans three
  have dest : u.getReg .x19=W dst:=(unused _ (by decide) (by decide) (by decide) (by decide)).trans ptr
  have tab : Capacity u:=fun j hj=>(congrFun mem _).trans (cap j hj)
  have room:=valid.2
  have align:=valid.1
  obtain ⟨v,runA,nextA,digitA,dstA,keepA,srcA,capA,dataA⟩:=copy_peer u i dst false xs tree salt size ip group
    (by simpa [Nat.mod_mod] using digit) tet dest ⟨align,by omega⟩ high (src.same_mem mem) tab
  have groupA:=(keepA .x4 (by decide)).trans group
  have threeA:=(keepA .x25 (by decide)).trans tet
  obtain ⟨t,runB,nextB,_,dstB,keepB,srcB,capB,dataB⟩:=copy_peer v i (dst+32) true xs tree salt size nextA groupA digitA threeA dstA
    ⟨by omega,by omega⟩ (by omega) srcA capA
  refine ⟨t,(hdr.trans runA).trans runB,nextB,dstB.trans (congrArg W (by omega)),?_,srcB,capB,?_,?_⟩
  · exact (keepB _ (by decide)).trans ((keepA _ (by decide)).trans (by simpa [indexAbove,S4.nodeIndex,S4.span] using parent))
  · intro r ne
    have both : r∉([.x6,.x7,.x19,.x28] : List Reg) := by intro h;apply ne;cases r <;> simp_all
    apply (keepB r both).trans ((keepA r both).trans _)
    apply unused <;> intro eq <;> subst r <;> simp at ne
  · change Written s t dst (_++_)
    apply (dataA.congr_mem mem.symm rfl).append
    · simp only [bytes,List.length_ofFn];exact dataB
    · simp only [bytes,List.length_ofFn];omega
    · simp [bytes]
    · simp only [bytes,List.length_ofFn];omega
end CommitGolfCandidate.S5Machine.Open
