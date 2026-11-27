import CommitGolfCandidate.Stage3cOrdinarySibling
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape)

def PathKeeps (s t : MachineState) := ∀ r,r∉([.x4,.x6,.x7,.x14,.x19,.x28] : List Reg)→
  t.getReg r=s.getReg r

theorem ordinary_path (s : MachineState) (d n dst : Nat) (i : Index) (xs : List Index) (tree : Levels) (salt : SaltTape)
    (depth : d+n≤24) (pc : s.pc=pcAt (477+19*d)) (gp : s.getReg .x3=W 2048) (tab : Capacity s)
    (idx : s.getReg .x14=W (indexAbove i d)) (ptr : s.getReg .x19=W dst)
    (high : proofBase≤dst) (valid : AddrOK dst (32*n)) (source : Sources s xs tree salt) (size : xs.length≤LENGTH) :
    ∃ t,Runs s t (19*n) (19*n) ∧ t.pc=pcAt (477+19*(d+n)) ∧ t.getReg .x19=W (dst+32*n) ∧
      t.getReg .x14=W (indexAbove i (d+n)) ∧ Capacity t ∧ Sources t xs tree salt ∧ PathKeeps s t ∧
      Written s t dst (pathBytes tree i d n) := by
  induction n generalizing d dst s with
  | zero=>exact ⟨s,Runs.refl _,by simpa using pc,by simpa using ptr,by simpa using idx,tab,source,fun _ _=>rfl,Written.empty ..⟩
  | succ n ih=>
    let l : Fin 24:=⟨d,by omega⟩
    let u:=ordinarySibling s l
    have all:=valid.2
    have head:=ordinary_sibling s l i dst tree pc gp tab idx ptr high ⟨valid.1,by omega⟩
      (source.node d (by change d≤24;omega) _ (mate_bound i d (by change d<24;omega)))
    have len : (Late.bytes (n:=32) (Late.node tree d (mate i d))).length=32 := by simp [Late.bytes]
    have outside:=head.written.outside
    rw [len] at outside
    have nextSources:=source.after size dst 32 outside high valid.1 (by decide)
    have aligned:=valid.1
    have next:=ih u (d+1) (dst+32) (by omega) head.pc ((head.regs .x3 (by decide)).trans gp)
      head.table head.idx head.ptr (by omega) ⟨by omega,by omega⟩ nextSources
    obtain ⟨t,run,last,dest,index,table,src,keep,bytes⟩:=next
    have endD : d+1+n=d+(n+1) := by omega
    have endDst : dst+32+32*n=dst+32*(n+1) := by omega
    rw [endD] at last index
    rw [endDst] at dest
    refine ⟨t,?_,last,dest,index,table,src,fun r ne=>(keep r ne).trans (head.regs r ne),?_⟩
    · have total:=head.run.trans run
      simpa only [Nat.mul_succ,Nat.add_comm 19] using total
    · rw [path_cons]
      apply head.written.append
      · rw [len];exact bytes
      · rw [len];omega
      · rw [path_len];omega
      · rw [len];omega
end CommitGolfCandidate.Chained.BinaryMachine.Open
