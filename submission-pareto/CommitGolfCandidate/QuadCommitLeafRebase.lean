import CommitGolfCandidate.QuadCommitLeafControlFetch
import CommitGolfCandidate.QuadCommitLeafProduction

/-! Exact rebases of the centered 44-leaf output window and 256-leaf centered salt window. -/
namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute image

def heapUpdate (s : MachineState) := (s.setReg .x20 (s.getReg .x12+2040)).setPC (s.pc+4)
def nonceUpdate (s : MachineState) := (s.setReg .x22 (s.getReg .x22+s.getReg .x7)).setPC (s.pc+4)
def rebased (s : MachineState) (u : Nat) :=
  let h := if u%44=43 ∨ u=4095 then heapUpdate s else s
  if u%256=127 then nonceUpdate h else h

theorem heap_at (s : MachineState) (u : Fin 4096) (here : s.pc=leafPC u 11)
    (h : u.val%44=43 ∨ u.val=4095) (fuel : Nat) :
    execute image (1+fuel) s true =
      (do let out ← execute image fuel (heapUpdate s) true
          return out.charge 1 0) := by
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (fetch_heap_rebase u h s here) (show ordinaryStep s _=some (heapUpdate s) by rfl)]
  rfl

theorem nonce_at (s : MachineState) (u : Fin 4096)
    (here : s.pc=leafPC u (11+heapExtra u.val)) (h : u.val%256=127) (fuel : Nat) :
    execute image (1+fuel) s true =
      (do let out ← execute image fuel (nonceUpdate s) true
          return out.charge 1 0) := by
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (fetch_nonce_rebase u h s here) (show ordinaryStep s _=some (nonceUpdate s) by rfl)]
  rfl

theorem rebase_run (s : MachineState) (u : Fin 4096) (here : s.pc=leafPC u 11) (fuel : Nat) :
    execute image (extra u.val+fuel) s true =
      (do let out ← execute image fuel (rebased s u.val) true
          return out.charge (extra u.val) 0) := by
  by_cases h : u.val%44=43 ∨ u.val=4095
  · by_cases n : u.val%256=127
    · simp only [extra,heapExtra,nonceExtra,rebased,h,n,ite_true]
      rw [show 1+1+fuel=1+(1+fuel) by omega,heap_at s u here h]
      have next : (heapUpdate s).pc=leafPC u (11+heapExtra u.val) := by
        change s.pc+4=_
        rw [here,heapExtra,if_pos h]
        exact leaf_pc_add u 11 1
      rw [nonce_at _ u next n]
      simp [Execution.charge,←Nat.add_assoc]
    · simpa only [extra,heapExtra,nonceExtra,rebased,h,n,ite_true,ite_false,Nat.add_zero] using heap_at s u here h fuel
  · by_cases n : u.val%256=127
    · have next : s.pc=leafPC u (11+heapExtra u.val) := by simpa only [heapExtra,if_neg h,Nat.add_zero] using here
      simpa only [extra,heapExtra,nonceExtra,rebased,h,n,ite_false,ite_true,Nat.zero_add] using nonce_at s u next n fuel
    · simp [extra,heapExtra,nonceExtra,rebased,h,n,Execution.charge]

private theorem pc_step (u : Fin 4096) :
    leafPC u 11+BitVec.ofNat 64 (4*extra u.val)=BitVec.ofNat 64 (4096+4*leafIndex (u.val+1)) := by
  unfold leafPC
  rw [←BitVec.ofNat_add,leaf_index_next]
  congr 1 <;> omega

private theorem next_heap (g u : Nat) (hu : u<4096) (h : u%44=43 ∨ u=4095) :
    wordAddress (leafDest (4096*g+u))+2040=wordAddress (heapBase g (u+1)) := by
  change wordAddress _+wordAddress 255=_
  rw [←wordAddress_add]
  congr 1
  unfold heapBase
  split <;> unfold windowWord leafDest leafWord groupWord <;> omega

private theorem same_heap (g u : Nat) (hu : u<4096) (h : ¬(u%44=43 ∨ u=4095)) :
    heapBase g u=heapBase g (u+1) := by
  unfold heapBase
  rw [if_neg (by omega),if_neg (by omega)]
  unfold windowWord
  congr 2
  omega

private theorem next_nonce (g u : Nat) (h : u%256=127) :
    wordAddress (nonceBase g u)+4096=wordAddress (nonceBase g (u+1)) := by
  change wordAddress _+wordAddress 512=_
  rw [←wordAddress_add]
  congr 1
  unfold nonceBase leafSalt Commit.saltWord
  omega

theorem rebase_regs (s : MachineState) (g : Nat) (u : Fin 4096) (r : RawRegs s g u) :
    Regs (rebased s u.val) g (u.val+1) := by
  have src : s.getReg .x10=wordAddress (leafStart (4096*g+(u.val+1))+5) := by
    simpa only [idx,Nat.add_assoc] using r.source
  have pc := pc_step u
  by_cases h : u.val%44=43 ∨ u.val=4095
  · by_cases n : u.val%256=127
    · simp only [rebased,h,n,ite_true]
      simp only [extra,heapExtra,nonceExtra,h,n,ite_true] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · change s.getReg .x12+2040=_
        rw [r.dest]
        exact next_heap g u.val u.isLt h
      · change s.getReg .x22+s.getReg .x7=_
        rw [r.salts,r.stride]
        exact next_nonce g u.val n
      · change s.pc+4+4=_
        rw [r.pc,BitVec.add_assoc]
        exact pc
    · simp only [rebased,h,n,ite_true,ite_false]
      simp only [extra,heapExtra,nonceExtra,h,n,ite_true,ite_false] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · change s.getReg .x12+2040=_
        rw [r.dest]
        exact next_heap g u.val u.isLt h
      · change s.getReg .x22=_
        rw [r.salts]
        unfold nonceBase
        rw [show (u.val+1+128)/256=(u.val+128)/256 by omega]
      · change s.pc+4=_
        rw [r.pc]
        exact pc
  · by_cases n : u.val%256=127
    · simp only [rebased,h,n,ite_false,ite_true]
      simp only [extra,heapExtra,nonceExtra,h,n,ite_false,ite_true] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · change s.getReg .x20=_
        rw [r.heap,same_heap g u.val u.isLt h]
      · change s.getReg .x22+s.getReg .x7=_
        rw [r.salts,r.stride]
        exact next_nonce g u.val n
      · change s.pc+4=_
        rw [r.pc]
        exact pc
    · simp only [rebased,h,n,ite_false]
      simp only [extra,heapExtra,nonceExtra,h,n,ite_false] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · rw [r.heap,same_heap g u.val u.isLt h]
      · rw [r.salts]
        unfold nonceBase
        rw [show (u.val+1+128)/256=(u.val+128)/256 by omega]
      · rw [r.pc]
        simpa using pc

theorem rebase_mem (s : MachineState) (u : Nat) : (rebased s u).mem=s.mem := by
  unfold rebased
  split <;> split <;> rfl

end TwoPermutationPrototype.Quad.Commit.Leaves
