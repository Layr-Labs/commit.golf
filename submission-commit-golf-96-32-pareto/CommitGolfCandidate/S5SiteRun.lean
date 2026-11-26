import CommitGolfCandidate.S5Pointers

namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem leaf_range (k : Nat) (inside : k < LENGTH) (j : Fin 4) :
    leafSource k j % 8 = 0 ∧ leafTarget k j % 8 = 0 ∧
    leafSource k j + 96 ≤ MEMORY_BYTES ∧ leafTarget k j + 32 ≤ MEMORY_BYTES := by
  change k < 16777216 at inside
  have off : levelOffset 0 = 0 := by decide
  fin_cases j <;> simp only [leafSource, leafTarget, Fin.isValue, msgAddr, rowAddr, rowBase,
    contentAddr, nodeAddress, off, leafOffset, ite_true, MEMORY_BYTES] <;> omega

def siteResult (h : Compression) (tile : Nat) (s : MachineState) (i : Fin 256) (j : Fin 4) :=
  leafReply s i j (h (readBuffer s (leafSource (256*tile+i.val) j) 96))

theorem execute_site {s : MachineState} {tile : Nat} {i : Fin 256} (regs : LeafRegs s tile i)
    (j : Fin 4) (pc : s.pc = pcAt (leafPC i j)) (inside : 256*tile+i.val < LENGTH) (fuel : Nat) :
    execute commitImage (fuel+3) s true =
      (do let w ← hash (readBuffer s (leafSource (256*tile+i.val) j) 96)
          let r ← execute commitImage fuel (leafReply s i j w) true
          return r.charge 10 1) := by
  obtain ⟨op₁,op₂,op₃⟩ := leaf_fetch i j
  obtain ⟨src,dst⟩ := ready_addresses regs j
  obtain ⟨sa,da,sv,dv⟩ := leaf_range _ inside j
  let k := 256*tile+i.val
  have sn : ((leafReady s i j).getReg .x10).toNat = leafSource k j := by
    rw [src,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; change _+96 ≤ 2^36 at sv; omega
  have dn : ((leafReady s i j).getReg .x12).toNat = leafTarget k j := by
    rw [dst,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; change _+32 ≤ 2^36 at dv; omega
  have valid : rangeValid ((leafReady s i j).getReg .x10) 96 = true ∧
      ((leafReady s i j).getReg .x10).toNat%8 = 0 ∧ rangeValid ((leafReady s i j).getReg .x12) 32 = true ∧
      ((leafReady s i j).getReg .x12).toNat%8 = 0 := by
    simp only [rangeValid,sn,dn]
    exact ⟨decide_eq_true sv,sa,decide_eq_true dv,da⟩
  have law := execute_compression s (leafPC i j) fuel _ _ _ _ op₁ op₂ op₃ pc regs.selector
    regs.length regs.kind valid
  change _ = (do let w ← hash (readBuffer s ((leafReady s i j).getReg .x10).toNat 96)
                 let r ← execute commitImage fuel (leafReply s i j w) true
                 pure (r.charge 10 1)) at law
  rw [sn] at law
  exact law

theorem fixed_site (o : Oracle) {s : MachineState} {tile : Nat} {i : Fin 256} (regs : LeafRegs s tile i)
    (j : Fin 4) (pc : s.pc = pcAt (leafPC i j)) (inside : 256*tile+i.val < LENGTH) (fuel : Nat) :
    o.run (execute commitImage (fuel+3) s true) =
      (do let (out,n) ← o.run (execute commitImage fuel (siteResult o.compression tile s i j) true)
          return (out.charge 10 1,1+n)) := by
  rw [execute_site regs j pc inside]
  unfold Late.hash
  erw [oracle_run_public_bind o (.inl _)]
  simp only [oracle_run_bind, oracle_run_pure, pure_bind, bind_assoc, Nat.add_zero]
  rfl

end CommitGolfCandidate.S5Machine
