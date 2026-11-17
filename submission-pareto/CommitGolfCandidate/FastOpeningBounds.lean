import CommitGolfCandidate.FastOpeningLoop
/-! Transfer the reference heap, node and output bounds to every unrolled path
copy, for arbitrary initial memory contents. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

theorem fast_path_heap (level : Nat) (s : MachineState) :
    (openingPathState^[level] s).getReg .x9=s.getReg .x9 := by
  induction level with
  | zero => rfl
  | succ level ih => rw [Function.iterate_succ_apply',(opening_path_registers _).2.2.2.2,ih]

theorem fast_path_node_bound (level : Nat) (s : MachineState)
    (bounded : (s.getReg .x20).toNat<2^25) :
    ((openingPathState^[level] s).getReg .x20).toNat<2^25 := by
  induction level with
  | zero => exact bounded
  | succ level ih =>
    rw [Function.iterate_succ_apply',(opening_path_registers _).2.1,
      BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    omega

theorem fast_full_path (s : MachineState) (pc : s.pc=4248)
    (heapBound : (s.getReg .x9).toNat+2^30≤MEMORY_BYTES)
    (heapAligned : (s.getReg .x9).toNat%8=0)
    (nodeBound : (s.getReg .x20).toNat<2^25)
    (outputBound : (s.getReg .x25).toNat+32*24≤MEMORY_BYTES)
    (outputAligned : (s.getReg .x25).toNat%8=0)
    (fuel : Nat) (coins : Bool) :
    execute fastImage (336+fuel) s coins=
      (do let result ← execute fastImage fuel
            ((openingPathState^[24] s).setPC 5592) coins
          return result.charge 336 0) := by
  have reads : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] s).getReg .x9+
       (((openingPathState^[level] s).getReg .x20 ^^^ 1)<<<5)+
       BitVec.ofNat 64 (8*word.val)) 8=true := by
    intro level inside word
    apply opening_sibling_access
    · simpa only [fast_path_heap] using heapBound
    · simpa only [fast_path_heap] using heapAligned
    · exact fast_path_node_bound level s nodeBound
  have writes : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] s).getReg .x25+
       BitVec.ofNat 64 (8*word.val)) 8=true := by
    intro level inside word
    have address : ((openingPathState^[level] s).getReg .x25).toNat=
        (s.getReg .x25).toNat+32*level := by
      rw [opening_path_output,BitVec.toNat_add,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 32*level<2^64),Nat.mod_eq_of_lt]
      simp only [MEMORY_BYTES] at outputBound
      omega
    apply opening_digest_access_valid
    · rw [address];omega
    · rw [address];omega
  have run := fast_path_loop 24 0 (by decide) s reads writes fuel coins
  have same : s.setPC (BitVec.ofNat 64 (4248+56*0))=s := by
    simp only [Nat.mul_zero,Nat.add_zero]
    change s.setPC (4248 : Word)=s
    rw [←pc]
    cases s
    rfl
  simp only [Function.iterate_zero,id_eq,Nat.zero_add] at run
  rw [same] at run
  exact run
end CommitGolfCandidate
