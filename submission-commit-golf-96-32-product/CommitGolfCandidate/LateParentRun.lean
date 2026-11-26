import CommitGolfCandidate.LateParentSites
import CommitGolfCandidate.LateCallState

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure ParentRegs (s : MachineState) (d : Fin 24) (p : Nat) : Prop where
  source : s.getReg .x21 = BitVec.ofNat 64 (nodeAddress d (2*(32*(p/32)))) + BitVec.ofNat 64 (parentBias d)
  target : s.getReg .x22 = BitVec.ofNat 64 (nodeAddress (d.val+1) (32*(p/32)))
  stride : 32 ≤ levelCount (d.val+1) → s.getReg .x29 = 3072
  mode : s.getReg .x5 = 0
  len : s.getReg .x11 = 96
  kind : s.getReg .x13 = 0

def parentReady (s : MachineState) (d p : Nat) :=
  prepareCall s .x21 .x22 (BitVec.ofNat 12 (parentSourceOffset d (p%32))) (BitVec.ofNat 12 (gapOffset (p%32)))

def parentReply (s : MachineState) (d p : Nat) (w : Digest) :=
  callState s .x21 .x22 (BitVec.ofNat 12 (parentSourceOffset d (p%32))) (BitVec.ofNat 12 (gapOffset (p%32))) w

set_option maxHeartbeats 2000000 in
private theorem source_offsets : ∀ d : Fin 24, ∀ j : Fin 32, j.val < tileWidth d →
    BitVec.ofNat 64 (parentBias d) + signExtend12 (BitVec.ofNat 12 (parentSourceOffset d j)) =
      BitVec.ofNat 64 (96*j.val) := by decide

private theorem target_offsets : ∀ j : Fin 32,
    signExtend12 (BitVec.ofNat 12 (gapOffset j)) = BitVec.ofNat 64 (gapOffset j) := by decide

theorem parent_addresses {s : MachineState} {d : Fin 24} {p : Nat} (r : ParentRegs s d p) (inside : p < levelCount (d.val+1)) :
    (parentReady s d p).getReg .x10 = BitVec.ofNat 64 (nodeAddress d (2*p)) ∧
    (parentReady s d p).getReg .x12 = BitVec.ofNat 64 (nodeAddress (d.val+1) p) := by
  let j : Fin 32 := ⟨p%32,by omega⟩
  have e := call_addresses s .x21 .x22 (BitVec.ofNat 12 (parentSourceOffset d j.val))
    (BitVec.ofNat 12 (gapOffset j)) (by decide)
  dsimp only [parentReady]
  change _ = _ ∧ _ = _ at e
  have bound : j.val < tileWidth d := by unfold tileWidth; dsimp [j]; omega
  rw [e.1,e.2,r.source,r.target,BitVec.add_assoc,source_offsets d j bound,
    target_offsets j,←BitVec.ofNat_add,←BitVec.ofNat_add]
  constructor <;> apply congrArg (BitVec.ofNat 64) <;> unfold nodeAddress gapOffset <;>
    dsimp only [j] <;> omega

theorem parent_site_run {s : MachineState} {d : Fin 24} {p : Nat} (regs : ParentRegs s d p)
    (inside : p < levelCount (d.val+1))
    (pc : s.pc = pcAt (parentPC d (p%32))) (fuel : Nat) :
    execute commitImage (fuel+3) s true =
      (do let w ← hash (readBuffer s (nodeAddress d (2*p)) 96)
          let out ← execute commitImage fuel (parentReply s d p w) true
          return out.charge 10 1) := by
  let j : Fin 32 := ⟨p%32,by omega⟩
  have htile : j.val < tileWidth d := by unfold tileWidth; dsimp [j]; omega
  obtain ⟨f0,f1,f2,_⟩ := parent_sites d j htile
  obtain ⟨s0,d0⟩ := parent_addresses regs inside
  have outEnd := parent_below_salts (d.val+1) p inside
  have rowEnd := parent_row_disjoint d p p d.isLt inside
  have smallSrc : nodeAddress d (2*p) + 96 ≤ MEMORY_BYTES := by unfold rowBase at outEnd; unfold MEMORY_BYTES; omega
  have smallDst : nodeAddress (d.val+1) p + 32 ≤ MEMORY_BYTES := by unfold rowBase at outEnd; unfold MEMORY_BYTES; omega
  have sn : ((parentReady s d p).getReg .x10).toNat = nodeAddress d (2*p) := by
    rw [s0,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; unfold MEMORY_BYTES at smallSrc; omega
  have dn : ((parentReady s d p).getReg .x12).toNat = nodeAddress (d.val+1) p := by
    rw [d0,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; unfold MEMORY_BYTES at smallDst; omega
  have aligned (l k : Nat) : nodeAddress l k % 8 = 0 := by unfold nodeAddress levelOffset gapOffset; omega
  have valid : rangeValid ((parentReady s d p).getReg .x10) 96 = true ∧ ((parentReady s d p).getReg .x10).toNat%8 = 0 ∧
      rangeValid ((parentReady s d p).getReg .x12) 32 = true ∧ ((parentReady s d p).getReg .x12).toNat%8 = 0 := by
    simp only [rangeValid,sn,dn,aligned,smallSrc,smallDst,decide_true,true_and]
  have law := execute_compression s _ fuel _ _ _ _ f0 f1 f2 pc regs.mode regs.len regs.kind valid
  change _ = (do let w ← hash (readBuffer s ((parentReady s d p).getReg .x10).toNat 96)
                 let out ← execute commitImage fuel (parentReply s d p w) true
                 pure (out.charge 10 1)) at law
  rw [sn] at law
  exact law

end CommitGolfCandidate.Late
