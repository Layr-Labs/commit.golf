import CommitGolfCandidate.LateCallState
import CommitGolfCandidate.LateLeafSites
import CommitGolfCandidate.LateLeafWrites

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure LeafRegs (s : MachineState) (tile : Nat) (i : Fin 32) : Prop where
  message : s.getReg .x8 = BitVec.ofNat 64 (msgAddr (32*tile+8*(i.val/8)))
  rows : s.getReg .x18 = BitVec.ofNat 64 (rowAddr (32*tile+16*(i.val/16)))
  nodes : s.getReg .x23 = BitVec.ofNat 64 (nodeAddress 0 (32*tile))
  selector : s.getReg .x5 = 0
  length : s.getReg .x11 = 96
  kind : s.getReg .x13 = 0

def leafSource (k : Nat) : Nat → Nat
  | 0 => msgAddr k | 1 => msgAddr k + 64 | 2 => msgAddr k + 160 | _ => rowAddr k

def leafTarget (k : Nat) : Nat → Nat
  | 0 => msgAddr k+64 | 1 => contentAddr k | 2 => contentAddr k+32 | _ => nodeAddress 0 k

def leafReady (s : MachineState) (i : Fin 32) (j : Fin 4) :=
  prepareCall s (sourceReg j) (targetReg j) (BitVec.ofNat 12 (sourceOffset i j))
    (BitVec.ofNat 12 (targetOffset i j))

def leafReply (s : MachineState) (i : Fin 32) (j : Fin 4) (w : Digest) :=
  callState s (sourceReg j) (targetReg j) (BitVec.ofNat 12 (sourceOffset i j))
    (BitVec.ofNat 12 (targetOffset i j)) w

private theorem base_dst (j : Fin 4) : Reg.x10 ≠ targetReg j := by fin_cases j <;> decide

set_option maxRecDepth 10000 in
private theorem short_offsets : ∀ i : Fin 32, ∀ j : Fin 4,
    signExtend12 (BitVec.ofNat 12 (sourceOffset i j)) = BitVec.ofNat 64 (sourceOffset i j) ∧
    signExtend12 (BitVec.ofNat 12 (targetOffset i j)) = BitVec.ofNat 64 (targetOffset i j) := by decide

theorem ready_addresses {s : MachineState} {tile : Nat} {i : Fin 32} (regs : LeafRegs s tile i)
    (j : Fin 4) :
    let r := leafReady s i j
    r.getReg .x10 = BitVec.ofNat 64 (leafSource (32*tile+i.val) j) ∧
    r.getReg .x12 = BitVec.ofNat 64 (leafTarget (32*tile+i.val) j) := by
  dsimp only [leafReady]
  obtain ⟨src,dst⟩ := call_addresses s (sourceReg j) (targetReg j) (BitVec.ofNat 12 (sourceOffset i j))
    (BitVec.ofNat 12 (targetOffset i j)) (base_dst j)
  rw [src,dst,(short_offsets i j).1,(short_offsets i j).2]
  have zero : levelOffset 0 = 0 := by decide
  fin_cases j <;>
    simp only [sourceReg, targetReg, leafSource, leafTarget, sourceOffset, targetOffset,
      Fin.isValue, Fin.reduceFinMk, Nat.reduceEqDiff, ↓reduceIte, regs.message, regs.nodes,
      regs.rows, ← BitVec.ofNat_add, nodeAddress, zero, msgAddr, rowAddr, contentAddr, gapOffset] <;>
    constructor <;> apply congrArg (BitVec.ofNat 64) <;> omega

theorem reply_regs {s : MachineState} {tile : Nat} {i : Fin 32} (regs : LeafRegs s tile i)
    (j : Fin 4) (w : Digest) : LeafRegs (leafReply s i j w) tile i := by
  constructor <;>
    first | exact (call_register _ _ _ _ _ _ _ (by decide) (by decide)).trans regs.message
          | exact (call_register _ _ _ _ _ _ _ (by decide) (by decide)).trans regs.rows
          | exact (call_register _ _ _ _ _ _ _ (by decide) (by decide)).trans regs.nodes
          | exact (call_register _ _ _ _ _ _ _ (by decide) (by decide)).trans regs.selector
          | exact (call_register _ _ _ _ _ _ _ (by decide) (by decide)).trans regs.length
          | exact (call_register _ _ _ _ _ _ _ (by decide) (by decide)).trans regs.kind

theorem reply_memory {s : MachineState} {tile : Nat} {i : Fin 32} (regs : LeafRegs s tile i)
    (j : Fin 4) (w : Digest) : (leafReply s i j w).mem =
      (store s (leafTarget (32*tile+i.val) j) w).mem := by
  have same := (call_addresses s (sourceReg j) (targetReg j) (BitVec.ofNat 12 (sourceOffset i j))
      (BitVec.ofNat 12 (targetOffset i j)) (base_dst j)).2
  exact (call_memory s _ _ _ _ w (base_dst j)).trans
    (congrArg (fun a => (writeBits s a w).mem) (same.symm.trans (ready_addresses regs j).2))

end CommitGolfCandidate.Late
