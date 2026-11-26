import CommitGolfCandidate.S5Calls
import CommitGolfCandidate.S5TileSites
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
abbrev leafPC := tileSite
def sourceReg (j : Nat) : Reg := if j=3 then .x22 else .x21
def targetReg (j : Nat) : Reg := if j=0 then .x21 else if j=3 then .x23 else .x22
def sourceLogical (i j : Nat) := if j=3 then 96*(i%42) else 256*(i%16)+(if j=0 then 0 else if j=1 then 64 else 160)
def targetLogical (i j : Nat) := if j=0 then 256*(i%16)+64 else if j=3 then gap (i%128)
  else 96*(i%42)+32*(i%2)+(if j=1 then 0 else 32)
def sourceOffset (i j : Nat) := 2048+sourceLogical i j
def targetOffset (i j : Nat) := 2048+targetLogical i j
def sourceInstr (i j : Nat) := Instr.ADDI .x10 (sourceReg j) (BitVec.ofNat 12 (sourceOffset i j))
def targetInstr (i j : Nat) := Instr.ADDI .x12 (targetReg j) (BitVec.ofNat 12 (targetOffset i j))


set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem leaf_decode : ∀ i : Fin 256, ∀ j : Fin 4,
    decodeInstruction (readWord i j)=some (.base (sourceInstr i j)) ∧
    decodeInstruction (writeWord i j)=some (.base (targetInstr i j)) := by decide +kernel

set_option maxRecDepth 20000 in
attribute [local irreducible] Artifact.commitCode ArtifactEncoding.decode in
theorem leaf_fetch (i : Fin 256) (j : Fin 4) :
    AtWord (leafPC i j) (sourceInstr i j) ∧ AtWord (leafPC i j+1) (targetInstr i j) ∧ AtWord (leafPC i j+2) .ECALL := by
  have bound : tileSite i j+2<18492 := by have :=i.isLt; have :=j.isLt;unfold tileSite;omega
  obtain ⟨w,v,e⟩:=all_tile_sites i j
  have dec (n : Nat) (hn : n<18492) (op : Instr) (ok : decodeInstruction (commitWord n)=some (.base op)) :
      AtWord n op := by
    apply site (p:=.commit) hn
    rw [commitWord,dif_pos hn] at ok
    exact ok
  refine ⟨dec (tileSite i j) (by omega) _ ?_,dec (tileSite i j+1) (by omega) _ ?_,dec _ bound _ ?_⟩
  · rw [w];exact (leaf_decode i j).1
  · rw [v];exact (leaf_decode i j).2
  · rw [e];rfl
end CommitGolfCandidate.S5Machine
