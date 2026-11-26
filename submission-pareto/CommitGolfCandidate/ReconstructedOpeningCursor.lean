import CommitGolfCandidate.ReconstructedOpeningLane
import CommitGolfCandidate.ReconstructedOpeningPut
import RiscvZkvm.Rv64.Logic.ByteOps

namespace CommitGolfCandidate.Reconstruction.OpeningCursor
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningLane
open TwoPermutationPrototype.RV64 OpeningPut
open CommitBlocks (addr)
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
abbrev W := BitVec.ofNat 64
abbrev image := OpeningStraight.image

theorem offset (cursor : Nat) : W cursor &&& signExtend12 63 = W (cursor%64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change (cursor%2^64) &&& (2^6-1) = (cursor%64)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod];omega

theorem aligned (x : Nat) : alignToDword (W x)=W (8*(x/8)) := by
  have h := alignToDword_add_byteOffset (W x)
  have off : byteOffset (W x)= x%8 := by
    unfold byteOffset
    rw [BitVec.toNat_and,BitVec.toNat_ofNat]
    change (x%2^64) &&& (2^3-1)=x%8
    rw [Nat.and_two_pow_sub_one_eq_mod];omega
  rw [off,show W x=W (8*(x/8))+W (x%8) from (by rw [←BitVec.ofNat_add,Nat.div_add_mod]) ] at h
  have cancel := congrArg (fun z : Word => z-W (x%8)) h
  rw [BitVec.add_sub_cancel,BitVec.add_sub_cancel] at cancel
  simpa only [←BitVec.ofNat_add,Nat.div_add_mod] using cancel

theorem word_address (cursor : Nat) (fit : cursor<2^64) :
    ((W cursor >>> (3 : Nat)) &&& signExtend12 4088) + wordAddress base = wordAddress (cell cursor) := by
  have shift : W cursor >>> (3 : Nat) = W (cursor/8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega : cursor/8<2^64)]
  rw [shift]
  change alignToDword (W (cursor/8))+wordAddress base=_
  rw [aligned,BitVec.add_comm]
  change wordAddress base+wordAddress (cursor/8/8)=_
  rw [←wordAddress_add]
  congr 1
  unfold cell;omega

theorem negative_shift (n : Fin 64) (positive : 0<n.val) :
    (((0 : BitVec 32)-(W n.val).truncate 32).signExtend 64).toNat%64=64-n.val := by
  exact (by decide : ∀ k : Fin 64, 0<k.val →
    (((0 : BitVec 32)-(W k.val).truncate 32).signExtend 64).toNat%64=64-k.val) n positive

def addressOps : List Op := [
  .reg .x10 (.andi .x7 63),.reg .x13 (.srli .x7 3),.reg .x13 (.andi .x13 4088),
  .reg .x13 (.add .x13 .x25)]

private theorem listed : OpeningStraight.Listed 201 (addressOps.map Op.instr) := ⟨rfl,rfl,rfl,rfl,True.intro⟩

theorem address_values (m : Model) (c : Nat) (fit : c<2^64) (cursor : m.reg .x7=W c)
    (dst : m.reg .x25=wordAddress base) :
    let t := after m addressOps
    t.reg .x10 = W (c%64) ∧ t.reg .x13=wordAddress (cell c) ∧ t.mem=m.mem ∧
    (∀ r, r≠.x10 → r≠.x13 → t.reg r=m.reg r) := by
  refine ⟨?_,?_,rfl,?_⟩
  · change m.reg .x7 &&& signExtend12 63=_
    rw [cursor,offset]
  · change ((m.reg .x7 >>> (3 : Nat)) &&& signExtend12 4088)+m.reg .x25=_
    rw [cursor,dst,word_address c fit]
  · intro r x y;simp [after,addressOps,Op.apply,Model.set,x.symm,y.symm]

theorem address_run (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 201) (fits : Fits s m) :
    ∃ t, CommitExact.Segment o image 4 s t ∧ t.pc=addr 205 ∧ Fits t (after m addressOps) :=
  OpeningStraight.block o m addressOps 201 (by decide) listed (by simp [addressOps,Checked,Op.Valid]) s pc fits

theorem zero_branch (o : Oracle) (s : MachineState) (i fall dst : Nat) (reg : Reg) (imm : BitVec 13)
    (pc : s.pc=addr i) (fits : i<1660) (word : OpeningStraight.actualAt i=some (.base (.BEQ reg .x0 imm)))
    (left : addr i+4=addr fall) (right : addr i+signExtend13 imm=addr dst) (v : Word) (value : s.getReg reg=v) :
    CommitExact.Segment o image 1 s (s.setPC (if v=0 then addr dst else addr fall)) := by
  apply CommitExact.plain o image _ _ _ (OpeningStraight.fetched i _ fits word s pc)
  change some (if s.getReg reg == s.getReg .x0 then s.setPC (s.pc+signExtend13 imm) else s.setPC (s.pc+4)) = _
  rw [value,show s.getReg .x0=0 from rfl,pc,right,left]
  by_cases z : v=0
  · rw [z];rfl
  · rw [beq_eq_false_iff_ne.mpr z,ite_eq_right z];rfl

end CommitGolfCandidate.Reconstruction.OpeningCursor
