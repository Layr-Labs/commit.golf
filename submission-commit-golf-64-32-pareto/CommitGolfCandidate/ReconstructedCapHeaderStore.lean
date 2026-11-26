import CommitGolfCandidate.ReconstructedCapWordStep
import CommitGolfCandidate.ReconstructedCapLowLast

namespace CommitGolfCandidate.Reconstruction.CapHeaderStore
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor OpeningPut
open TwoPermutationPrototype (writeWord)
open TwoPermutationPrototype.RV64
open CapLowCore (sameReg)
open CommitBlocks (addr)
set_option maxRecDepth 18000
set_option maxHeartbeats 1700000

def beginOps : List Op := [.reg .x15 (.andi .x7 63),.reg .x12 (.srli .x7 3),.reg .x12 (.andi .x12 4088),
  .reg .x14 (.add .x12 .x17),.reg .x16 (.and .x16 .x29)]
def direct (c : Nat) : List Op := [.sd .x14 .x16 0 (cell c)]
def merged (c : Nat) : List Op := [.ld .x12 .x14 0 (cell c),.reg .x6 (.sll .x16 .x15),
  .reg .x12 (.or .x12 .x6),.sd .x14 .x12 0 (cell c)]
def spill (c : Nat) : List Op := [.reg .x12 (.subw .x0 .x15),.reg .x12 (.srl .x16 .x12),.sd .x14 .x12 8 (cell c+1)]
def ends (m : Model) (c : Nat) :=
  if c%64=0 then after m (direct c) else
  let a := after m (merged c)
  if c%64<34 then a else after a (spill c)

theorem entry (m : Model) (c : Nat) (bound : c<2^64) (cursor : m.reg .x7=W c) (baseReg : m.reg .x17=wordAddress base) :
    let a := after m beginOps
    a.reg .x15=W (c%64) ∧ a.reg .x14=wordAddress (cell c) ∧ a.reg .x16=m.reg .x16 &&& m.reg .x29 := by
  refine ⟨?_,?_,rfl⟩
  · change m.reg .x7 &&& signExtend12 63=_
    rw [cursor,offset]
  · change ((m.reg .x7 >>> (3:Nat)) &&& signExtend12 4088)+m.reg .x17=_
    rw [cursor,baseReg,word_address _ bound]

theorem checks (m : Model) (c : Nat) (room : cell c+1<2^33) (ptr : m.reg .x14=wordAddress (cell c)) :
    Checked m (direct c) ∧ Checked m (merged c) ∧ Checked (after m (merged c)) (spill c) := by
  have a : m.reg .x14+signExtend12 0=wordAddress (cell c) := ptr ▸ BitVec.add_zero _
  have b : m.reg .x14+signExtend12 8=wordAddress (cell c+1) := by rw [ptr,wordAddress_add];rfl
  simp only [direct,merged,spill,Checked,Op.Valid,Op.apply,true_and,and_true]
  exact ⟨⟨by omega,a⟩,⟨⟨by omega,a⟩,⟨by omega,a⟩⟩,⟨room,b⟩⟩

theorem memory (m : Model) (c : Nat) (zero : m.reg .x0=0) (off : m.reg .x15=W (c%64)) :
    (ends m c).mem=put m.mem c 31 (m.reg .x16) := by
  unfold ends
  by_cases al : c%64=0
  · rw [ite_eq_left al];exact CapWriter.aligned_store m.mem c 31 (m.reg .x16) al (by decide)
  · rw [ite_eq_right al]
    have sh : (((m.reg .x0).truncate 32 - (m.reg .x15).truncate 32).signExtend 64).toNat%64=64-c%64 := by
      rw [zero,off];exact negative_shift ⟨c%64,Nat.mod_lt _ (by decide)⟩ (Nat.pos_of_ne_zero al)
    rw [put,first,ite_eq_right al]
    by_cases short : c%64<34
    · rw [ite_eq_left short,ite_eq_right (show ¬c%64+31>64 by omega)]
      change writeWord m.mem (cell c) (m.mem (cell c) ||| (m.reg .x16 <<< ((m.reg .x15).toNat%64)))=_
      rw [off,CapLowMergedWords.amount]
    · rw [ite_eq_right short,ite_eq_left (show c%64+31>64 by omega)]
      change writeWord (writeWord m.mem (cell c) (m.mem (cell c) ||| (m.reg .x16 <<< ((m.reg .x15).toNat%64)))) (cell c+1)
        (m.reg .x16 >>> ((((m.reg .x0).truncate 32 - (m.reg .x15).truncate 32).signExtend 64).toNat%64))=_
      rw [sh,off,CapLowMergedWords.amount]

theorem keep (m : Model) (c : Nat) (r : Reg) (ne : r≠.x6) (ne' : r≠.x12) : (ends m c).reg r=m.reg r := by
  unfold ends;split
  · rfl
  · split <;> simp [after,merged,spill,Op.apply,Model.set,Model.store,ne.symm,ne'.symm]

theorem offsetGate (o : Oracle) (s : MachineState) (pc : s.pc=addr 1636) (off : Fin 64)
    (value : s.getReg .x15=W off.val) (bound : s.getReg .x19=34) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (if off.val<34 then addr 1598 else addr 1637)) := by
  apply CommitExact.plain o _ _ _ (.base (.BLTU .x15 .x19 8040)) (OpeningStraight.fetched 1636 _ (by decide) rfl s pc)
  change some (if (s.getReg .x15).ult (s.getReg .x19) then s.setPC (s.pc+signExtend13 8040) else s.setPC (s.pc+4))=_
  rw [pc,value,bound];fin_cases off <;> rfl

theorem actual (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 1631) (fit : Fits s m) (c : Nat)
    (room : cell c+1<2^33) (ptr : m.reg .x14=wordAddress (cell c)) (off : m.reg .x15=W (c%64)) (bound : m.reg .x19=34) :
    ∃ n t, n≤10 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1598 ∧ Fits t (ends m c) := by
  have branch := zero_branch o s 1631 1632 1597 .x15 8056 pc (by decide) rfl rfl rfl (W (c%64)) ((fit.registers _).trans off)
  have ziff : W (c%64)=0 ↔ c%64=0 := by
    constructor
    · intro z;have n := congrArg BitVec.toNat z;change (c%64)%2^64=0 at n;omega
    · intro z;rw [z];rfl
  simp only [ziff] at branch
  obtain ⟨directOk,mergeOk,spillOk⟩ := checks m c room ptr
  by_cases al : c%64=0
  · rw [ite_eq_left al] at branch
    obtain ⟨v,g,loc,f⟩ := OpeningStraight.block o m (direct c) 1597 (by change 1597+1≤1660;decide) ⟨rfl,True.intro⟩ directOk _ rfl (fit.pc _)
    exact ⟨2,_,by decide,CommitExact.compose branch g,loc,by rw [ends,ite_eq_left al];exact f⟩
  · rw [ite_eq_right al] at branch
    let a := after m (merged c)
    obtain ⟨v,g,loc,f⟩ := OpeningStraight.block o m (merged c) 1632 (by change 1632+4≤1660;decide)
      ⟨rfl,rfl,rfl,rfl,True.intro⟩ mergeOk _ rfl (fit.pc _)
    have gate := offsetGate o v loc ⟨c%64,by omega⟩ ((f.registers _).trans off) ((f.registers _).trans bound)
    change CommitExact.Segment _ _ _ _ (v.setPC (if c%64<34 then addr 1598 else addr 1637)) at gate
    by_cases no : c%64<34
    · rw [ite_eq_left no] at gate
      exact ⟨6,_,by decide,CommitExact.compose (CommitExact.compose branch g) gate,rfl,
        by simp only [ends,ite_eq_right al,ite_eq_left no];exact f.pc _⟩
    · rw [ite_eq_right no] at gate
      obtain ⟨t,spillRun,spillPC,ff⟩ := OpeningStraight.block o a (spill c) 1637 (by change 1637+3≤1660;decide)
        ⟨rfl,rfl,rfl,True.intro⟩ spillOk _ rfl (f.pc _)
      have finish := CapWordStep.jump o t 1640 1598 2096984 spillPC (by decide) rfl rfl
      exact ⟨10,_,by decide,CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose branch g) gate) spillRun) finish,rfl,
        by simp only [ends,ite_eq_right al,ite_eq_right no];exact ff.pc _⟩

end CommitGolfCandidate.Reconstruction.CapHeaderStore
