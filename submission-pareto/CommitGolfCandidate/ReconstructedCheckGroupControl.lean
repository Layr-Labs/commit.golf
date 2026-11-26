import CommitGolfCandidate.ReconstructedCheckCapArith
import CommitGolfCandidate.ReconstructedCheckGroupRadix
import CommitGolfCandidate.ReconstructedCheckRecordHeader

namespace CommitGolfCandidate.Reconstruction.CheckGroupControl
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapArith CheckGroupRadix
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def Kept (xs : List Reg) (s t : MachineState) := ∀ v∉xs,t.getReg v=s.getReg v

theorem less (o : Oracle) (s : MachineState) (pc dest : Nat) (a b : Reg) (i j : Nat) (off : BitVec 13)
    (inside : pc<796) (pos : s.pc=addr pc) (word : CheckStraight.actualAt pc=some (.base (.BLTU a b off)))
    (target : addr pc+signExtend13 off=addr dest) (ha : s.getReg a=W i) (hb : s.getReg b=W j)
    (hi : i<2^64) (hj : j<2^64) :
    Segment o 1 s (s.setPC (addr (if i<j then dest else pc+1))) [] := by
  have h:=CheckBranch.event o s pc dest .lt a b off inside pos word target
  change Segment o 1 s (s.setPC (if (s.getReg a).ult (s.getReg b) then addr dest else addr (pc+1))) [] at h
  rw [ha,hb,BitVec.ult_eq_decide] at h
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj,decide_eq_true_eq] at h
  split <;> simp_all

theorem endDigit (o : Oracle) (s : MachineState) (v : Nat) (pos : s.pc=addr 592)
    (val : s.getReg .x5=W v) (base : s.getReg .x21=W 211) (small : v<2^31) :
    Segment o 1 s (s.setPC (addr (if v/211=0 then 593 else 672))) [] := by
  have h:=CheckBranch.event o s 592 672 .ge .x5 .x21 320 (by decide) pos rfl (by decide)
  change Segment o 1 s (s.setPC (if !(s.getReg .x5).ult (s.getReg .x21) then addr 672 else addr 593)) [] at h
  rw [val,base,BitVec.ult_eq_decide] at h
  by_cases low : v<211
  · have inv : v/211=0:=by omega
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : v<2^64),show 211%2^64=211 by decide,
      low,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,inv,ite_true] using h
  · have inv : v/211≠0:=by omega
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : v<2^64),show 211%2^64=211 by decide,
      low,decide_false,Bool.not_false,ite_true,ite_eq_right inv] using h

def initCode : List Line := [(.x15,.op (.addi .x0 0)),(.x16,.op (.slli .x13 32)),(.x16,.op (.srli .x16 30)),
  (.x16,.op (.add .x29 .x16)),(.x24,.op (.addi .x24 31)),(.x17,.op (.slli .x17 33)),(.x17,.op (.srli .x17 33))]

theorem setup (o : Oracle) (s : MachineState) (c j base v : Nat) (pos : s.pc=addr 570)
    (cursor : s.getReg .x24=W c) (idx : s.getReg .x13=W j) (small : j<2^32) (stack : s.getReg .x29=W base)
    (raw : (s.getReg .x17).toNat%2^31=v) :
    ∃ t,Segment o 7 s t [] ∧ t.pc=addr 577 ∧ t.getReg .x15=0 ∧ t.getReg .x16=CheckCapSlots.address base j ∧
      t.getReg .x24=W (c+31) ∧ t.getReg .x17=W v ∧ t.mem=s.mem ∧ Kept [.x15,.x16,.x17,.x24] s t := by
  let t:=effect s initCode
  refine ⟨t,CheckCapArith.positive o s 570 initCode pos (by decide),location s 570 initCode pos,?_,?_,?_,?_,memory ..,?_⟩
  · rw [register];rfl
  · rw [register];change s.getReg .x29+((s.getReg .x13 <<< (32 : Nat)) >>> (30 : Nat))=_
    rw [idx,stack,index _ small];exact (BitVec.ofNat_add ..).symm
  · rw [register];change s.getReg .x24+W 31=W (c+31);rw [cursor];exact (BitVec.ofNat_add ..).symm
  · rw [register];change ((s.getReg .x17 <<< (33 : Nat)) >>> (33 : Nat))=_
    rw [clip,raw]
  · intro r ok;apply outside;simpa [initCode,and_comm,and_left_comm,and_assoc] using ok

def countCode : List Line := [(.x14,.op (.subw .x12 .x13)),(.x15,.op (.addi .x0 4))]
def capCode : List Line := [(.x14,.op (.addi .x0 4))]

private theorem subSmall (a b : Nat) (le : b≤a) (small : a≤512) :
    ((W a).truncate 32-(W b).truncate 32).signExtend 64=W (a-b) := by
  have eq : (W a).truncate 32=BitVec.ofNat 32 (a-b)+(W b).truncate 32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add,BitVec.toNat_setWidth,BitVec.toNat_ofNat];omega
  rw [eq,BitVec.add_sub_cancel]
  exact (by decide +kernel : ∀ i : Fin 513,(BitVec.ofNat 32 i.val).signExtend 64=W i.val) ⟨a-b,by omega⟩

theorem count (o : Oracle) (s : MachineState) (n j : Nat) (pos : s.pc=addr 554) (total : s.getReg .x12=W n)
    (idx : s.getReg .x13=W j) (le : j≤n) (small : n≤512) :
    ∃ k t,k≤4 ∧ Segment o k s t [] ∧ t.pc=addr 558 ∧ t.getReg .x14=W (min (n-j) 4) ∧
      t.mem=s.mem ∧ Kept [.x14,.x15] s t := by
  let u:=effect s countCode
  have first:=CheckCapArith.positive o s 554 countCode pos (by decide)
  have diff : u.getReg .x14=W (n-j) := by rw [register];change ((s.getReg .x12).truncate 32-(s.getReg .x13).truncate 32).signExtend 64=_;rw [idx,total,subSmall _ _ le small]
  have four : u.getReg .x15=W 4:=by rw [register];rfl
  have test:=less o u 556 558 .x14 .x15 (n-j) 4 8 (by decide) (location s 554 countCode pos) rfl (by decide) diff four (by omega) (by decide)
  by_cases tiny : n-j<4
  · rw [ite_eq_left tiny] at test
    refine ⟨3,_,by decide,compose first test,rfl,?_,memory ..,?_⟩
    · simpa only [MachineState.getReg_setPC,Nat.min_eq_left (by omega : n-j≤4)] using diff
    · intro r ok;change u.getReg r=_;apply outside;simpa [countCode] using ok
  · rw [ite_eq_right tiny] at test
    let a:=u.setPC (addr 557)
    let t:=effect a capCode
    have set:=CheckCapArith.positive o a 557 capCode rfl (by decide)
    refine ⟨4,t,by decide,compose (compose first test) set,location a 557 capCode rfl,?_,?_,?_⟩
    · rw [register,Nat.min_eq_right (by omega : 4≤n-j)];rfl
    · exact (memory a capCode).trans (memory s countCode)
    · intro r ok
      have hx : r≠.x14 ∧ r≠.x15 := by simpa using ok
      have z:=outside a capCode r (by simpa [capCode] using hx.1)
      exact z.trans (outside s countCode r (by simpa [countCode] using hx))

end CommitGolfCandidate.Reconstruction.CheckGroupControl

