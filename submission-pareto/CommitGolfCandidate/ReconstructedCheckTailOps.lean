import CommitGolfCandidate.ReconstructedCheckLaunch
import CommitGolfCandidate.ReconstructedCheckRoot

namespace CommitGolfCandidate.Reconstruction.CheckTailOps
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding.Machine CheckRecorded CheckCapArith CommitBlocks
open TwoPermutationPrototype.RV64
set_option maxRecDepth 60000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute
abbrev W := BitVec.ofNat 64

theorem align (n : Nat) (small : n<2^64) : ((W n >>> (3 : Nat)) &&& 0xfffffffffffffff8#64)=W (8*(n/64)) := by
  have bits (w : Word) : (w >>> (3 : Nat)) &&& 0xfffffffffffffff8#64=(w >>> (6 : Nat)) <<< (3 : Nat) := by
    rw [show 0xfffffffffffffff8#64=BitVec.allOnes 64 <<< 3 by decide]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have sub : i-3<64 := by omega
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_allOnes,BitVec.getLsbD_ushiftRight,
      hi,sub,decide_true,Bool.true_and,Bool.and_true]
    by_cases low : i<3
    · simp [low]
    · simp [low,show 6+(i-3)=3+i by omega]
  rw [bits]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow];congr 1;omega

theorem load (o : Oracle) (s : MachineState) (pc : Nat) (rd rs : Reg) (imm : BitVec 12)
    (w : Nat) (room : w<2^33) (val : Word) (location : s.pc=addr pc)
    (op : CheckMemoryOps.word pc (.base (.LD rd rs imm))=true)
    (ptr : s.getReg rs+signExtend12 imm=wordAddress w) (mem : s.getMem (wordAddress w)=val) :
    Segment o 1 s ((s.setReg rd val).setPC (addr (pc+1))) [] := by
  have safe : accessValid (wordAddress w) 8=true := by
    simp [accessValid,rangeValid,MEMORY_BYTES,word_address_value (by omega : w<2^61)];omega
  apply plain _ _ _ _ (CheckMemoryOps.parsed op s location)
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,ptr,safe,ite_true,execInstrBr,mem,location,addr_next]

def firstOps : List Line := [(.x10,.op (.addi .x24 63)),(.x10,.op (.srli .x10 3)),(.x11,.op (.andi .x10 4088)),
    (.x10,.op (.addi .x0 4095)),(.x12,.op (.lui 1)),(.x12,.op (.sub .x8 .x12))]

structure Frame (s t : MachineState) : Prop where
  regs : ∀ r∈[Reg.x2,.x8,.x24],t.getReg r=s.getReg r
  mem : ∀ p,t.getMem p=s.getMem p

private theorem fetchedFirst : listed 632 firstOps=true := by decide +kernel
private theorem fetchedLength : CheckMemoryOps.word 638 (.base (.LD .x12 .x12 1672))=true := by decide +kernel
private theorem fetchedBranch : CheckStraight.actualAt 639=some (.base (.BNE .x11 .x12 5864)) := CheckDecode.same_sound (by decide +kernel)

theorem wordNe (x y : Nat) (hx : x<2^64) (hy : y<2^64) : (W x != W y)=decide (x≠y) := by
  by_cases eq : x=y
  · subst y;simp
  · rw [decide_eq_true eq];apply bne_iff_ne.mpr;intro h
    have q := congrArg BitVec.toNat h
    change x%2^64=y%2^64 at q;omega

private theorem raw12 (r : Reg → Word) : regs r firstOps .x12=r .x8-W 4096 := rfl
private theorem raw11 (r : Reg → Word) : regs r firstOps .x11=((r .x24+W 63) >>> (3 : Nat)) &&& 0xfffffffffffffff8#64 := rfl
private theorem raw10 (r : Reg → Word) : regs r firstOps .x10=r .x0+(-1) := rfl

private theorem prep12 (s : MachineState) (fp : s.getReg .x8=W CheckLayout.fp) :
    (effect s firstOps).getReg .x12+signExtend12 1672=wordAddress 8589934163 := by
  rw [register,raw12,fp];decide
private theorem prep11 (s : MachineState) (c : Nat) (bound : c≤70000000000) (cursor : s.getReg .x24=W c) :
    (effect s firstOps).getReg .x11=W (alignedBytes c) := by
  rw [register,raw11,cursor,←BitVec.ofNat_add,align _ (by omega)]
  exact congrArg W (by unfold alignedBytes;omega)
private theorem prep10 (s : MachineState) : (effect s firstOps).getReg .x10=(-1) := by
  rw [register,raw10];change 0#64+(-1)=(-1);decide

def afterLength (u : MachineState) (len : Nat) := (u.setReg .x12 (W len)).setPC (addr 639)
theorem afterOther (u : MachineState) (len : Nat) (r : Reg) (other : r≠.x12) :
    (afterLength u len).getReg r=u.getReg r := by
  unfold afterLength;rw [MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg]
  simp [Ne.symm other]
private theorem lengthValue (u : MachineState) (len : Nat) : (afterLength u len).getReg .x12=W len := rfl

theorem prefixRun (o : Oracle) (s : MachineState) (c len : Nat) (bound : c≤70000000000) (size : len<2^64)
    (pc : s.pc=addr 632) (cursor : s.getReg .x24=W c) (fp : s.getReg .x8=W CheckLayout.fp)
    (saved : s.getMem (W (CheckLayout.fp-2424))=W len) :
    ∃ t,Segment o 8 s t [] ∧ t.pc=(if alignedBytes c=len then addr 640 else addr 57) ∧
      t.getReg .x10=(-1) ∧ Frame s t := by
  let u := effect s firstOps
  have first := CheckCapArith.positive o s 632 firstOps pc fetchedFirst
  have pc638 : u.pc=addr 638 := location s 632 firstOps pc
  have ptr := prep12 s fp
  have masked := prep11 s c bound cursor
  have neg := prep10 s
  have memU (p : Word) : u.getMem p=s.getMem p := congrFun (memory s firstOps) p
  let v := afterLength u len
  have ld := load o u 638 .x12 .x12 1672 8589934163 (by decide) (W len) pc638 fetchedLength ptr ((memU _).trans saved)
  have mask : v.getReg .x11=W (alignedBytes c) := (afterOther u len .x11 (by decide)).trans masked
  have br := CheckBranch.event o v 639 57 .ne .x11 .x12 5864 (by decide) rfl fetchedBranch (by decide)
  have test : CheckOrdinary.Cond.test .ne (v.getReg .x11) (v.getReg .x12)=decide (alignedBytes c≠len) := by
    change (v.getReg .x11 != v.getReg .x12)=_;rw [mask,lengthValue]
    exact wordNe _ _ (by unfold alignedBytes;omega) size
  rw [test] at br
  let flag := if alignedBytes c=len then addr 640 else addr 57
  have dest : (if decide (alignedBytes c≠len) then addr 57 else addr (639+1))=flag := by
    by_cases h : alignedBytes c=len <;> simp [flag,h]
  rw [dest] at br
  refine ⟨v.setPC flag,compose (compose first ld) br,rfl,(MachineState.getReg_setPC ..).trans ((afterOther u len .x10 (by decide)).trans neg),?_,memU⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  all_goals exact (MachineState.getReg_setPC ..).trans ((afterOther u len _ (by decide)).trans (CheckCapArith.outside s firstOps _ (by decide)))

end CommitGolfCandidate.Reconstruction.CheckTailOps
