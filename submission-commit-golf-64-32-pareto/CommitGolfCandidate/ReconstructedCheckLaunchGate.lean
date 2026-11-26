import CommitGolfCandidate.ReconstructedCheckHalt
import CommitGolfCandidate.ReconstructedCheckCapArith
import CommitGolfCandidate.ReconstructedCheckLaunchCode

namespace CommitGolfCandidate.Reconstruction.CheckLaunchGate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding.Machine CheckRecorded CommitBlocks CheckCapArith
open TwoPermutationPrototype.Sampling
set_option maxHeartbeats 1050000
set_option maxRecDepth 50000
attribute [local irreducible] execute ArtifactEncoding.decode
abbrev W:=BitVec.ofNat 64

def minimum (count : Nat) := (3633*count+7)/8

def Reject (o : Oracle) (n : Nat) (s : MachineState) := ∀ fuel,
    let obs:=observation o (n+fuel) s
    obs.1.1.exit=.failure ∧ obs.1.2=[] ∧ obs.2=0 ∧ obs.1.1.state.getReg .x11=(-1)

theorem reject (o : Oracle) (t : MachineState) (pc : t.pc=addr 20) (value : t.getReg .x10=(-1)) : Reject o 4 t := by
  intro fuel
  have endAt:=CheckHalt.terminal o t pc fuel
  rw [value] at endAt
  exact endAt

theorem extend {o n m s t} (step : Segment o n s t []) (wrong : Reject o m t) : Reject o (n+m) s := by
  obtain ⟨fee,step⟩:=step
  intro fuel
  have h:=wrong fuel
  simp only [Nat.add_assoc,step,List.nil_append,List.length_nil,Nat.zero_add,Execution.charge]
  exact h

def alignCode : List Line := [(.x5,.op (.addi .x10 0)),(.x12,.op (.andi .x11 7)),(.x10,.op (.addi .x0 4095))]

private theorem alignListed : listed 24 alignCode=true := by decide +kernel
private theorem branchListed : CheckStraight.actualAt 27=some (.base (.BEQ .x12 .x0 8)) := CheckDecode.same_sound (by decide +kernel)
private theorem returnListed : CheckMemoryOps.word 28 (.base (.JALR .x0 .x1 0))=true := by decide +kernel

private theorem jump28 (o : Oracle) (t : MachineState) (pos : t.pc=addr 28) (ra : t.getReg .x1=addr 20) :
    Segment o 1 t (t.setPC (addr 20)) [] := by
  apply plain _ _ _ _ (CheckMemoryOps.parsed returnListed t pos)
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,execInstrBr,ra]
  rfl

structure Aligned (s t : MachineState) (count len : Nat) : Prop where
  ret : t.getReg .x1=addr 20
  stack : t.getReg .x2=W CheckLayout.fp
  countReg : t.getReg .x5=W count
  minus : t.getReg .x10=(-1)
  length : t.getReg .x11=W len
  memory : t.mem=s.mem

def startPC (len : Nat) := if len%8=0 then 29 else 28
def endGate (s : MachineState) (len : Nat):=(effect s alignCode).setPC (addr (startPC len))

private theorem control (o : Oracle) (u : MachineState) (len : Nat) (pc : u.pc=addr 27) (bits : u.getReg .x12=W (len%8)) :
    Segment o 1 u (u.setPC (addr (startPC len))) [] := by
  have beq:=CheckBranch.event o u 27 29 .eq .x12 .x0 8 (by decide) pc branchListed (by decide)
  change Segment o 1 u (u.setPC (if u.getReg .x12==0#64 then addr 29 else addr 28)) [] at beq
  rw [bits] at beq
  by_cases eq : len%8=0
  · rw [startPC,ite_eq_left eq];rw [eq] at beq;exact beq
  · have diff : W (len%8)≠0#64 := by intro h;have v:=congrArg BitVec.toNat h;change (len%8)%2^64=0 at v;omega
    rw [startPC,ite_eq_right eq];rw [beq_eq_false_iff_ne.mpr diff] at beq;exact beq

private theorem entrance (o : Oracle) (s : MachineState) (len : Nat) (pc : s.pc=addr 24) (size : s.getReg .x11=W len) :
    Segment o 4 s (endGate s len) [] := by
  let u:=effect s alignCode
  have bits : u.getReg .x12=W (len%8) := by
    rw [register];change s.getReg .x11 &&& 7#64=_;rw [size]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,BitVec.toNat_ofNat,BitVec.toNat_ofNat]
    change (len%2^64 &&& (2^3-1))=(len%8)%2^64
    rw [Nat.and_two_pow_sub_one_eq_mod];omega
  exact compose (CheckCapArith.positive o s 24 alignCode pc alignListed) (control o u len (location s 24 alignCode pc) bits)

private theorem aligned (s : MachineState) (count len : Nat) (ra : s.getReg .x1=addr 20)
    (stack : s.getReg .x2=W CheckLayout.fp) (num : s.getReg .x10=W count) (size : s.getReg .x11=W len) :
    Aligned s (endGate s len) count len := by
  constructor
  · exact (MachineState.getReg_setPC ..).trans ((outside s alignCode .x1 (by decide)).trans ra)
  · exact (MachineState.getReg_setPC ..).trans ((outside s alignCode .x2 (by decide)).trans stack)
  · unfold endGate;rw [MachineState.getReg_setPC,register s alignCode]
    change s.getReg .x10+0=W count
    exact (BitVec.add_zero _).trans num
  · unfold endGate;rw [MachineState.getReg_setPC,register s alignCode]
    change (0#64)+signExtend12 4095= -1#64
    decide
  · exact (MachineState.getReg_setPC ..).trans ((outside s alignCode .x11 (by decide)).trans size)
  · exact CheckCapArith.memory s alignCode

theorem align (o : Oracle) (s : MachineState) (count len : Nat) (pc : s.pc=addr 24) (ra : s.getReg .x1=addr 20)
    (stack : s.getReg .x2=W CheckLayout.fp) (num : s.getReg .x10=W count) (size : s.getReg .x11=W len) :
    if len%8=0 then
      ∃ t,Segment o 4 s t [] ∧ t.pc=addr 29 ∧ t.getReg .x1=addr 20 ∧ t.getReg .x2=W CheckLayout.fp ∧
        t.getReg .x5=W count ∧ t.getReg .x10=(-1) ∧ t.getReg .x11=W len ∧ t.mem=s.mem
    else Reject o 9 s := by
  let t:=endGate s len
  have filled:=aligned s count len ra stack num size
  have stem:=entrance o s len pc size
  have loc : t.pc=addr (startPC len):=rfl
  split
  · rename_i ok
    rw [startPC,ite_eq_left ok] at loc
    exact ⟨t,stem,loc,filled.ret,filled.stack,filled.countReg,filled.minus,filled.length,filled.memory⟩
  · rename_i bad
    rw [startPC,ite_eq_right bad] at loc
    exact extend (compose stem (jump28 o t loc filled.ret)) (reject o (t.setPC (addr 20)) rfl filled.minus)

def sizeCode : List Line := [(.x12,.op (.mul .x5 .x12)),(.x12,.op (.addi .x12 7)),(.x12,.op (.srli .x12 3))]

theorem sizeWord (count : Nat) (small : count≤2^24) : ((W count*3633#64+7#64) >>> (3 : Nat))=W (minimum count) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  change (((count%2^64)*3633%2^64+7)%2^64)/8=(minimum count)%2^64
  unfold minimum
  rw [Nat.mod_eq_of_lt (by omega : count<2^64),Nat.mod_eq_of_lt (by omega : count*3633<2^64),
    Nat.mod_eq_of_lt (by omega : count*3633+7<2^64),Nat.mod_eq_of_lt (by omega : (3633*count+7)/8<2^64),
    Nat.mul_comm]

end CommitGolfCandidate.Reconstruction.CheckLaunchGate

