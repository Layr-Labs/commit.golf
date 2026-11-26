import CommitGolfCandidate.S5OpenInitial
import CommitGolfCandidate.S5Empty
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late (Levels SaltTape node)

def rawLevels (td : Trapdoor) : Levels :=
  (List.range (LOG_LENGTH+1)).map fun d=>(List.range (sourceCount d)).map fun j=>slice td (nodeAddress d j) 32
def rawSalts (td : Trapdoor) : SaltTape := fun i=>slice td (saltAddress i) 24

attribute [local irreducible] List.range readBuffer
theorem raw_agrees (td : Trapdoor) : TrapdoorAgrees td (rawLevels td) (rawSalts td) := by
  have lookup (d j : Nat) (height : d≤LOG_LENGTH) (inside : j<sourceCount d) :
      Late.node (rawLevels td) d j=slice td (nodeAddress d j) 32 := by
    simp only [rawLevels,node,List.getElem?_map,List.getElem?_range (show d<LOG_LENGTH+1 by omega),
      Option.map_some,Option.getD_some,List.getElem?_range inside]
  constructor
  · intro d hd i hi;apply (lookup d i hd _).symm
    unfold sourceCount;split
    next lt =>
      change i<S4.width (min d 24) at hi;rw [Nat.min_eq_left (by omega)] at hi
      unfold S4.rowCount
      by_cases zero : d=0 <;> simp [S4.radix,zero] at * <;> omega
    next=>exact hi
  · exact fun i=>rfl
  · intro d p k hd hp hk _
    have par : p<S4.rowCount d := by
      unfold levelCount at hp;rw [Nat.min_eq_left (by omega)] at hp
      exact (S4.row_width ⟨d,hd⟩).symm ▸ hp
    rw [lookup d _ (show d≤LOG_LENGTH from (show d≤24 by omega)) (by
      rw [sourceCount,if_pos hd];have :=Nat.mul_le_mul_left (S4.radix d) (show p+1≤S4.rowCount d from par)
      rw [Nat.mul_add,Nat.mul_one] at this;omega),row_slot _ _ _ hk]
theorem open_abi (td : Trapdoor) (ps : Positions) :
    Artifact.submission.run .opening (td,ps)=execute image 68719476736 (initial td ps) true := by
  have generic (s : Submission) (t : BitVec (8*s.sizes.trapdoor)) :
    s.run .opening (t,ps)=execute (s.image .opening) (s.steps .opening) (s.initialState .opening (t,ps)) true := rfl
  exact generic Artifact.submission td

theorem read_proof (s : MachineState) (cycles : Nat) (bs : Proof) (len : s.getReg .x11=W bs.length)
    (fits : bs.length≤17179869184) (data : HasBytes s proofBase bs) :
    let result : Execution:=⟨.success,s,cycles,0⟩
    Artifact.submission.openingSucceeded result=true ∧ Artifact.submission.readProof result=bs := by
  have n : (s.getReg .x11).toNat=bs.length := by rw [len,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ok : Artifact.submission.openingSucceeded ⟨.success,s,cycles,0⟩=true := by
    change (true && decide ((s.getReg .x11).toNat≤17179869184))=true;rw [n,decide_eq_true fits];rfl
  refine ⟨ok,?_⟩
  rw [Submission.readProof,if_pos ok]
  change (List.range (s.getReg .x11).toNat).map _=bs
  rw [n];apply List.ext_getElem
  · simp
  · intro j _ hj
    simp only [List.getElem_map,List.getElem_range]
    exact data j hj

def reportLength : PathCode := [(989,.SUB .x11 .x19 .x18),(990,.ADDI .x5 .x0 1),(991,.ADDI .x10 .x0 0)]
def reported (s : MachineState) := pathEnd s reportLength

theorem ordinary_exit (s : MachineState) (pc : s.pc=pcAt 989) (len : Nat)
    (start : s.getReg .x18=W proofBase) (dest : s.getReg .x19=W (proofBase+len)) (fuel : Nat) :
    execute image (fuel+4) s true=pure ⟨.success,reported s,4,0⟩ ∧
      (reported s).getReg .x11=W len ∧ (reported s).mem=s.mem := by
  have ok : pathReady s reportLength ∧ (reported s).pc=pcAt 992 := by
    simp +decide [reportLength,reported,pathReady,pathEnd,execInstrBr,ordinaryStep,memoryArgumentsValid,memAccess,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,pc,pcAt]
  have run:=path_run .opening true s reportLength (by decide +kernel) ok.1 (fuel+1)
  have halt:=site (p:=.opening) (n:=992) (op:=.ECALL) (by decide) (by rfl) _ ok.2
  refine ⟨?_,?_,rfl⟩
  · rw [show fuel+4=(fuel+1)+reportLength.length by rfl,run]
    change (do let r←execute image (fuel+1) (reported s) true; pure (r.charge 3 0))=_
    rw [execute,halt,show (reported s).getReg .x5=1 by rfl,show (reported s).getReg .x10=0 by rfl];rfl
  · change s.getReg .x19-s.getReg .x18=_
    rw [start,dest];unfold W
    rw [BitVec.ofNat_add,BitVec.add_comm,BitVec.add_sub_cancel]
end CommitGolfCandidate.S5Machine.Open
