import CommitGolfCandidate.R1bOpenRoute
namespace CommitGolfCandidate.R1b.Opening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open R1bPC (pcAt)

set_option maxRecDepth 8192
attribute [local irreducible] MachineState.setByte

private def price (ops : List Instr) := (ops.map (fun op=>instructionCycles (.base op))).sum

private theorem seqRun (s : MachineState) (idx : Nat) (ops : List Instr) (pc : s.pc=pcAt idx)
    (room : idx+ops.length≤12697) (code : Matches .opening idx ops)
    (valid : ∀ j (hj : j<ops.length),
      let t:=(ops.take j).foldl execInstrBr s
      ordinaryStep t (.base ops[j])=some (execInstrBr t ops[j]) ∧ t.pc=pcAt (idx+j)) :
    Runs .opening s (ops.foldl execInstrBr s) ops.length (price ops) := by
  induction ops generalizing idx s with
  | nil => exact Runs.refl _ _
  | cons op ops ih =>
    let t:=execInstrBr s op
    have first:=one (by change idx<12697;simp only [List.length_cons] at room;omega) pc op code.head (valid 0 (by simp)).1
    have good (j : Nat) (hj : j<ops.length) :
        let u:=(ops.take j).foldl execInstrBr t
        ordinaryStep u (.base ops[j])=some (execInstrBr u ops[j]) ∧ u.pc=pcAt (idx+1+j) := by
      obtain ⟨st,atPC⟩:=valid (j+1) (Nat.succ_lt_succ hj)
      refine ⟨st,?_⟩
      exact atPC.trans (congrArg pcAt (show idx+(j+1)=idx+1+j by omega))
    cases ops with
    | nil => simpa [price] using first
    | cons a rest =>
      have here := (good 0 (by simp)).2
      have tail:=ih (idx:=idx+1) (s:=t) here (by simp only [List.length_cons] at room ⊢;omega) code.tail good
      simpa [price,Nat.add_comm 1,List.foldl_cons] using first.trans tail

private def tagOps : List Instr := [.LUI .x6 16,.ADDI .x6 .x6 2560,.SUB .x7 .x11 .x6,
  .ADDI .x6 .x0 30,.DIVU .x7 .x7 .x6,.SB .x22 .x7 0,.LUI .x11 16,.ADDI .x11 .x11 1953]

theorem tagRun (s : MachineState) (len : Nat) (hi : len≤67840) (low : 67488<len)
    (pc : s.pc=pcAt 12616) (l : s.getReg .x11=W len) (ptr : s.getReg .x22=W (proofBase+67488)) :
    ∃ t, Runs .opening s t 8 11 ∧ t.pc=returnPC ∧ t.getReg .x11=W 67489 ∧
      Wrote s t (proofBase+67488) 1 (fun _=>BitVec.ofNat 8 ((len-64000)/30)) := by
  let t:=tagOps.foldl execInstrBr s
  have offset : s.getReg .x11-64000#64=W (len-64000) := by
    rw [l];exact BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)
  have tag : rv64_divu (s.getReg .x11-64000#64) 30 = W ((len-64000)/30) := by
    rw [offset];change (W (len-64000))/30=W _
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv]
    change ((len-64000)%2^64)/30=((len-64000)/30)%2^64
    rw [Nat.mod_eq_of_lt (by omega : len-64000<2^64),Nat.mod_eq_of_lt (by omega : (len-64000)/30<2^64)]
  have addr : s.getReg .x22+0=W (proofBase+67488) := (BitVec.add_zero _).trans ptr
  have safe : accessValid (s.getReg .x22+0) 1=true := by rw [addr];exact Safe.valid ⟨by decide,by decide⟩
  have words : listed .opening 12616 tagOps := by decide
  have run:=seqRun s 12616 tagOps pc (by decide) (matchesListed words) (by
    intro j hj
    have b : j<8:=hj
    interval_cases j
    all_goals constructor
    all_goals first | rfl | (change (if accessValid (s.getReg .x22+0) 1 then some _ else none)=_;rw [safe] <;> rfl) |
      (simp [tagOps,List.foldl,execInstrBr,MachineState.setPC,pc,pcAt]))
  refine ⟨t,run,?_,?_,?_⟩
  · simp [t,tagOps,List.foldl,execInstrBr,MachineState.setPC,pc,pcAt,returnPC]
  · rfl
  · have effect:=storedFlag s (proofBase+67488) (BitVec.ofNat 8 ((len-64000)/30)) (by decide)
    let u:=(tagOps.take 5).foldl execInstrBr s
    have loc : u.getReg .x22+signExtend12 0=W (proofBase+67488) := addr
    have lastValue : u.getReg .x7 = rv64_divu (s.getReg .x11-64000#64) (30#64) := by
      simp (config:={decide:=true}) [u,tagOps,List.foldl,execInstrBr,MachineState.getReg,
        MachineState.setReg,MachineState.setPC,signExtend12] <;> rfl
    have val : (u.getReg .x7).truncate 8=BitVec.ofNat 8 ((len-64000)/30) := by
      have number : u.getReg .x7=W ((len-64000)/30) := lastValue.trans tag
      exact (congrArg (BitVec.truncate 8) number).trans (BitVec.setWidth_ofNat_of_le (by decide : 8≤64) _)
    have actual : t.mem=(u.setByte (u.getReg .x22+signExtend12 0) ((u.getReg .x7).truncate 8)).mem := rfl
    rw [loc,val] at actual
    apply effect.mem
    exact actual.trans (by unfold MachineState.setByte MachineState.setMem MachineState.getMem;rfl)

def haltState (s : MachineState) :=
  execInstrBr (((execInstrBr s (.ADDI .x5 .x0 1)).setPC (pcAt 665))) (.ADDI .x10 .x0 0)

theorem halt (s : MachineState) (pc : s.pc=returnPC) (fuel : Nat) (coins : Bool) :
    execute (Code.image .opening) (4+fuel) s coins =
      pure ⟨.success,haltState s,4,0⟩ := by
  let t:=execInstrBr s (.ADDI .x5 .x0 1)
  let u:=t.setPC (pcAt 665)
  have oneA:=one (c:=.opening) (n:=12624) (by decide) pc (.ADDI .x5 .x0 1) (by apply stood; decide) (show ordinaryStep s _=some t from rfl)
  have pcT : t.pc=pcAt 12625 := by change s.pc+4=_;rw [pc] <;> rfl
  have oneB:=Codec.returnOpen t pcT
  have oneC:=one (c:=.opening) (n:=665) (by decide) (show u.pc=pcAt 665 from rfl) (.ADDI .x10 .x0 0)
    (by apply stood; decide) (show ordinaryStep u _=some (haltState s) from rfl)
  have run:=((oneA.trans oneB).trans oneC) (fuel+1) coins
  have pcH : (haltState s).pc=pcAt 666 := rfl
  have sys : fetch (Code.image .opening) (haltState s)=some (.base .ECALL) :=
    (fetched .opening 666 (by decide) _ pcH).trans (by apply stood; decide)
  rw [show 4+fuel=fuel+1+(1+1+1) by omega,run,show fuel+1=Nat.succ fuel by rfl,execute,sys]
  simp [show (haltState s).getReg .x5=1 by rfl,show (haltState s).getReg .x10=0 by rfl,Execution.charge,instructionCycles]
end CommitGolfCandidate.R1b.Opening
