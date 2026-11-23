import CommitGolfCandidate.Layout2CapInput
import CommitGolfCandidate.Layout2QuartetLoaded
import CommitGolfCandidate.TwoPermutationPackedHonestInput
import CommitGolfCandidate.Layout2OneByteGuard
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype
open CommitGolfCandidate.Layout2.Quartet (checkImage)
set_option maxHeartbeats 1400000

theorem honest_good (o : Oracle) (msg : Message) (p : Positions) (salts : Index → BitVec 128) :
    Good p.card (QuartetCertificate.honestCheckInput o msg p salts).proof.length := by
  rw [PackedHonest.honest_proof_length,←size_eq]
  apply good_shape
  intro empty;simp [Opening.openingNodes,empty]

private theorem addr_inj {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; rfl

theorem reserve (k len hc hr : Nat) (card : k≤16777216) (fits : len≤8959041024)
    (cap : hc≤200+108*(len-534*k)) (recs : hr≤9+65*k+prologueSteps k) :
    hc+hr+34359803904≤2^41 := by
  unfold prologueSteps tailSteps Layout2.dispatchCost at recs
  split_ifs at recs <;> omega

/-- `reserve` with the entry guard's 8 extra steps. -/
theorem reserve8 (k len hc hr : Nat) (card : k≤16777216) (fits : len≤8959041024)
    (cap : hc≤208+108*(len-534*k)) (recs : hr≤9+65*k+prologueSteps k) :
    hc+hr+34359900000≤2^41 := by
  unfold prologueSteps tailSteps Layout2.dispatchCost at recs
  split_ifs at recs <;> omega

/-- One-byte search (Opus): from word 0 through the entry guard to V2b's cap pass, quartet preparation and V1
prologue, for the effective input (`effective i`: a k = 128 proof of 72,159 bytes read as 72,160 bytes ending in 0). -/
theorem prepare_run (τ : Tables) (wf : WellFormed τ)
    (physical : ∀ j,j<85440 → Layout2Helpers.pget K1Artifact.checkData j=tableByte τ j)
    (i : CheckInput) (fits : i.proof.length≤8959041024) :
    let e:=effective i
    let k:=i.positions.card
    let s:=candidate.initialState .check i
    ∃ t h c, h+34359900000≤2^41 ∧ Runs checkImage s t h c ∧
      (if Good k e.proof.length then Normalized τ (candidate.initialState .check (Quartet.prepared (prepared e))) t k
       else t.pc=pc 364) := by
  dsimp only
  let s:=candidate.initialState .check i
  let e:=effective i
  let s':=candidate.initialState .check e
  let k:=i.positions.card
  have card:=Checker.checker_positions_bound i
  have eLen:=effective_length i
  have eFits : e.proof.length≤8959041024 := by rw [eLen];split <;> omega
  have ePos : e.positions=i.positions := effective_positions i
  obtain ⟨g,hg,cg,rg,hgle,cgle,pg,mg,regG,x17G⟩:=entry_guard s rfl
  have fireIff : guardFires s ↔ fires i := by
    unfold guardFires fires;rw [initial_x16,initial_x17]
    constructor
    · rintro ⟨a,b⟩
      exact ⟨(addr_inj (by omega) (by decide)).mp a,(addr_inj (by omega) (by decide)).mp b⟩
    · rintro ⟨a,b⟩;rw [a,b];exact ⟨rfl,rfl⟩
  have memE : s'.mem=s.mem := by
    by_cases f : fires i
    · have eq : e=pad i := effective_fires i f
      change (candidate.initialState .check e).mem=_;rw [eq]
      apply initial_mem_pad candidate i
      · rw [data_base,f.2];decide
      · rw [f.1];decide
    · have eq : e=i := effective_not i f
      change (candidate.initialState .check e).mem=_;rw [eq]
  have gMem : g.mem=s'.mem := mg.trans memE.symm
  have gReg (r : Reg) (a6 : r≠.x6) (a7 : r≠.x7) : g.getReg r=s'.getReg r := by
    by_cases f : fires i
    · have eq : e=pad i := effective_fires i f
      change _=(candidate.initialState .check e).getReg r;rw [eq]
      by_cases r17 : r=.x17
      · subst r17;rw [x17G,if_pos (fireIff.mpr f),pad_x17,f.2]
      · rw [regG r a6 a7 r17,pad_reg candidate i r r17]
    · have eq : e=i := effective_not i f
      change _=(candidate.initialState .check e).getReg r;rw [eq]
      by_cases r17 : r=.x17
      · subst r17;rw [x17G,if_neg (fun h=>f (fireIff.mp h))]
      · exact regG r a6 a7 r17
  have byteG (q : Nat) : byte g q=byte s' q := by simp only [byte,MachineState.getByte,MachineState.getMem,gMem]
  have args0:=initial_args e eFits
  have args : Input g k e.proof.length := by
    refine ⟨(gReg _ (by decide) (by decide)).trans args0.scratch,(gReg _ (by decide) (by decide)).trans args0.output,
      (gReg _ (by decide) (by decide)).trans args0.stack,(gReg _ (by decide) (by decide)).trans (by rw [args0.card,ePos]),
      (gReg _ (by decide) (by decide)).trans args0.length,card,eFits⟩
  have data : AtData g := fun j hj=>(byteG _).trans (initial_data e eFits j hj)
  have clean : ∀ j,j<952 → byte g (scratchBase+j)=0 := fun j hj=>(byteG _).trans (scratch_clean e j (by omega))
  obtain ⟨m,a,ca,limit,ra,done⟩:=pass g k _ args pg data clean
  have resEq (base n : Nat) : result g base n=result s' base n := by
    unfold result;congr 1;funext j;exact byteG _
  by_cases legal : Good k e.proof.length
  · rw [if_pos legal] at done
    obtain ⟨pcM,wrote,kept⟩:=done
    have prev : Kept temps (candidate.initialState .check (prepared e)) m := by
      intro r free
      have a6 : r≠.x6 := fun h=>free (by subst h;decide)
      have a7 : r≠.x7 := fun h=>free (by subst h;decide)
      exact (kept r free).trans ((gReg r a6 a7).trans (same_args candidate e r))
    have legalE : Good e.positions.card e.proof.length := by rwa [ePos]
    have wroteE : Writes s' m (proofBase+534*e.positions.card) (e.proof.length-534*e.positions.card)
        (result s' (proofBase+534*e.positions.card) (e.proof.length-534*e.positions.card)) := by
      rw [ePos,←resEq];exact wrote.move gMem.symm rfl
    obtain ⟨t,b,cb,le,rb,norm⟩:=Quartet.prepare_from τ wf physical (prepared e) (by simpa using eFits)
      (by simpa only [prepared_len,show (prepared e).positions=e.positions from rfl,ePos] using legal.1)
      m pcM prev (prepared_mem e eFits legalE wroteE)
    refine ⟨t,hg+(a+b),_,?_,rg.thenDo (ra.thenDo rb),?_⟩
    · have:=reserve8 k e.proof.length (hg+a) b card eFits (by omega) (by simpa [show (prepared e).positions=e.positions from rfl,ePos] using le)
      omega
    · rw [if_pos legal];simpa [show (prepared e).positions=e.positions from rfl,ePos] using norm
  · refine ⟨m,hg+a,_,?_,rg.thenDo ra,?_⟩
    · have:=reserve8 k e.proof.length (hg+a) 0 card eFits (by omega) (by omega);omega
    · rw [if_neg legal];rwa [if_neg legal] at done
end CommitGolfCandidate.Layout2.Cap
