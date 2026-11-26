import CommitGolfCandidate.R1bCheckRoute
import CommitGolfCandidate.TwoPermutationPackedCheckerExit
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.R1b
open R1bPC (pcAt)
open Machine (W Runs one)
open RV64 (wordAddress memoryView)
set_option maxRecDepth 8192

structure Header (x : CheckInput) (s : MachineState) extends DecoderFrame s x : Prop where
  pc : s.pc=4100
  factor : s.getReg .x6=500
  root : s.getReg .x11=4294971392
  indices : s.getReg .x13=5905584160
  values : s.getReg .x14=6039801952
  proof : s.getReg .x15=10334769248
  count : s.getReg .x16=W x.positions.card
  length : s.getReg .x17=W x.proof.length

def bad (x : CheckInput) := Route.ofInput x=.low ∨ Route.ofInput x=.high

private def returnHeader (s : MachineState) := (execInstrBr s (.ADDI .x6 .x0 500)).setPC (pcAt 1)

private theorem finishRoute (s : MachineState) (pc : s.pc=pcAt 10525) :
    Runs .check s (returnHeader s) 2 2 := by
  let t:=execInstrBr s (.ADDI .x6 .x0 500)
  have first:=one (c:=.check) (n:=10525) (by decide) pc _ (show decodeInstruction (Machine.Code.word .check 10525)=some (.base (.ADDI .x6 .x0 500)) from Machine.stood (by decide))
    (by rfl : ordinaryStep s _=some t)
  have ip : t.pc=pcAt 10526:=by change s.pc+4=_;rw [pc] <;> rfl
  exact first.trans (Codec.returnWideCheck t ip)

theorem front (x : CheckInput) (fits : x.proof.length≤8388615680) (ok : ¬bad x) :
    ∃ s steps cycles,steps≤10200 ∧ Runs .check (initial x) s steps cycles ∧ Header (wideInput x) s := by
  obtain ⟨t,run,ip,mem,length,ptr,keep⟩:=routeRun x fits
  have prev : ByteImage t x := by intro a _;simp only [Machine.byte,MachineState.getByte,MachineState.getMem,mem]
  have make (u : MachineState) (f : DecoderFrame u (wideInput x)) (atPC : u.pc=pcAt 10525)
      (len : u.getReg .x17=W (wideInput x).proof.length)
      (saved : ∀ reg,reg∈[Reg.x11,.x13,.x14,.x15,.x16] → u.getReg reg=(initial x).getReg reg) :
      Header (wideInput x) (returnHeader u) := by
    refine ⟨⟨?_,f.marks⟩,rfl,rfl,?_,?_,?_,?_,?_,len⟩
    · rcases f.input with ⟨tail,size,frame⟩;exact ⟨tail,size,frame⟩
    · exact saved .x11 (by decide)
    · exact saved .x13 (by decide)
    · exact saved .x14 (by decide)
    · exact saved .x15 (by decide)
    · exact saved .x16 (by decide)
  by_cases full : Route.ofInput x=.packed
  · have facts : x.positions.card=BATCH ∧ x.proof.length=67489 ∧ 117≤frontierCount x ∧ frontierCount x≤128 := by
      unfold Route.ofInput at full;split_ifs at full <;> try contradiction
      exact ⟨by change _=128;omega,by omega,by omega,by omega⟩
    have here : t.pc=pcAt 396 := by rw [ip,show Route.ofInput x=.packed from full] <;> rfl
    obtain ⟨u,cm,done,body⟩:=Codec.realCodec true t here (ptr full)
    have decoded:=decodedFrame x u facts.1 facts.2.1 (decodedImage x t u prev facts.2.1 cm.memory)
    have actualLen : (wideInput x).proof.length=64000+30*frontierCount x := by
      simp [wideInput,Hybrid.wideProof,Carry.batchDecode,facts.1,facts.2.1,List.length_take,Carry.wide_length,
        frontierCount,Nat.min_eq_left (show 64000+30*(Carry.read x.proof 67488).toNat≤67840 by change 64000+30*frontierCount x≤67840;omega)]
    refine ⟨_,_,_,?_,(run.trans body).trans (finishRoute u done),make u decoded done ?_ ?_⟩
    · change (Route.ofInput x).code.length+10129+2≤10200;rw [full];decide
    · rw [cm.keep .x17 (by decide),length,if_pos full,actualLen]
    · intro reg hr
      have stable : Codec.stable reg := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide
      exact (cm.keep _ stable).trans (keep reg hr)
  · have skip : Route.ofInput x=.count ∨ Route.ofInput x=.length := by
      cases e:Route.ofInput x with
      | count => exact Or.inl rfl
      | length => exact Or.inr rfl
      | low => exact False.elim (ok (Or.inl e))
      | high => exact False.elim (ok (Or.inr e))
      | packed => exact False.elim (full e)
    have enter : t.pc=pcAt 10525 := by rcases skip with eq|eq <;> rw [ip,eq] <;> rfl
    have same : wideInput x=x := by
      rcases skip with eq|eq <;> unfold Route.ofInput at eq <;> split_ifs at eq <;> try contradiction
      all_goals simp_all [wideInput,Hybrid.wideProof,Carry.batchDecode,BATCH]
    have dec : DecoderFrame t (wideInput x) := by
      rw [same]
      refine ⟨⟨[],by change _≤8858378240;simp;omega,?_⟩,?_⟩
      · simp only [List.append_nil];intro w hw _;exact prev.word w hw
      · intro n hn;exact (prev.word _ (by omega)).trans (TwoPermutationPrototype.Checker.check_mark_zero x n hn)
    refine ⟨_,_,_,?_,run.trans (finishRoute t enter),make t dec enter ?_ keep⟩
    · change (Route.ofInput x).code.length+2≤10200;rcases skip with e|e <;> rw [e] <;> decide
    · rw [length,if_neg full,same]

theorem badRun (x : CheckInput) (fits : x.proof.length≤8388615680) (invalid : bad x) :
    ∃ result : Execution,execute packedImage 34359803904 (initial x) false=pure result ∧ result.exit=.failure := by
  obtain ⟨t,run,ip,_,_,_,_⟩:=routeRun x fits
  rcases invalid with e|e
  all_goals
    have here : t.pc=pcAt 10527 := by rw [ip,e] <;> rfl
    have skip:=Codec.rejectTag t here
    let n:=(Route.ofInput x).code.length+1
    have fits : n+3≤34359803904 := by dsimp [n];rw [e];decide
    let fuel:=34359803904-n-3
    have eq : 34359803904=(3+fuel)+n := by dsimp [fuel];omega
    have chain:=(run.trans skip) (3+fuel) false
    change execute (Artifact.submission.image .check) ((3+fuel)+n) _ false=_ at chain
    simp only [Machine.Code.image,delivered_check_image] at chain
    rw [execute_header_reject (t.setPC (pcAt 364)) rfl fuel] at chain
    simp only [pure_bind] at chain
    rw [eq]
    exact ⟨_,chain,rfl⟩
end TwoPermutationPrototype.Packed.Checker
