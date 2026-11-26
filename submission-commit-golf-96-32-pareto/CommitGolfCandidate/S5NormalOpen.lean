import CommitGolfCandidate.S5OrdinaryRecords
import CommitGolfCandidate.S5OpenOutput
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late (Levels SaltTape)
attribute [local irreducible] execute List.range records ordinaryCost readBuffer 

theorem normal_open (td : Trapdoor) (ps : Positions) (tree : Levels) (salt : SaltTape)
    (agree : TrapdoorAgrees td tree salt) (normal : ps.card≠BATCH) :
    ∃ result : Execution, Artifact.submission.run .opening (td,ps)=pure result ∧ result.exit=.success ∧
      Artifact.submission.openingSucceeded result=true ∧ result.oracleCalls=0 ∧
      Artifact.submission.readProof result=S5.opening tree salt ps := by
  let xs:=indices ps
  let s:=initial td ps
  have count : xs.length=ps.card := Finset.length_sort ..
  have size : ps.card≤LENGTH := by simpa using Finset.card_le_univ ps
  have cap : ps.card≤16777216:=size
  have no : ps.card≠128:=normal
  have wide : S5.opening tree salt ps=xs.flatMap (normalBytes tree salt) := normal_opening tree salt ps normal
  rw [open_abi,wide]
  by_cases empty : ps.card=0
  · have countReg : s.getReg .x16=W ps.card := rfl
    have zero : s.getReg .x16=0 := by rw [countReg,empty];rfl
    obtain ⟨run,len⟩:=empty_open_run s rfl zero 68719476731
    let t:=pathEnd s emptyOpenPath
    have noBytes : HasBytes t proofBase [] := fun _ h=>by simp at h
    obtain ⟨ok,data⟩:=read_proof t 5 [] len (by decide) noBytes
    have xs0 : xs=[] := List.length_eq_zero_iff.mp (count.trans empty)
    exact ⟨⟨.success,t,5,0⟩,run,rfl,ok,rfl,by simpa only [xs0,List.flatMap_nil] using data⟩
  · obtain ⟨u,head,pc,seed,gp,table,source,_⟩:=enter_initial td ps tree salt agree (by omega)
    simp only [no,decide_false,Bool.false_eq_true,ite_false] at head pc seed
    have room : AddrOK proofBase (824*ps.card) := by constructor <;> first | decide | (change 13421772800+824*ps.card≤2^36;omega)
    have first : OrdinaryRegs u 0 xs.length proofBase := by
      refine ⟨pc.trans (by rw [if_pos (by omega)]),gp,?_,?_,seed.salts,seed.radix,seed.start,seed.dest⟩
      · simpa using seed.indices
      · simpa only [count,Nat.sub_zero] using seed.count rfl
    obtain ⟨t,body,reg,written⟩:=ordinary_records xs tree salt 0 ps.card proofBase u (by omega) (count ▸ size) first table source le_rfl room
    have whole:=head.trans body
    let steps:=113+ordinaryCost xs 0 ps.card
    let cycles:=113+(ordinaryCost xs 0 ps.card+12*ps.card)
    let spare:=68719476736-(steps+4)
    have price:=ordinary_cost_bound xs 0 ps.card
    have fuel : 68719476736=(spare+4)+steps := by dsimp [steps,spare];omega
    have repr : records xs tree salt 0 ps.card=xs.flatMap (normalBytes tree salt) := by
      rw [records_eq _ _ _ _ _ (by omega),List.drop_zero,← count,List.take_length]
    have endPC : t.pc=pcAt 989:=reg.pc.trans (by rw [if_neg (Nat.lt_irrefl _)])
    obtain ⟨halt,len,mem⟩:=ordinary_exit t endPC (824*ps.card) reg.proof reg.dest spare
    have final : execute image 68719476736 s true=pure ⟨.success,reported t,cycles+4,0⟩ := by
      rw [fuel,whole,halt,pure_bind];rfl
    have bytes:=written.congr_mem (s':=u) rfl mem
    have length:=records_length xs tree salt 0 ps.card
    have ptr : (reported t).getReg .x11=W (records xs tree salt 0 ps.card).length := by rw [length];exact len
    have facts:=read_proof (reported t) (cycles+4) _ ptr (by rw [length];omega) bytes.data
    exact ⟨_,final,rfl,facts.1,rfl,facts.2.trans repr⟩
end CommitGolfCandidate.S5Machine.Open
