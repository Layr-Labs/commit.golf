import CommitGolfCandidate.CapBFlushCore
import CommitGolfCandidate.CapBBytes
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening (openingImage)
open TwoPermutationPrototype.GroupedOpening.CapB (flushBytes flushPrice)
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000

private theorem flush_lengths : ∀ p : Fin 32,p.val≠0 → 5+(flushCore (flushBytes p.val)).length+1=flushPrice p.val := by decide +kernel

theorem slot (p : Fin 32) (nonzero : p.val≠0) (s : MachineState) (B : Nat) (v : Word)
    (here : s.pc=pc (slotWord p.val)) (dst : s.getReg .x21=addr B) (carry : s.getReg .x22=v)
    (alg : B%8=0) (room : B+8≤MEMORY_BYTES) :
    let n:=flushBytes p.val
    let cost:=(flushCore n).length+1
    ∃ t, Run openingImage s t cost cost ∧ t.pc=pc 6662 ∧
      t.getReg .x21=addr (B+n) ∧ t.getReg .x20=s.getReg .x20 ∧ t.getReg .x14=s.getReg .x14 ∧
      Layout2.Writes s t B n (extractByte v) := by
  obtain ⟨code,last⟩:=code_snoc (slice_code (flushCode p))
  let n:=flushBytes p.val
  let w:=slotWord p.val
  have low : w<7000 := by dsimp [w,slotWord];have:=p.isLt;omega
  have choice:= (flushTargets p).2.2.2 nonzero
  have body : ∃ u,Run openingImage s u (flushCore n).length (flushCore n).length ∧
      u.pc=pc (w+(flushCore n).length) ∧ u.getReg .x21=addr (B+n) ∧ u.getReg .x20=s.getReg .x20 ∧
      u.getReg .x14=s.getReg .x14 ∧ u.mem=(s.setMem (addr B) (patch n (gword s B) v)).mem := by
    change CodeAt openingImage w (flushCore n) at code
    change n=2 ∨ n=4 ∨ n=6 ∨ n=8 at choice
    rcases choice with eq|eq|eq|eq <;> rw [eq] at code ⊢
    · exact core2 s w B v here low dst carry alg room code
    · exact core4 s w B v here low dst carry alg room code
    · exact core6 s w B v here low dst carry alg room code
    · exact core8 s w B v here low dst carry alg room code
  obtain ⟨u,ru,pu,du,ou,cu,mu⟩:=body
  let loc:=w+(flushCore n).length
  let t:=execInstrBr u (.JAL .x0 (jalOffset loc 6662))
  have bound : loc<2^40 := by dsimp [loc];rcases choice with a|a|a|a <;> change flushBytes p.val=_ at a <;> simp [n,a,flushCore] <;> omega
  have endRun : Run openingImage u t 1 1 := one bound pu last rfl
  have pt : t.pc=pc 6662 := by change u.pc+signExtend21 (jalOffset loc 6662)=_;rw [pu];exact (flushTargets p).2.2.1
  exact ⟨t,ru.thenDo endRun,pt,du,ou,cu,flushWrites choice alg room (by exact mu)⟩

theorem flush (f B : Nat) (s : MachineState) (v : Word) (here : s.pc=pc 707)
    (phase : s.getReg .x19=pc (startHandler f)) (first : s.getReg .x24=pc 6144)
    (dest : s.getReg .x21=addr B) (carry : s.getReg .x22=v) (align : B%8=0) (room : B+8≤MEMORY_BYTES) :
    ∃ t,Run openingImage s t (2+flushPrice f) (2+flushPrice f) ∧ t.pc=pc 6662 ∧
      t.getReg .x21=addr (B+flushBytes (f%32)) ∧ t.getReg .x20=s.getReg .x20 ∧ t.getReg .x14=s.getReg .x14 ∧
      WritesList s t B ((wordBytes v).take (flushBytes (f%32))) := by
  let p : Fin 32:=⟨f%32,by omega⟩
  have ph : startHandler f=startHandler p.val := by simp [p,startHandler]
  have eqPrice : flushPrice f=flushPrice p.val := by simp [flushPrice,p]
  obtain ⟨a,ra,pa,ma,rA⟩:=nav_finishJump s here
  obtain ⟨b,rb,pb,mb,rB⟩:=nav_flushTest a pa
  rw [rA,rA,phase,ph,first] at pb
  by_cases z : p.val=0
  · have same:=(flushTargets p).2.1.2 z
    have bytes : flushBytes (f%32)=0 := by change flushBytes p.val=0;rw [z];rfl
    have cost : flushPrice f=0 := by rw [eqPrice,z];rfl
    refine ⟨b,by simpa [cost] using ra.thenDo rb,by simpa [same] using pb,by simp [bytes,rB,rA,dest],by simp [rB,rA],by simp [rB,rA],?_⟩
    rw [bytes,List.take_zero];exact (Layout2.writes_zero s _ _).move rfl (mb.trans ma)
  · have diff:=mt (flushTargets p).2.1.1 z
    obtain ⟨c,rc,pcC,mc,rC⟩:=nav_flushJump b (by simpa [diff] using pb)
    have pos : c.pc=pc (slotWord p.val) := by rw [pcC,rB,rB,rA,rA,phase,ph,first];exact (flushTargets p).1
    obtain ⟨t,rt,pt,dt,ot,ct,write⟩:=slot p z c B v pos (by simp [rC,rB,rA,dest]) (by simp [rC,rB,rA,carry]) align room
    have cost:=flush_lengths p z
    have len : 1+1+5+((flushCore (flushBytes p.val)).length+1)=2+flushPrice f := by omega
    exact ⟨t,by simpa only [len] using ((ra.thenDo rb).thenDo rc).thenDo rt,pt,dt,by simpa [rC,rB,rA] using ot,by simpa [rC,rB,rA] using ct,
      carryWrites (flush_range p).1 (write.move (mc.trans (mb.trans ma)).symm rfl)⟩
end CommitGolfCandidate.CapB
