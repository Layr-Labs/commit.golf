import CommitGolfCandidate.CapBHandlerCode
import CommitGolfCandidate.CapBExecute
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open TwoPermutationPrototype.GroupedOpening (openingImage)
open TwoPermutationPrototype.GroupedOpening.CapB (carryBits handlerLen)
set_option maxRecDepth 14000
set_option maxHeartbeats 1200000

def merged (j : Nat) (acc tail : Word) := acc ||| (tail <<< carryBits j)
def nextCarry (j : Nat) (acc tail : Word) :=
  if carryBits j=0 then tail else if carryBits j≤18 then merged j acc tail else tail >>> (64-carryBits j)
def nextWord (j : Nat) (acc : Word) (src : Nat→Word) (i : Nat) :=
  if i<3 then src i else merged j acc (src 3)
private theorem handler_offset : ∀ j : Fin 32,
    pc (startHandler j)+signExtend12 (BitVec.ofNat 12 (phaseDelta j))=pc (startHandler (j.val+1)) := by decide +kernel
theorem pc_mask (w : Nat) : (pc w &&& ~~~1#64)=pc w := by
  unfold pc addr
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  by_cases z : i=0
  · subst z;simp [Nat.testBit_zero,show (4096+4*w)%2=0 by omega]
  · have one : Nat.testBit 1 i=false := by
      rw [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.div_eq_of_lt (Nat.one_lt_two_pow z)];rfl
    simp [one]

theorem code_snoc {I w xs r} (all : CodeAt I w (xs++[r])) :
    CodeAt I w xs ∧ (I.code[w+xs.length]?).bind decodeInstruction=some (.base r) := by
  constructor
  · intro i
    have eq:=all ⟨i.val,by simp <;> have:=i.isLt <;> omega⟩
    simpa only [List.getElem_append_left i.isLt] using eq
  · have eq:=all ⟨xs.length,by simp⟩
    rw [List.getElem_append_right (Nat.le_refl _)] at eq
    simpa only [Nat.sub_self,List.getElem_cons_zero] using eq

/-- One handler from its first instruction through its return. Inputs may contain dirty high bits. -/
theorem emit (s : MachineState) (j : Fin 32) (ret dst src : Nat) (lim : ret<2^40)
    (here : s.pc=pc (startHandler j)) (phase : s.getReg .x19=pc (startHandler j))
    (link : s.getReg .x18=pc ret) (dest : s.getReg .x21=addr dst)
    (input : s.getReg .x25+(s.getReg .x6 <<< (5:Nat))=addr src)
    (safe : Safe ⟨dst,src,width j,4⟩) :
    ∃ t, Run openingImage s t (handlerLen j) (handlerLen j) ∧ t.pc=pc ret ∧
      t.getReg .x19=pc (startHandler (j.val+1)) ∧ t.getReg .x21=addr (dst+8*width j) ∧
      t.getReg .x22=nextCarry j (s.getReg .x22) (gword s (src+24)) ∧
      (∀ i,i<width j → gword t (dst+8*i)=nextWord j (s.getReg .x22) (fun k=>gword s (src+8*k)) i) ∧
      (∀ r,r∉[.x7,.x28,.x31,.x22,.x21,.x19] → t.getReg r=s.getReg r) ∧
      (∀ w : Word,(∀ i,i<width j → w≠addr (dst+8*i)) → t.getMem w=s.getMem w) := by
  let a : Areas:=⟨dst,src,width j,4⟩
  let rs:=handlerRows j
  let w:=startHandler j
  have valid:=handler_valid j
  obtain ⟨ok,len,cost,carry,dstOut,phaseOut,words⟩:=valid
  obtain ⟨code,tail⟩:=code_snoc (slice_code (handler_code j))
  simp only [List.length_map] at tail
  have bound : w+rs.length<2^40 := by
    have small : handlerLen j≤16 := (show ∀ i : Fin 32,handlerLen i≤16 by decide +kernel) j
    dsimp [w,startHandler,rs];have:=j.isLt;omega
  obtain ⟨u,ran,atU,m⟩:=run (a:=a) (l:=handlerLayout j) safe (by intro r;cases r <;> first | exact dest | exact input)
    (by intro r;cases r <;> rfl) rs w s initial (track_zero ..) here bound code ok
  change Tracks s u a (handlerModel j) at m
  have keep (r : Reg) (h : r∉[.x7,.x28,.x31,.x22,.x21,.x19]) : u.getReg r=s.getReg r := by
    have eq:=m.reg r;rw [handler_keep j r h] at eq;exact eq
  let t:=execInstrBr u (.JALR .x0 .x18 0)
  have last : Run openingImage u t 1 1 := one bound atU tail rfl
  have pcT : t.pc=pc ret := by
    change ((u.getReg .x18+signExtend12 0) &&& ~~~1#64)=_
    rw [keep _ (by decide),link,show signExtend12 0=0#64 from rfl,BitVec.add_zero,pc_mask ret]
  have joined:=ran.thenDo last
  change Run openingImage s t ((handlerRows j).length+1) (price (handlerRows j)+1) at joined
  rw [len,cost] at joined
  refine ⟨t,joined,pcT,?_,?_,?_,?_,?_,m.frame⟩
  · change u.getReg .x19=_;rw [m.reg,phaseOut];simpa only [val,addr,BitVec.ofNat_toNat,BitVec.setWidth_eq,phase] using handler_offset j
  · change u.getReg .x21=_;rw [m.reg,dstOut];simp only [val,dest,addr,←BitVec.ofNat_add]
  · change u.getReg .x22=_;rw [m.reg,carry];unfold carryE nextCarry mergedE merged;split_ifs <;> simp only [val,Areas.key,Areas.start,a,gword]
  · intro i hi;have value:=m.out i hi
    rw [words ⟨i,hi⟩] at value
    change u.getMem (addr (dst+8*i))=_
    unfold nextWord;split <;> rename_i test <;>
      simpa only [test,ite_true,ite_false,val,mergedE,merged,a,Areas.key,Areas.start,gword] using value
  · intro r free;change u.getReg r=_;exact keep r free
end CommitGolfCandidate.CapB
