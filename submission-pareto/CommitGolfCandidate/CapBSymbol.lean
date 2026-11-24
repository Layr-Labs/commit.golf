import CommitGolfCandidate.CapBRaw
import CommitGolfCandidate.CapBBytes
namespace CommitGolfCandidate.CapB.Symbol
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening.CapB (carryBits flushBytes)
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

/-- A bit is the OR of its listed source bits. An empty list represents zero. -/
abbrev SWord := Nat→List Nat
def value (f : Nat→Bool) (u : SWord) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 64=>(u i.val).any f))).cast (by simp)
theorem value_bit (f u i) (bound : i<64) : (value f u).getLsbD i=(u i).any f := by
  simp only [value,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using bound : i<(List.ofFn (fun j : Fin 64=>(u j.val).any f)).length),
    Option.getD_some,List.getElem_ofFn]
attribute [local irreducible] value
def zero : SWord := fun _=>[]
def source (n lane : Nat) : SWord := fun b=>if 64*lane+b<238 then [256*n+64*lane+b] else []
def merge (c : Nat) (u t : SWord) : SWord := fun b=>u b++(if c≤b then t (b-c) else [])
def remaining (c : Nat) (t : SWord) : SWord := fun b=>if b+(64-c)<64 then t (b+(64-c)) else []
def carry (j : Nat) (u t : SWord) := if carryBits j=0 then t else if carryBits j≤18 then merge (carryBits j) u t else remaining (carryBits j) t
def words (j : Nat) (u : SWord) (n : Nat) : List SWord :=
  List.ofFn (fun i : Fin (width j)=>if i.val<3 then source n i.val else merge (carryBits j) u (source n 3))

theorem val_merge (f c u t) : value f (merge c u t)=value f u ||| (value f t <<< c) := by
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  rw [value_bit _ _ _ hb,BitVec.getLsbD_or,value_bit _ _ _ hb,BitVec.getLsbD_shiftLeft]
  by_cases h : c≤b
  · simp only [merge,if_pos h,List.any_append,hb,decide_true,show ¬b<c by omega,decide_false,Bool.not_false,Bool.true_and,value_bit f t (b-c) (by omega)]
  · simp [merge,h,hb,show b<c by omega]
theorem val_rem (f c t) : value f (remaining c t)=value f t >>> (64-c) := by
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  rw [value_bit _ _ _ hb,BitVec.getLsbD_ushiftRight]
  by_cases h : b+(64-c)<64
  · simp only [remaining,if_pos h,show 64-c+b=b+(64-c) by omega,value_bit f t _ h]
  · simp [remaining,h,BitVec.getLsbD_of_ge (value f t) _ (by omega : 64≤(64-c)+b)]
theorem val_carry (f j u t) : value f (carry j u t)=nextCarry j (value f u) (value f t) := by
  unfold carry nextCarry merged;split_ifs <;> first | apply val_merge | apply val_rem | rfl

def readBit (ds : List D) (a : Nat) := (ds.getD (a/256) 0).getLsbD (a%256)
theorem val_source {ds : List D} (clean : ∀ d∈ds,d.extractLsb' 238 18=0) (n lane : Nat) (node : n<ds.length) (small : lane<4) :
    value (readBit ds) (source n lane)=dw (ds.getD n 0) lane := by
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  rw [value_bit _ _ _ hb];simp only [dw,BitVec.getLsbD_extractLsb',hb,decide_true,Bool.true_and]
  by_cases low : 64*lane+b<238
  · simp [source,low,readBit,show (256*n+64*lane+b)/256=n by omega,show (256*n+64*lane+b)%256=64*lane+b by omega]
  · have member : ds.getD n 0∈ds := by rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem node,Option.getD_some];apply List.getElem_mem
    have inside : 64*lane+b-238<18 := by omega
    have bit:=congrArg (fun v : BitVec 18=>v.getLsbD (64*lane+b-238)) (clean _ member)
    simp only [BitVec.getLsbD_extractLsb',inside,decide_true,Bool.true_and,BitVec.getLsbD_zero] at bit
    simp [source,low,show 238+(64*lane+b-238)=64*lane+b by omega] at bit ⊢
    first | exact bit.symm | simpa [Nat.add_comm] using bit.symm
structure State where
  out : List SWord
  acc : SWord
def stages : Nat→State
  | 0=>⟨[],zero⟩
  | n+1=>
    let old:=stages n
    ⟨old.out++words (n%32) old.acc n,carry (n%32) old.acc (source n 3)⟩

theorem val_words {ds : List D} (clean : ∀ d∈ds,d.extractLsb' 238 18=0) (n : Nat) (node : n<ds.length) (u : SWord) :
    (words (n%32) u n).map (value (readBit ds))=emittedWords (n%32) (value (readBit ds) u) (ds.getD n 0) := by
  rw [words,List.map_ofFn,emittedWords];congr 1;funext i
  simp only [Function.comp_apply];unfold nextWord merged;split_ifs
  · exact val_source clean n i node (by omega)
  · rw [val_merge,val_source clean n 3 node (by decide)]

theorem model (ds : List D) (clean : ∀ d∈ds,d.extractLsb' 238 18=0) (k : Nat) (hk : k≤ds.length) :
    (stream 0 (ds.take k)).out=(stages k).out.map (value (readBit ds)) ∧
    (stream 0 (ds.take k)).carry=value (readBit ds) (stages k).acc := by
  induction k with
  | zero=>
    refine ⟨rfl,?_⟩;change 0#64=value _ zero
    apply BitVec.eq_of_getLsbD_eq;intro i h;rw [value_bit _ _ _ h,BitVec.getLsbD_zero];rfl
  | succ n ih=>
    obtain ⟨o,a⟩:=ih (by omega)
    have member : n<ds.length := by omega
    have cut : ds.take (n+1)=ds.take n++[ds.getD n 0] := by
      rw [List.take_succ_eq_append_getElem member,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem member,Option.getD_some]
    rw [cut,stream_snoc]
    simp only [push,stages,List.map_append,stream_count,List.length_take,Nat.min_eq_left (by omega : n≤ds.length),o,a,
      val_words clean n member,val_carry,val_source clean n 3 member (by decide),and_self]

/-- All symbolic bits of the actual aligned stores and the low bytes of the flush. -/
def tags (m i : Nat) : List Nat :=
  let st:=stages m
  if i/64<st.out.length then (st.out.getD (i/64) zero) (i%64) else st.acc (i-64*st.out.length)

theorem raw_bit {ds : List D} (clean : ∀ d∈ds,d.extractLsb' 238 18=0) (a b : Nat)
    (ha : a<(capRaw ds).length) (hb : b<8) :
    ((capRaw ds)[a]?.getD 0).getLsbD b=(tags ds.length (8*a+b)).any (readBit ds) := by
  let m:=ds.length;let st:=stream 0 ds;let ss:=stages m
  have hm:=model ds clean ds.length (by omega)
  rw [List.take_length] at hm
  have out : st.out=ss.out.map (value (readBit ds)) := hm.1
  have car : st.carry=value (readBit ds) ss.acc := hm.2
  have len : st.out.length=ss.out.length := by simp [out]
  change (((st.out.flatMap wordBytes)++(wordBytes st.carry).take (flushBytes (m%32)))[a]?.getD 0).getLsbD b=_
  change _=(if (8*a+b)/64<ss.out.length then (ss.out.getD ((8*a+b)/64) zero) ((8*a+b)%64) else ss.acc (8*a+b-64*ss.out.length)).any _
  have flat:=flatWordLength st.out
  by_cases body : a<8*st.out.length
  · rw [List.getElem?_append_left (by omega),if_pos (by omega)]
    let i:=a/8;let j:=a%8
    have hi : i<st.out.length := by dsimp [i];omega
    have hj : j<8 := by dsimp [j];omega
    have off : a=8*i+j := by dsimp [i,j];omega
    conv => lhs; rw [off,flatWordGet _ _ _ hi hj]
    have raw : st.out.getD i 0=value (readBit ds) (ss.out.getD i zero) := by
      rw [out,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem (show i<ss.out.length by omega)];simp [List.getD_eq_getElem?_getD,show i<ss.out.length by omega]
    rw [raw];simp only [extractByte,BitVec.getLsbD_setWidth,hb,decide_true,Bool.true_and,BitVec.getLsbD_ushiftRight]
    rw [value_bit _ _ _ (by omega),show (8*a+b)/64=i by omega,show (8*a+b)%64=j*8+b by omega]
  · rw [List.getElem?_append_right (by omega),if_neg (by omega)]
    let j:=a-8*st.out.length
    have room:=flush_range ⟨m%32,by omega⟩
    have ja : j<flushBytes (m%32) := by
      change a<((st.out.flatMap wordBytes)++(wordBytes st.carry).take (flushBytes (m%32))).length at ha
      simp only [List.length_append,flat,List.length_take,wordBytes,List.length_ofFn] at ha;dsimp [j];omega
    have jb : j<8 := by have bd : flushBytes (m%32)≤8:=room.1;omega
    rw [flat,List.getElem?_take_of_lt ja]
    change (((wordBytes st.carry)[j]?.getD 0).getLsbD b)=_
    unfold wordBytes;rw [List.getElem?_eq_getElem (by simpa using jb),Option.getD_some,List.getElem_ofFn,car]
    simp only [extractByte,BitVec.getLsbD_setWidth,hb,decide_true,Bool.true_and,BitVec.getLsbD_ushiftRight]
    rw [value_bit _ _ _ (by omega)];congr 2;dsimp [j];omega
end CommitGolfCandidate.CapB.Symbol
