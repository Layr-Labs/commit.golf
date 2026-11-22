import CommitGolfCandidate.CapBLabels
import CommitGolfCandidate.CapBBlocks
namespace CommitGolfCandidate.CapB.Symbol
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.GroupedOpening (capOffset foldNodes fold_nodes_append fold_nodes_length fold_nodes_eq fold_nodes_short foldPack8 foldSlot fold_slot foldSlot_length plain30 partial_slot slot_getLsbD)
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
private theorem uniformGet {α β : Type} (f : α → List β) (L : Nat) : ∀ (xs : List α),
    (∀ a ∈ xs, (f a).length=L) → ∀ m j, (hm : m<xs.length) → j<L → (xs.flatMap f)[L*m+j]?=(f xs[m])[j]?
  | [], _, m, j, hm, _ => absurd hm (by simp)
  | x :: rest, hL, m, j, hm, hj => by
    have hx : (f x).length=L := hL x (by simp)
    rw [List.flatMap_cons]
    cases m with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by omega)]
      rfl
    | succ m =>
      rw [List.getElem?_append_right (by rw [hx]; nlinarith), hx,
        show L*(m+1)+j-L=L*m+j by rw [Nat.mul_succ]; omega]
      exact uniformGet f L rest (fun a ha => hL a (List.mem_cons_of_mem _ ha)) m j
        (by simpa using hm) hj

private theorem digest_get (v : D) (j : Nat) (small : j<32) :
    (digestBytes v)[j]?.getD 0=v.extractLsb' (8*j) 8 := by
  unfold digestBytes;rw [List.getElem?_eq_getElem (by simpa using small),Option.getD_some,List.getElem_ofFn]
private theorem slot_bit (x : D) (c : BitVec 2) (j b : Nat) (hj : j<30) (hb : b<8) :
    ((Quartet.packedSlot x c)[j]?.getD 0).getLsbD b=
      if 8*j+b<238 then x.getLsbD (8*j+b) else c.getLsbD (8*j+b-238) := by
  unfold Quartet.packedSlot proofDigestBytes
  simp only [ite_true,List.getElem?_take_of_lt hj,digest_get _ j (show j<32 by omega),BitVec.getLsbD_extractLsb',hb,decide_true,Bool.true_and]
  rw [slot_getLsbD];simp only [show 8*j+b<240 by omega,ite_true]

theorem full_bit (d : Nat→D) (clean : ∀ n,n<7 → (d n).extractLsb' 238 18=0)
    (q b : Nat) (hq : q<238) (hb : b<8) :
    ((foldPack8 d)[q]?.getD 0).getLsbD b=
      if 8*(q%30)+b<238 then (d (q/30)).getLsbD (8*(q%30)+b)
      else (d 7).getLsbD (224+2*(q/30)+(8*(q%30)+b-238)) := by
  unfold foldPack8
  have lens : ((List.range 7).flatMap fun k=>foldSlot (d k) (d 7) k).length=210 := by simp [List.length_flatMap,foldSlot_length]
  by_cases head : q<210
  · rw [List.getElem?_append_left (by omega)]
    let j:=q/30;let lane:=q%30
    have small : j<7 := by dsimp [j];omega
    have inside : lane<30 := by dsimp [lane];omega
    have eq:=uniformGet (fun k=>foldSlot (d k) (d 7) k) 30 (List.range 7) (fun k _=>foldSlot_length ..) j lane (by simpa using small) inside
    simp only [List.getElem_range] at eq
    rw [show 30*j+lane=q by dsimp [j,lane];omega] at eq
    rw [eq,fold_slot _ _ _ small (clean _ small),slot_bit _ _ _ _ inside hb]
    change (if 8*lane+b<238 then _ else _)=if 8*lane+b<238 then _ else _
    split
    · rfl
    · rename_i high;rw [BitVec.getLsbD_extractLsb'];simp [show 8*lane+b-238<2 by omega,j,lane]
  · have q7 : q/30=7 := by omega
    have rem : q%30=q-210 := by omega
    rw [List.getElem?_append_right (by omega),lens,List.getElem?_take_of_lt (by omega),digest_get _ _ (by omega),
      BitVec.getLsbD_extractLsb',q7,rem,if_pos (by omega)];simp [hb]

private theorem read_tag (ds : List D) (n b : Nat) (small : b<256) :
    ([256*n+b] : List Nat).any (readBit ds)=(ds.getD n 0).getLsbD b := by
  simp [readBit,show (256*n+b)/256=n by omega,show (256*n+b)%256=b by omega]

theorem canonical_bit (ds : List D) (clean : ∀ v∈ds,v.extractLsb' 238 18=0) (a b : Nat)
    (ha : a<Layout2.Cap.size ds.length) (hb : b<8) :
    ((foldNodes ds)[a]?.getD 0).getLsbD b=(oldTags ds.length (8*a+b)).any (readBit ds) := by
  let g:=a/238;let q:=a%238;let j:=q/30;let lane:=q%30;let bit:=8*lane+b
  have gfit : 8*g≤ds.length := by dsimp [g];unfold Layout2.Cap.size at ha;omega
  let pre:=ds.take (8*g);let rest:=ds.drop (8*g)
  have join : pre++rest=ds := List.take_append_drop _ _
  have prelen : pre.length=8*g := by simp [pre,gfit,Nat.min_eq_left]
  have sizePre : (foldNodes pre).length=238*g := by rw [fold_nodes_length,prelen];unfold capOffset;omega
  have count : rest.length=ds.length-8*g := by simp [rest]
  have get (i : Nat) : rest.getD i 0=ds.getD (8*g+i) 0 := by simp only [rest,List.getD_eq_getElem?_getD,List.getElem?_drop]
  have source (i : Nat) (bound : i<rest.length) : (rest.getD i 0).extractLsb' 238 18=0 := by
    apply clean;rw [List.getD_eq_getElem rest 0 bound];exact List.mem_of_mem_drop (List.getElem_mem _)
  have qfit : q<238 := by dsimp [q];omega
  have jfit : j<8 := by dsimp [j];omega
  have lfit : lane<30 := by dsimp [lane];omega
  have bfit : bit<240 := by dsimp [bit];omega
  have numeric : (8*a+b)/1904=g ∧ (8*a+b)%1904/240=j ∧ (8*a+b)%1904%240=bit := by
    dsimp [g,j,lane,bit,q];omega
  have offset : (foldNodes ds)[a]?=(foldNodes rest)[q]? := by
    rw [←join,fold_nodes_append _ _ (by omega),List.getElem?_append_right (by dsimp [g] at *;omega),sizePre]
    congr 1;dsimp [q,g];omega
  rw [offset,oldTags,numeric.1,numeric.2.1,numeric.2.2]
  by_cases full : 8≤rest.length
  · rw [fold_nodes_eq,if_pos full,List.getElem?_append_left (by rw [TwoPermutationPrototype.GroupedOpening.foldPack8_length];exact qfit),
      full_bit _ (fun i h=>source i (by omega)) q b qfit hb]
    change (if bit<238 then _ else _)=_
    by_cases low : bit<238
    · rw [if_pos low,if_pos low,read_tag _ _ _ (by omega),get]
    · rw [if_neg low,if_neg low,if_pos (by omega),read_tag _ _ _ (by omega),get]
  · have jroom : j<rest.length := by dsimp [j,q,g] at *;unfold Layout2.Cap.size at ha;omega
    have rr : 30*j+lane=q := by dsimp [j,lane];omega
    have eq:=uniformGet plain30 30 rest (fun v _=>by simp [plain30,digestBytes]) j lane jroom lfit
    rw [rr] at eq
    rw [fold_nodes_short rest (by omega),eq,show plain30 rest[j]=Quartet.packedSlot rest[j] 0 from partial_slot _ (clean _ (List.mem_of_mem_drop (List.getElem_mem _))),
      slot_bit _ _ _ _ lfit hb,←List.getD_eq_getElem rest 0 jroom,get]
    change (if bit<238 then _ else _)=_
    by_cases low : bit<238
    · rw [if_pos low,if_pos low,read_tag _ _ _ (by omega)]
    · rw [if_neg low,if_neg low,if_neg (by omega)]
      exact BitVec.getLsbD_zero (w:=2) (i:=8*lane+b-238)
end CommitGolfCandidate.CapB.Symbol
