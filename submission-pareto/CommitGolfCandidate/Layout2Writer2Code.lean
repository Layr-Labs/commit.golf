import CommitGolfCandidate.Layout2Writer2Program
import CommitGolfCandidate.TwoPermutationPackedFetchBase

namespace CommitGolfCandidate.Layout2Writer2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Writer Layout2Phase OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

def InstrsAt (I : Image) (w : Nat) (ops : List Instr) : Prop :=
  ∀ j : Fin ops.length, (I.code[w+j.val]?).bind decodeInstruction=some (.base (ops[j.val]'j.isLt))

theorem decoded {I p q} (code : ImageAt I p) (hp : p<4) (hq : q<4) (length : 4+(rows p q).length=Layout2Phase2.bodyLen p) :
    InstrsAt I (Layout2Phase2.bodyWord p) (listing p q) := by
  unfold ImageAt at code
  rw [←same_listing ⟨p,hp⟩ ⟨q,hq⟩] at code
  intro i
  have h:=congrArg (fun xs : List (Option Instr)=>xs[i.val]?) code
  have size : (listing p q).length=Layout2Phase2.bodyLen p := by simpa only [listing,List.length_append,List.length_map,show headOps.length=4 from rfl] using length
  have small : i.val<Layout2Phase2.bodyLen p := size ▸ i.isLt
  simp only [List.getElem?_map,List.getElem?_take,small,ite_true,List.getElem?_drop,
    List.getElem?_eq_getElem i.isLt,Option.map_some,Option.some.injEq] at h
  cases word : I.code[Layout2Phase2.bodyWord p+i.val]? with
  | none => simp [word] at h
  | some x =>
    simp only [word,Option.map_some,Option.some.injEq] at h
    unfold decodedBase at h
    cases d : decodeInstruction x with
    | none => simp [d] at h
    | some inst => cases inst <;> simp_all

theorem split_code {I p q} (h : InstrsAt I (Layout2Phase2.bodyWord p) (listing p q)) :
    InstrsAt I (Layout2Phase2.bodyWord p) headOps ∧
    InstrsAt I (Layout2Phase2.bodyWord p+4) ((rows p q).map op) := by
  unfold listing at h
  constructor
  · intro i
    have a:=h ⟨i.val,by simp;have:=i.isLt;omega⟩
    simpa only [List.getElem_append_left i.isLt] using a
  · intro i
    have a:=h ⟨headOps.length+i.val,by simp only [List.length_append];have:=i.isLt;omega⟩
    rw [List.getElem_append_right (show headOps.length≤headOps.length+i.val by omega)] at a
    simpa only [Nat.add_sub_cancel_left,Nat.add_assoc,show headOps.length=4 from rfl] using a

theorem zero_run (I : Image) (s : MachineState) : RunsBlock I s s 0 := by
  intro f coins;simp [Execution.charge]
theorem join_run {I s m t n k} (a : RunsBlock I s m n) (b : RunsBlock I m t k) :
    RunsBlock I s t (n+k) := by
  intro fuel coins;rw [Nat.add_assoc,a,b];simp [bind_assoc,pure_bind,Execution.charge,Nat.add_assoc]
theorem pc_next (w : Nat) : wordAddress w+4=wordAddress (w+1) := by
  unfold wordAddress;change addr _+addr 4=_
  rw [←BitVec.ofNat_add];congr 1 <;> omega

theorem unit {I : Image} (m : MachineState) (w : Nat) (inst : Instr)
    (small : w<2^40) (pc : m.pc=wordAddress w)
    (code : (I.code[w]?).bind decodeInstruction=some (.base inst))
    (ord : ordinaryStep m (.base inst)=some (execInstrBr m inst)) (cost : instructionCycles (.base inst)=1) :
    RunsBlock I m (execInstrBr m inst) 1 := by
  have fetch:=wide_image_fetch I m w inst small pc code
  intro f coin;rw [Nat.add_comm 1 f,execute_ordinary_step _ _ _ _ _ _ fetch ord,cost]

end CommitGolfCandidate.Layout2Writer2
