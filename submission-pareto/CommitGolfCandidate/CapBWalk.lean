import CommitGolfCandidate.CapBWalkApi
import CommitGolfCandidate.CapBFlow
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open TwoPermutationPrototype.GroupedOpening (openingImage leafMask chunkEntries chunkNode)
open TwoPermutationPrototype.GroupedOpening.CapB (handlerLen handlers control entryLen chunkPrice)
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

private theorem shl_addr (n k : Nat) : addr n <<< k=addr (n*2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addr,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mod_mul_mod]
theorem add_addr (a b : Nat) : addr a+addr b=addr (a+b) := (BitVec.ofNat_add ..).symm
private theorem parity0 : ∀ n : Fin 64,(addr (2*n.val) &&& 1#64)=0#64 ∧ (addr (2*n.val+1) &&& 1#64)=1#64 ∧
    (addr (2*n.val+1) >>> (1:Nat))=addr n.val := by decide +kernel
private theorem targetBlock : ∀ n : Fin 256, ((36864#64+(addr n.val <<< (6:Nat)))+128#64 &&& ~~~1#64)=pc (chunkBlockWord n.val) := by decide +kernel
theorem w702 : (openingImage.code[702]?).bind decodeInstruction=some (.base (.JALR .x18 .x19 0)) := rfl

def walkCost (gs : List Nat) (node h start : Nat) :=
  control gs node h + (handlers (start+(capFrontierNodes gs node (h+3)).length)-handlers start)

theorem handlers_mono (s n : Nat) : handlers s≤handlers (s+n) := by
  induction n with | zero => rfl | succ j ih => rw [Nat.add_succ,handlers];omega

private theorem sameCost {a b c d} (h : Run openingImage a b c c) (eq : c=d) : Run openingImage a b d d := eq ▸ h

theorem walk {gs} (api : API gs) (h n : Nat) (xs : List Nat) (s : MachineState)
    (small : h≤5) (span : 32≤n*2^h ∧ (n+1)*2^h≤64) (root : n=1 → capIsMarked gs n (h+3)=true)
    (room : xs.length+(capFrontierNodes gs n (h+3)).length≤256)
    (inv : api.inv xs s) (here : s.pc=pc 661) (node : s.getReg .x6=addr n) :
    ∃ t, Run openingImage s t (walkCost gs n h xs.length) (walkCost gs n h xs.length) ∧
      t.pc=(if n=1 then pc 707 else pc 703) ∧ api.inv (xs++capFrontierNodes gs n (h+3)) t ∧ t.getReg .x6=addr n := by
  induction h using Nat.strong_induction_on generalizing n xs s with
  | h h ih =>
    have zspan:=span.1;have zbound:=span.2
    have nn : 0<n := by by_contra! z;simp [Nat.eq_zero_of_le_zero z] at zspan
    have hn : n<64 := by nlinarith [Nat.one_le_two_pow (n:=h)]
    have constants:=api.constants inv
    have ptr : s.getReg .x26+(s.getReg .x6 <<< (3:Nat))=addr (markBase+8*n) := by
      rw [constants.1,node,shl_addr,add_addr];congr 1;omega
    obtain ⟨a,ra,pa,ma,regA⟩:=nav_visit s here (by rw [ptr];apply access_ok <;> dsimp [markBase,MEMORY_BYTES] <;> omega)
    have ia:=api.move inv (show Moved s a from ⟨ma,by intro r f;cases r <;> first | exact False.elim ((by decide : _∉savedRegs) f) | simp [regA]⟩)
    have lev : a.getReg .x16=addr (8*n) := by simp [regA,node,shl_addr,Nat.mul_comm]
    have a6 : a.getReg .x6=addr n := by simp [regA,node]
    have read:=api.mark inv n h zspan zbound
    rw [ptr,read] at pa regA
    by_cases marked : capIsMarked gs n (h+3)=true
    case neg =>
      have unmarked : capIsMarked gs n (h+3)=false := Bool.eq_false_iff.mpr marked
      have noRoot : n≠1 := fun e=>marked (root e)
      have zero:= (tree_zero gs n _).2 unmarked
      have atA : a.pc=pc 702 := by simpa [zero] using pa
      have single : capFrontierNodes gs n (h+3)=[n] := by rw [show h+3=(h+2)+1 by omega,capFrontierNodes,if_neg marked]
      obtain ⟨b,rb,pb,ib,nb,_⟩:=api.call ia (by rw [single] at room;simp only [List.length_singleton] at room;omega) (by decide) (by omega) a6 atA w702
      refine ⟨b,?_,by simpa [noRoot] using pb,by simpa only [single] using ib,nb⟩
      have joint:=ra.thenDo rb
      unfold walkCost;rw [single];have ctrl : control gs n h=5 := by cases h <;> simp only [TwoPermutationPrototype.GroupedOpening.CapB.control,unmarked,Bool.false_eq_true,ite_false]
      rw [ctrl];simp only [List.length_singleton,handlers,Nat.add_sub_cancel_left]
      simpa only [←Nat.add_assoc] using joint
    have nz : treeWord gs n h≠0#64 := by intro eq;have bad:=(tree_zero gs n _).1 eq;rw [marked] at bad;contradiction
    have atA : a.pc=pc 665 := by simpa [nz] using pa
    obtain ⟨b,rb,pb,mb,regB⟩:=nav_level a atA
    have ib:=api.move ia (show Moved a b from ⟨mb,fun r _=>regB r⟩)
    rw [lev,(api.constants ia).2.1] at pb
    cases h with
    | zero =>
      have bottom : 32≤n := by simpa using zspan
      have u : BitVec.ult (addr (8*n)) 256#64=false := by simp [BitVec.ult,addr,Nat.mod_eq_of_lt (show 8*n<2^64 by omega)];omega
      have toChunk : b.pc=pc 668 := by simpa [u] using pb
      obtain ⟨d,rd,pd,md,regD⟩:=nav_dispatch b toChunk
      have id:=api.move ib (show Moved b d from ⟨md,by intro r f;cases r <;> first | exact False.elim ((by decide : _∉savedRegs) f) | simp [regD]⟩)
      let mask:=leafMask gs n
      have hmask:=TwoPermutationPrototype.GroupedOpening.leaf_mask_lt gs n
      have maskR : b.getReg .x28=addr mask := by rw [regB,regA];rfl
      have begin : d.pc=pc (chunkBlockWord mask) := by rw [pd,maskR];exact targetBlock ⟨mask,hmask⟩
      have nonzero : mask≠0 := (TwoPermutationPrototype.GroupedOpening.mask_marked_iff _ hmask).1 ((TwoPermutationPrototype.GroupedOpening.chunk_marked gs n).symm ▸ marked)
      have frontier:=TwoPermutationPrototype.GroupedOpening.chunk_frontier gs n
      obtain ⟨t,rt,pt,it,nT⟩:=entries api n hn (chunkEntries mask) (chunkBlockWord mask) xs d
        (fun j hj=>block_instr mask j hmask nonzero hj) (by unfold chunkBlockWord;omega)
        (by have fit:=block_fits mask hmask nonzero; have w : chunkBlockWord mask≤12304 := by unfold chunkBlockWord;omega; done
            omega)
        (fun r hr=>chunk_entries_range mask hmask nonzero r hr)
        (by rw [frontier,List.length_map] at room;exact room) begin
        (by simpa [regD,regB] using lev) id
      have joint:=((ra.thenDo rb).thenDo rd).thenDo rt
      refine ⟨t,?_,by simpa [show n≠1 by omega] using pt,by simpa only [frontier] using it,nT⟩
      unfold walkCost;rw [frontier,List.length_map]
      simp only [TwoPermutationPrototype.GroupedOpening.CapB.control,marked,ite_true,chunkPrice,entriesPrice] at joint ⊢
      apply sameCost joint;dsimp only [entriesPrice,mask];omega
    | succ h =>
      have upper : n<32 := by rw [Nat.pow_succ] at zbound;nlinarith [Nat.one_le_two_pow (n:=h)]
      have u : BitVec.ult (addr (8*n)) 256#64=true := by simp [BitVec.ult,addr,Nat.mod_eq_of_lt (show 8*n<2^64 by omega)];omega
      have next : b.pc=pc 666 := by simpa [u] using pb
      obtain ⟨c,rc,pcC,mc,regsC⟩:=nav_descend b next
      have ic:=api.move ib (show Moved b c from ⟨mc,by intro r f;cases r <;> first | exact False.elim ((by decide : _∉savedRegs) f) | simp [regsC]⟩)
      let L:=capFrontierNodes gs (2*n) (h+3);let R:=capFrontierNodes gs (2*n+1) (h+3)
      have front : capFrontierNodes gs n (h+1+3)=L++R := by
        rw [show h+1+3=(h+3)+1 by omega,capFrontierNodes,if_pos marked]
      have room' : xs.length+L.length+R.length≤256 := by rw [front,List.length_append] at room;omega
      rw [Nat.pow_succ] at zspan zbound
      obtain ⟨d,rd,pd,id,nd⟩:=ih h (by omega) (2*n) xs c (by omega) ⟨by nlinarith,by nlinarith [Nat.one_le_two_pow (n:=h)]⟩
        (by intro no;omega) (by change xs.length+L.length≤256;omega) ic pcC (by simp [regsC,regB,a6,shl_addr,Nat.mul_comm])
      have par:=parity0 ⟨n,hn⟩
      have atD : d.pc=pc 703 := by simpa [show 2*n≠1 by omega] using pd
      obtain ⟨e,re,pe,me,regE⟩:=nav_parity d atD
      have ie:=api.move id (show Moved d e from ⟨me,by intro r f;cases r <;> first | exact False.elim ((by decide : _∉savedRegs) f) | simp [regE]⟩)
      have atE : e.pc=pc 660 := by rw [pe,nd,par.1];rfl
      obtain ⟨f,rf,pf,mf,regsF⟩:=nav_right e atE
      have iF:=api.move ie (show Moved e f from ⟨mf,by intro r f;cases r <;> first | exact False.elim ((by decide : _∉savedRegs) f) | simp [regsF]⟩)
      obtain ⟨g,rg,pg,ig,ng⟩:=ih h (by omega) (2*n+1) (xs++L) f (by omega)
        ⟨by nlinarith [Nat.one_le_two_pow (n:=h)],by nlinarith⟩
        (by intro no;omega) (by simpa [L,R] using room') iF pf (by simp [regsF,regE,nd,show (1#64)=addr 1 from rfl,add_addr])
      have atG : g.pc=pc 703 := by simpa only [if_neg (show 2*n+1≠1 by omega)] using pg
      obtain ⟨i,ri,pi,mi,regI⟩:=nav_parity g atG
      have ii:=api.move ig (show Moved g i from ⟨mi,by intro r f;cases r <;> first | exact False.elim ((by decide : _∉savedRegs) f) | simp [regI]⟩)
      have atI : i.pc=pc 705 := by rw [pi,ng,par.2.1];rfl
      obtain ⟨t,rt,pt,mt,regT⟩:=nav_climb i atI
      have it:=api.move ii (show Moved i t from ⟨mt,by intro r f;cases r <;> first | exact False.elim ((by decide : _∉savedRegs) f) | simp [regT]⟩)
      have child : i.getReg .x6=addr (2*n+1) := by simpa [regI] using ng
      rw [child,par.2.2,(api.constants ii).2.2] at pt
      have joint:=(((((((ra.thenDo rb).thenDo rc).thenDo rd).thenDo re).thenDo rf).thenDo rg).thenDo ri).thenDo rt
      refine ⟨t,?_,?_,by simpa [front,List.append_assoc,L,R] using it,by simp [regT,child,par.2.2]⟩
      · have ba:=handlers_mono xs.length L.length
        have bb:=handlers_mono (xs.length+L.length) R.length
        unfold walkCost at joint ⊢;rw [front,List.length_append,TwoPermutationPrototype.GroupedOpening.CapB.control,if_pos marked]
        simp only [List.length_append,←Nat.add_assoc] at joint ⊢
        apply sameCost joint;dsimp only [L,R] at ba bb ⊢;omega
      · by_cases z : n=1
        · simpa [z,addr] using pt
        · have diff : addr n≠1#64 := by intro eq;have q:=congrArg BitVec.toNat eq;change n%2^64=1 at q;omega
          simpa [z,diff] using pt

end CommitGolfCandidate.CapB
