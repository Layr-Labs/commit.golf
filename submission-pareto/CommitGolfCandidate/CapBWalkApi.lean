import CommitGolfCandidate.CapBChunkCode
import CommitGolfCandidate.CapBPrep
import CommitGolfCandidate.CapBHandler
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening (openingImage leafMask chunkEntries chunkNode depthOf)
open TwoPermutationPrototype.GroupedOpening.CapB (handlerLen handlers entryLen)
open TwoPermutationPrototype.Sampling (capIsMarked cap_marked_children)
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000

def savedRegs : List Reg := [.x14,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27]
def Moved (a b : MachineState) := b.mem=a.mem ∧ ∀ r,r∈savedRegs → b.getReg r=a.getReg r

/-- Local contract for a walk callback; the same handler is invoked at word 702 and from a chunk block. -/
structure API (gs : List Nat) where
  inv : List Nat → MachineState → Prop
  move : ∀ {xs s t},inv xs s → Moved s t → inv xs t
  constants : ∀ {xs s},inv xs s → s.getReg .x26=addr markBase ∧ s.getReg .x27=256 ∧ s.getReg .x23=1
  mark : ∀ {xs s},inv xs s → ∀ n h,32≤n*2^h → (n+1)*2^h≤64 → s.getMem (addr (markBase+8*n))=treeWord gs n h
  call : ∀ {xs s w n},inv xs s → xs.length<256 → w<12320 → n<512 → s.getReg .x6=addr n → s.pc=pc w →
    (openingImage.code[w]?).bind decodeInstruction=some (.base (.JALR .x18 .x19 0)) →
    ∃ t,Run openingImage s t (1+handlerLen xs.length) (1+handlerLen xs.length) ∧ t.pc=pc (w+1) ∧
      inv (xs++[n]) t ∧ t.getReg .x6=addr n ∧ t.getReg .x16=s.getReg .x16

theorem tree_zero (gs : List Nat) (n h : Nat) : treeWord gs n h=0#64 ↔ capIsMarked gs n (h+3)=false := by
  induction h generalizing n with
  | zero =>
    have iff:=TwoPermutationPrototype.GroupedOpening.mask_marked_iff _ (TwoPermutationPrototype.GroupedOpening.leaf_mask_lt gs n)
    rw [←TwoPermutationPrototype.GroupedOpening.chunk_marked] at iff
    have bound:=TwoPermutationPrototype.GroupedOpening.leaf_mask_lt gs n
    have base : addr (leafMask gs n)=0#64 ↔ leafMask gs n=0 := by
      constructor
      · intro e;have v:=congrArg BitVec.toNat e;change leafMask gs n%2^64=0 at v;omega
      · intro e;rw [e] <;> rfl
    rw [treeWord,base];change _ ↔ capIsMarked gs n 3=false
    cases x : capIsMarked gs n 3 <;> simp_all
  | succ h ih =>
    rw [treeWord,show h+1+3=(h+3)+1 by omega,cap_marked_children]
    have oz (a b : Word) : (a ||| b)=0#64 ↔ a=0#64 ∧ b=0#64 := by
      constructor
      · intro e;have v:=congrArg BitVec.toNat e
        rw [BitVec.toNat_or] at v
        have left : a.toNat≤a.toNat ||| b.toNat := Nat.left_le_or
        have right : b.toNat≤a.toNat ||| b.toNat := Nat.right_le_or
        constructor <;> apply BitVec.eq_of_toNat_eq <;> change _=0 <;> change _=0 at v <;> omega
      · rintro ⟨rfl,rfl⟩;rfl
    rw [oz,ih,ih,Bool.or_eq_false_iff]

theorem widen {w : Nat} {op : Instr} (f : (openingImage.code[w]?).bind decodeBase=some op) :
    (openingImage.code[w]?).bind decodeInstruction=some (.base op) := by
  cases v : openingImage.code[w]? with
  | none => simp [v] at f
  | some x =>
    simp only [v,Option.bind_some,decodeBase] at f
    cases d : decodeInstruction x with
    | none => simp [d] at f
    | some o => cases o <;> simp_all

def entriesPrice (xs : List Nat) := (xs.map entryLen).sum

/-- Single-register, unit-priced arithmetic with an independent code lookup. -/
theorem set6 {s : MachineState} {w : Nat} {op : Instr} {v : Word}
    (lim : w<2^40) (here : s.pc=pc w) (code : (openingImage.code[w]?).bind decodeInstruction=some (.base op))
    (ok : ordinaryStep s (.base op)=some (execInstrBr s op)) (cost : instructionCycles (.base op)=1)
    (effect : execInstrBr s op=(s.setReg .x6 v).setPC (s.pc+4)) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=pc (w+1) ∧ Moved s t ∧ t.getReg .x6=v ∧ t.getReg .x16=s.getReg .x16 := by
  let t:=execInstrBr s op
  have run:=one lim here code ok
  rw [cost] at run
  refine ⟨t,run,?_,?_,?_,?_⟩ <;> dsimp only [t] <;> rw [effect]
  · change s.pc+4=_;rw [here,pc_add]
  · refine ⟨rfl,?_⟩;intro r h;have neq : Reg.x6≠r := by intro eq;subst r;exact (by decide : Reg.x6∉savedRegs) h
    simp [MachineState.getReg_setReg_ne _ _ _ _ neq]
  · simp [MachineState.getReg_setReg_eq (by decide : Reg.x6≠.x0)]
  · simp [MachineState.getReg_setReg_ne s .x6 .x16 v (by decide)]

theorem exit_jump_code : ∀ i : Fin 4096, pc (8224+i.val)+signExtend21 (jalOffset (8224+i.val) 703)=pc 703 := by decide +kernel

theorem entries {gs} (api : API gs) (node : Nat) (hn : node<64) (rs : List Nat) (w : Nat) (xs : List Nat)
    (s : MachineState) (atBlock : BlockAt rs w) (low : 8224≤w) (high : w+(blockCode rs w).length≤12320)
    (range : ∀ r∈rs,2≤r ∧ r<16) (size : xs.length+rs.length≤256)
    (here : s.pc=pc w) (level : s.getReg .x16=addr (8*node)) (inv : api.inv xs s) :
    ∃ t, let cost:=entriesPrice rs+2+(handlers (xs.length+rs.length)-handlers xs.length)
         Run openingImage s t cost cost ∧ t.pc=pc 703 ∧ api.inv (xs++rs.map (chunkNode node)) t ∧ t.getReg .x6=addr node := by
  induction rs generalizing w xs s with
  | nil =>
    have code0:=atBlock 0 (by simp [blockCode])
    have cd0:=widen (op:=.SRLI .x6 .x16 3) (by simpa [blockCode] using code0)
    obtain ⟨u,ru,pu,move,reg,_⟩:=set6 (by have:=block_code_two [] w;omega) here cd0 rfl rfl rfl
    have nodeR : u.getReg .x6=addr node := by
      rw [reg,level];apply BitVec.eq_of_toNat_eq
      simp [addr,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt (show 8*node<2^64 by omega),Nat.mod_eq_of_lt (show node<2^64 by omega)] <;> omega
    have code1:=atBlock 1 (by simp [blockCode])
    have cd1:=widen (op:=.JAL .x0 (jalOffset (w+1) 703)) (by simpa [blockCode] using code1)
    let t:=execInstrBr u (.JAL .x0 (jalOffset (w+1) 703))
    have ret : Run openingImage u t 1 1 := one (by have:=block_code_two [] w;omega) pu cd1 rfl
    have delta:=exit_jump_code ⟨w+1-8224,by have:=block_code_two [] w;omega⟩
    simp only [show 8224+(w+1-8224)=w+1 by omega] at delta
    have pcT : t.pc=pc 703 := (congrArg (fun v : Word=>v+signExtend21 (jalOffset (w+1) 703)) pu).trans delta
    exact ⟨t,by simpa [entriesPrice] using ru.thenDo ret,pcT,by simpa using (api.move (t:=t) (api.move inv move) ⟨rfl,fun _ _=>rfl⟩),nodeR⟩
  | cons r rest ih =>
    have rrange:=range r (by simp)
    obtain ⟨index,off⟩:=entry_node node r rrange.1 rrange.2
    have sn:=chunk_node_lt node r hn rrange.1 rrange.2
    have length : (blockCode (r::rest) w).length=entryLen r+(blockCode rest (w+entryLen r)).length := by simp [blockCode,entry_code_length]
    have inside:=block_code_two rest (w+entryLen r)
    have inst:=block_at_head r rest w atBlock
    have cd0 : (openingImage.code[w]?).bind decodeInstruction=some (.base (.ADDI .x6 .x16 (BitVec.ofNat 12 (entryOffset r)))) := by
      apply widen;have h:=inst 0 (by unfold entryLen;split <;> decide);unfold entryCode at h;split at h <;> simpa using h
    obtain ⟨a,ra,pa,ma,regA,levA⟩:=set6 (by omega) here cd0 rfl rfl rfl
    rw [level,small_imm _ off,←BitVec.ofNat_add] at regA
    have sh : entryShift r<4 := by unfold entryShift;omega
    have after : ∃ b, Run openingImage s b (entryLen r-1) (entryLen r-1) ∧ b.pc=pc (w+entryLen r-1) ∧
        api.inv xs b ∧ b.getReg .x6=addr (chunkNode node r) ∧ b.getReg .x16=addr (8*node) ∧
        (openingImage.code[w+entryLen r-1]?).bind decodeInstruction=some (.base (.JALR .x18 .x19 0)) := by
      by_cases leaf : depthOf r=3
      · have len : entryLen r=2 := by simp [entryLen,leaf]
        have e : entryShift r=0 := by simp [entryShift,leaf]
        simp [e] at index
        have h:=inst 1 (by omega)
        rw [len,show w+2-1=w+1 by omega]
        exact ⟨a,ra,pa,api.move inv ma,by simpa [index] using regA,levA.trans level,widen (by simpa [entryCode,leaf] using h)⟩
      · have len : entryLen r=3 := by simp [entryLen,leaf]
        have cd:=inst 1 (by omega)
        have ci:=widen (op:=.SRLI .x6 .x6 (BitVec.ofNat 6 (entryShift r))) (by simpa [entryCode,leaf] using cd)
        obtain ⟨b,rb,pb,mb,regB,levB⟩:=set6 (by omega) pa ci rfl rfl rfl
        have value : b.getReg .x6=addr (chunkNode node r) := by
          rw [regB,regA];apply BitVec.eq_of_toNat_eq
          simp only [addr,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show 8*node+entryOffset r<2^64 by omega),Nat.mod_eq_of_lt (show entryShift r<64 by omega),
            Nat.mod_eq_of_lt (show chunkNode node r<2^64 by omega)]
          exact index
        have h:=inst 2 (by omega)
        rw [len,show w+3-1=w+2 by omega]
        exact ⟨b,ra.thenDo rb,pb,api.move (api.move inv ma) mb,value,levB.trans (levA.trans level),widen (by simpa [entryCode,leaf] using h)⟩
    obtain ⟨b,rb,pb,ib,xb,lb,cb⟩:=after
    obtain ⟨c,rc,pcC,ic,_,lc⟩:=api.call ib (by simp only [List.length_cons] at size;omega) (by omega) sn xb pb cb
    have en : 0<entryLen r := by unfold entryLen;split <;> decide
    have pcC' : c.pc=pc (w+entryLen r) := by convert pcC using 2 <;> omega
    have len' : (xs++[chunkNode node r]).length=xs.length+1 := by simp
    obtain ⟨d,rd,pd,id,xd⟩:=ih (w+entryLen r) (xs++[chunkNode node r]) c (block_at_tail r rest w atBlock)
      (by omega) (by omega) (fun z hz=>range z (List.mem_cons_of_mem _ hz))
      (by rw [len'];simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using size) pcC' (lc.trans lb) ic
    have mono (a n : Nat) : handlers a≤handlers (a+n) := by
      induction n with | zero=>rfl | succ k ih=>rw [Nat.add_succ,handlers];omega
    have bound:=mono ((xs++[chunkNode node r]).length) rest.length
    rw [len',handlers] at bound
    dsimp only at rd ⊢
    have trace:=(rb.thenDo rc).thenDo rd
    refine ⟨d,?_,pd,by simpa [List.append_assoc] using id,xd⟩
    rw [len',handlers] at trace
    unfold entriesPrice at *;simp only [List.map_cons,List.sum_cons,List.length_cons] at *
    rw [show xs.length+(rest.length+1)=xs.length+1+rest.length by omega]
    have eq : entryLen r-1+(1+handlerLen xs.length)+
        (((rest.map entryLen).sum+2)+(handlers (xs.length+1+rest.length)-(handlers xs.length+handlerLen xs.length))) =
        (entryLen r+(rest.map entryLen).sum)+2+(handlers (xs.length+1+rest.length)-handlers xs.length) := by omega
    simpa only [eq] using trace
end CommitGolfCandidate.CapB
