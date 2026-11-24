import CommitGolfCandidate.Layout2Writer3Phase0
import CommitGolfCandidate.Layout2Writer3Phase1
import CommitGolfCandidate.Layout2Writer3Phase2
import CommitGolfCandidate.Layout2Writer3Phase3
import CommitGolfCandidate.Layout2WriterTrack
import CommitGolfCandidate.GroupOpenWalk

/-! Fused opener: execution of the phase-`p` record writer at any word `w` as a row walk (`walkRows`), from the
writer's entry (`Entry3`: position in `t1`, block start in `s5`, saved L22 node address in `s2`, carry in `tp`).
Adapted from Astra's V2a writer proof (`Layout2Writer2Context/Head/Step/Run`) to the fused registers (`reg3`, `op3`)
and to row walks. The result (`writer3_run`) is V2a's `PhaseFacts` with the carry in `x4`. -/
namespace CommitGolfCandidate.Layout2Writer3
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase Layout2Writer Layout2Writer2
open TwoPermutationPrototype.GroupedOpening (walkRows legal address legal_append walk_join address_succ)
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

/-- Rows `(w, op₀), (w+1, op₁), …`. -/
def rowsFrom : Nat → List Instr → List (Nat × Instr)
  | _, [] => []
  | w, op::ops => (w,op) :: rowsFrom (w+1) ops

theorem rowsFrom_append (w : Nat) (xs ys : List Instr) :
    rowsFrom w (xs++ys)=rowsFrom w xs ++ rowsFrom (w+xs.length) ys := by
  induction xs generalizing w with
  | nil => simp [rowsFrom]
  | cons x xs ih =>
    show (w,x) :: rowsFrom (w+1) (xs++ys)=(w,x) :: (rowsFrom (w+1) xs ++ rowsFrom (w+(xs.length+1)) ys)
    rw [ih, show w+1+xs.length=w+(xs.length+1) by omega]

theorem rowsFrom_length (w : Nat) (xs : List Instr) : (rowsFrom w xs).length=xs.length := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp [rowsFrom, ih]

def Free3 (r : Reg) := r≠.x6 ∧ r≠.x7 ∧ r≠.x10 ∧ r≠.x4 ∧ r≠.x28 ∧ r≠.x31
instance (r : Reg) : Decidable (Free3 r) := by unfold Free3;infer_instance

theorem reg3_free (t : T) (r : Reg) (h : Free3 r) : reg3 t≠r := by
  rcases h with ⟨a,b,c,d,e,f⟩
  cases t <;> first | exact a.symm | exact b.symm | exact c.symm | exact d.symm | exact e.symm | exact f.symm
theorem reg3_inj (t u : T) (h : t≠u) : reg3 t≠reg3 u := by cases t <;> cases u <;> simp_all [reg3]
theorem reg3_nz (t : T) : reg3 t≠.x0 := by cases t <;> decide

/-- The model rows' entry, after the three head instructions (`a0 = 32 q`, `t3 = B + 32 q`). -/
structure Core3 (a : MachineState) (p pos B l22 : Nat) (c : Word) : Prop where
  index : pos<16777216
  aligned : B%8=0
  room : recordBase0 ≤ B ∧ B+stride p≤MEMORY_BYTES
  quad : l22%8=0 ∧ heapBase≤l22 ∧ l22+32≤saltBase
  posReg : a.getReg .x6=addr pos
  ptr : a.getReg .x18=addr l22
  slot : a.getReg .x28=addr (B+32*(pos%4))
  dest : a.getReg .x21=addr B
  carry : a.getReg .x4=c
  heap : a.getReg .x9=addr heapBase
  leaves : a.getReg .x19=addr 4194304

/-- The symbolic registers (through `reg3`) and sparse output describe the state after a prefix of the rows. -/
structure Track3 (s m : MachineState) (p pos B l22 : Nat) (c : Word) (v : Model) : Prop where
  reg : ∀ t : T, m.getReg (reg3 t)=denote s pos l22 c (v.reg t)
  fixed : ∀ r, Free3 r → m.getReg r=s.getReg r
  block : ∀ j, 8*j+8≤stride p → m.getMem (addr (B+8*j))=wordAt s pos B l22 c j (v.out j)
  frame : ∀ q : Word, q.toNat<B ∨ B+stride p≤q.toNat → m.getMem q=s.getMem q

theorem begin_track3 {a p pos B l22 c} (e : Core3 a p pos B l22 c) : Track3 a a p pos B l22 c start3 := by
  refine ⟨?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
  intro t
  cases t with
  | n => exact e.posReg
  | c => exact e.carry
  | _ => rfl

theorem Track3.readAs {s m p pos B l22 c v} (h : Track3 s m p pos B l22 c v) (t : T) {x : V}
    (eq : v.reg t=x) : m.getReg (reg3 t)=denote s pos l22 c x := eq ▸ h.reg t

theorem Track3.assign {s m p pos B l22 c v} (h : Track3 s m p pos B l22 c v) (t : T) (x : V) (physical newPC : Word)
    (same : physical=denote s pos l22 c x) :
    Track3 s ((m.setReg (reg3 t) physical).setPC newPC) p pos B l22 c (changeReg v t x) := by
  have mem : ((m.setReg (reg3 t) physical).setPC newPC).mem=m.mem := by cases t <;> rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro u
    by_cases e : u=t
    · subst u;simpa [changeReg,MachineState.getReg_setReg_eq (reg3_nz t)] using same
    · simp [changeReg,e,MachineState.getReg_setReg_ne m _ _ physical (reg3_inj t u (Ne.symm e)),h.reg]
  · intro r free;simp [MachineState.getReg_setReg_ne m _ _ physical (reg3_free t r free),h.fixed r free]
  · intro j bound;simpa only [MachineState.getMem,mem,changeReg] using h.block j bound
  · intro q bound;simpa only [MachineState.getMem,mem] using h.frame q bound

theorem geometry3 {s p pos B l22 c} (e : Core3 s p pos B l22 c) (f : Nat) (large : 4≤f) :
    fieldBase l22 pos f%8=0 ∧ fieldBase l22 pos f+width f≤B := by
  have index:=e.index;have lo:=e.room.1;unfold recordBase0 at lo
  by_cases quad : f=4
  · have a:=e.quad;unfold saltBase at a
    simp only [fieldBase,width,if_neg (by omega : f≠0),if_neg (by omega : ¬f<4),if_pos quad];omega
  · have h : node pos (f-4)<2^23 := by
      unfold node;rw [Nat.shiftRight_eq_div_pow];apply lt_of_le_of_lt (Nat.div_le_self _ _);omega
    have x:=Nat.xor_lt_two_pow h (by decide : 1<2^23)
    simp only [fieldBase,width,if_neg (by omega : f≠0),if_neg (by omega : ¬f<4),if_neg quad,heapBase];omega

private theorem concatenate (x : Word) :
    extractByte x 7 ++ extractByte x 6 ++ extractByte x 5 ++ extractByte x 4 ++
    extractByte x 3 ++ extractByte x 2 ++ extractByte x 1 ++ extractByte x 0=x := by
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  simp only [BitVec.getLsbD_append,extractByte,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight]
  interval_cases b <;> simp

private theorem input_dword3 {s p pos B l22 c} (e : Core3 s p pos B l22 c) (f j : Nat)
    (large : 4≤f) (inside : 8*j+8≤width f) :
    dwordOf (recordSource s l22 pos) (start f+8*j)=s.getMem (addr (fieldBase l22 pos f+8*j)) := by
  have facts:=geometry3 e f large
  have byte (b : Nat) (hb : b<8) : recordSource s l22 pos (start f+8*j+b)=
      extractByte (s.getMem (addr (fieldBase l22 pos f+8*j))) b := by
    unfold recordSource
    rw [Nat.add_assoc,source_offset l22 pos f (8*j+b) (by omega),←Nat.add_assoc]
    exact aligned_byte' _ _ _ (by omega) hb
  have b0 : recordSource s l22 pos (start f+8*j) = extractByte (s.getMem (addr (fieldBase l22 pos f+8*j))) 0 := by simpa only [Nat.add_zero] using byte 0 (by decide)
  simp only [dwordOf,byte _ (by decide : 7<8),byte _ (by decide : 6<8),byte _ (by decide : 5<8),
    byte _ (by decide : 4<8),byte _ (by decide : 3<8),byte _ (by decide : 2<8),byte _ (by decide : 1<8),b0,concatenate]

theorem store_dword3 {s m p pos B l22 c v} (e : Core3 s p pos B l22 c) (h : Track3 s m p pos B l22 c v)
    (j : Nat) (x : V) (physical newPC : Word) (same : physical=denote s pos l22 c x) (inside : 8*j+8≤stride p) :
    Track3 s ((m.setMem (addr (B+8*j)) physical).setPC newPC) p pos B l22 c (changeMem v j x) := by
  have room:=e.room.2;have ram : MEMORY_BYTES<2^64 := by decide
  have fit : B+8*j<2^64 := by omega
  refine ⟨h.reg,h.fixed,?_,?_⟩
  · intro i ib
    change (m.setMem _ physical).getMem (addr (B+8*i))=wordAt _ _ _ _ _ i (if i=j then some x else v.out i)
    by_cases eq : i=j
    · subst i;simpa only [MachineState.getMem_setMem_eq,if_pos rfl,ite_true,wordAt] using same
    · have neq : addr (B+8*i)≠addr (B+8*j) := by
        intro g
        have r:=congrArg BitVec.toNat g
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,Nat.mod_eq_of_lt (show B+8*i<2^64 by omega)] at r
        omega
      rw [MachineState.getMem_setMem_ne neq,if_neg eq];exact h.block i ib
  · intro q away
    change (m.setMem _ physical).getMem q=_
    rw [MachineState.getMem_setMem_ne]
    · exact h.frame q away
    · intro eq;rw [eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at away;omega

theorem read_dword3 {s m p pos B l22 c v} (e : Core3 s p pos B l22 c) (h : Track3 s m p pos B l22 c v)
    (f j : Nat) (large : 4≤f) (inside : 8*j+8≤width f) :
    m.getMem (addr (fieldBase l22 pos f+8*j))=denote s pos l22 c (.data (start f+8*j)) := by
  have room:=e.room.2;have geo:=geometry3 e f large;have ram : MEMORY_BYTES<2^64:=by decide
  exact (h.frame _ (Or.inl (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show fieldBase l22 pos f+8*j<2^64 by omega)];omega))).trans
    (input_dword3 e f j large inside).symm

/-! ### One row -/

private theorem shr_num (a k : Nat) (fit : a<2^64) : addr a >>> k=addr (a >>> k) := by
  have bound : a >>> k<2^64 := by rw [Nat.shiftRight_eq_div_pow];exact (Nat.div_le_self _ _).trans_lt fit
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,Nat.mod_eq_of_lt bound]

private theorem scale5 (a : Nat) : addr a <<< (5:Nat)=addr (32*a) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow];change addr a * addr 32=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm]
private theorem add_addr (a b : Nat) : addr a+addr b=addr (a+b) := (BitVec.ofNat_add ..).symm
private theorem imm8 (i : Nat) (small : i<68) : signExtend12 (BitVec.ofNat 12 (8*i))=addr (8*i) := by
  interval_cases i <;> rfl
private theorem node_bound {pos : Nat} (small : pos<16777216) (l : Nat) : node pos l<2^64 := by
  unfold node;rw [Nat.shiftRight_eq_div_pow];exact (Nat.div_le_self _ _).trans_lt (by omega)

theorem progress3 {s m p pos B l22 c v} (e : Core3 s p pos B l22 c) (h : Track3 s m p pos B l22 c v)
    (r : Row) (ok : need3 (pos%4) p v r) :
    memoryArgumentsValid m (op3 r)=true ∧ Track3 s (execInstrBr m (op3 r)) p pos B l22 c (advance v r) := by
  have heap : m.getReg .x9=addr heapBase := (h.fixed _ (by decide)).trans e.heap
  have leaves : m.getReg .x19=addr 4194304 := (h.fixed _ (by decide)).trans e.leaves
  have dest : m.getReg .x21=addr B := (h.fixed _ (by decide)).trans e.dest
  have ptr : m.getReg .x18=addr l22 := (h.fixed _ (by decide)).trans e.ptr
  have posSmall:=e.index
  have room:=e.room.2
  have limit : MEMORY_BYTES<2^64 := by decide
  cases r with
  | residue | selector | groupDelta | groupBase | mateOffset _ | mateBase _ | pointer => exact False.elim ok
  | quartet =>
    have src : m.getReg .x6=addr pos := h.readAs .n ok
    refine ⟨rfl,h.assign .n .quartet _ _ ?_⟩
    change m.getReg .x6 >>> (2:Nat)=addr (pos/4)
    rw [src,shr_num _ _ (by omega),Nat.shiftRight_eq_div_pow]
  | root =>
    have n : m.getReg .x6=addr (pos/4) := h.readAs .n ok
    refine ⟨rfl,h.assign .n (.node 0) _ _ ?_⟩
    change m.getReg .x6+m.getReg .x19=addr (node pos 0)
    rw [n,leaves,add_addr];simp [node,Nat.add_comm]
  | ascend l =>
    have n : m.getReg .x6=addr (node pos l) := h.readAs .n ok
    refine ⟨rfl,h.assign .n (.node (l+1)) _ _ ?_⟩
    change m.getReg .x6 >>> (1:Nat)=addr (node pos (l+1))
    rw [n,shr_num _ _ (node_bound posSmall l)]
    exact congrArg addr (Nat.shiftRight_add _ _ _).symm
  | flip l =>
    have n : m.getReg .x6=addr (node pos l) := h.readAs .n ok
    refine ⟨rfl,h.assign .ptr (.flipped l) _ _ ?_⟩
    change m.getReg .x6 ^^^ signExtend12 1=_
    rw [n,show signExtend12 1=addr 1 from rfl,←BitVec.ofNat_xor];rfl
  | scale l =>
    have n : m.getReg .x7=addr (node pos l ^^^ 1) := h.readAs .ptr ok
    refine ⟨rfl,h.assign .ptr (.scaled l) _ _ ?_⟩
    change m.getReg .x7 <<< (5:Nat)=_;rw [n];exact scale5 _
  | sibling l =>
    have n : m.getReg .x7=addr (32*(node pos l ^^^ 1)) := h.readAs .ptr ok.1
    refine ⟨rfl,h.assign .ptr (.base (4+l)) _ _ ?_⟩
    change m.getReg .x9+m.getReg .x7=addr (fieldBase l22 pos (4+l))
    rw [heap,n,add_addr];simp [fieldBase,show ¬4+l<4 by omega, show 4+l≠4 by have:=ok.2;omega,Nat.ne_of_gt ok.2]
  | load d b f j =>
    obtain ⟨large,ok⟩:=ok
    have wid : width f≤32 := by unfold width;split <;> decide
    have bounds:=geometry3 e f large
    by_cases f4 : f=4
    · subst f4
      have inside : 8*j+8≤width 4 := by simpa using ok
      have src : m.getReg .x18=addr (fieldBase l22 pos 4) := by rw [ptr]; simp [fieldBase]
      have a : m.getReg .x18+signExtend12 (BitVec.ofNat 12 (8*j))=addr (fieldBase l22 pos 4+8*j) := by
        rw [src,imm8 _ (by omega),add_addr]
      have opEq : op3 (.load d b 4 j)=.LD (reg3 d) .x18 (BitVec.ofNat 12 (8*j)) := by simp [op3]
      rw [opEq]
      refine ⟨?_,h.assign d (.data (start 4+8*j)) _ _ ?_⟩
      · change accessValid _ 8=true
        rw [a];apply access8 <;> omega
      · change m.getMem (m.getReg .x18+signExtend12 (BitVec.ofNat 12 (8*j)))=_
        rw [a];exact read_dword3 e h _ _ (by omega) inside
    · have pre' : v.reg b=.base f ∧ 8*j+8≤width f := by
        have ok' : pre p v (.load d b f j) := by simpa [f4] using ok
        exact ok'
      have src : m.getReg (reg3 b)=addr (fieldBase l22 pos f) := h.readAs b pre'.1
      have inside:=pre'.2
      have a : m.getReg (reg3 b)+signExtend12 (BitVec.ofNat 12 (8*j))=addr (fieldBase l22 pos f+8*j) := by
        rw [src,imm8 _ (by omega),add_addr]
      have opEq : op3 (.load d b f j)=.LD (reg3 d) (reg3 b) (BitVec.ofNat 12 (8*j)) := by simp [op3,f4]
      rw [opEq]
      refine ⟨?_,h.assign d (.data (start f+8*j)) _ _ ?_⟩
      · change accessValid _ 8=true
        rw [a];apply access8 <;> omega
      · change m.getMem (m.getReg (reg3 b)+signExtend12 (BitVec.ofNat 12 (8*j)))=_
        rw [a];exact read_dword3 e h _ _ large inside
  | store t j =>
    have width : stride p≤536 := by unfold stride;split <;> decide
    obtain ⟨inside,special⟩:=ok
    by_cases routedHere : routed j=true
    · obtain ⟨aux,lo,hi⟩:=special routedHere
      have slot : m.getReg .x28=addr (B+32*(pos%4)) := (h.readAs .aux aux).trans e.slot
      have a : m.getReg .x28+signExtend12 (BitVec.ofNat 12 (8*(9+(j-9)%4)))=addr (B+8*j) := by
        rw [slot,imm8 _ (by omega),add_addr];congr 1;omega
      simp only [op3,routedHere,ite_true,execInstrBr,a]
      refine ⟨?_,store_dword3 e h j (v.reg t) _ _ (h.reg t) inside⟩
      change accessValid _ 8=true;rw [a];apply access8 <;> have:=e.aligned <;> omega
    · have a : m.getReg .x21+signExtend12 (BitVec.ofNat 12 (8*j))=addr (B+8*j) := by
        rw [dest,imm8 _ (by omega),add_addr]
      simp only [op3,if_neg routedHere,execInstrBr,a]
      refine ⟨?_,store_dword3 e h j (v.reg t) _ _ (h.reg t) inside⟩
      change accessValid _ 8=true;rw [a];apply access8 <;> have:=e.aligned <;> omega
  | shl d t n =>
    refine ⟨rfl,h.assign d (.shl (v.reg t) n) _ _ ?_⟩
    change m.getReg (reg3 t) <<< (BitVec.ofNat 6 n).toNat=_
    rw [h.reg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<64 from ok)];rfl
  | shr d t n =>
    refine ⟨rfl,h.assign d (.shr (v.reg t) n) _ _ ?_⟩
    change m.getReg (reg3 t) >>> (BitVec.ofNat 6 n).toNat=_
    rw [h.reg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<64 from ok)];rfl
  | bor d x y =>
    refine ⟨rfl,h.assign d (.bor (v.reg x) (v.reg y)) _ _ ?_⟩
    change m.getReg (reg3 x) ||| m.getReg (reg3 y)=_;rw [h.reg,h.reg];rfl

/-- A row's instruction is an ordinary step that moves the PC by one word. -/
theorem op3_step (r : Row) (m : MachineState) (ok : memoryArgumentsValid m (op3 r)=true) :
    ordinaryStep m (.base (op3 r))=some (execInstrBr m (op3 r)) ∧ (execInstrBr m (op3 r)).pc=m.pc+4 := by
  cases r with
  | store t j =>
    by_cases hit : routed j=true <;> simp only [op3,hit,Bool.false_eq_true,ite_true,ite_false] at ok ⊢ <;>
      exact ⟨by simp only [ordinaryStep,ok,ite_true],rfl⟩
  | load d b f j =>
    by_cases f4 : f=4 <;> simp only [op3,f4,ite_true,ite_false] at ok ⊢ <;>
      exact ⟨by simp only [ordinaryStep,ok,ite_true],rfl⟩
  | shl d t n =>
    change memoryArgumentsValid m (.SLLI (reg3 d) (reg3 t) (BitVec.ofNat 6 n))=true at ok
    change ordinaryStep m (.base (.SLLI (reg3 d) (reg3 t) (BitVec.ofNat 6 n)))=_ ∧ _
    exact ⟨by simp only [ordinaryStep,ok,ite_true] <;> rfl,rfl⟩
  | shr d t n =>
    change memoryArgumentsValid m (.SRLI (reg3 d) (reg3 t) (BitVec.ofNat 6 n))=true at ok
    change ordinaryStep m (.base (.SRLI (reg3 d) (reg3 t) (BitVec.ofNat 6 n)))=_ ∧ _
    exact ⟨by simp only [ordinaryStep,ok,ite_true] <;> rfl,rfl⟩
  | bor d x y =>
    change memoryArgumentsValid m (.OR (reg3 d) (reg3 x) (reg3 y))=true at ok
    change ordinaryStep m (.base (.OR (reg3 d) (reg3 x) (reg3 y)))=_ ∧ _
    exact ⟨by simp only [ordinaryStep,ok,ite_true] <;> rfl,rfl⟩
  | _ => all_goals exact ⟨by simp only [op3,instruction] at ok ⊢;simp only [ordinaryStep,ok,ite_true],rfl⟩

/-- The model rows as a row walk from word `w`. -/
theorem execute_rows3 {a p pos B l22 c} (e : Core3 a p pos B l22 c) (xs : List Row) :
    ∀ (w : Nat) (m : MachineState) (v : Model), Track3 a m p pos B l22 c v → m.pc=address w →
      valid3 (pos%4) p v xs=true →
      legal (rowsFrom w (xs.map op3)) m ∧ (walkRows m (rowsFrom w (xs.map op3))).pc=address (w+xs.length) ∧
        Track3 a (walkRows m (rowsFrom w (xs.map op3))) p pos B l22 c (xs.foldl advance v) := by
  induction xs with
  | nil => intro w m v tr pc _; exact ⟨trivial,by simpa [rowsFrom,walkRows] using pc,tr⟩
  | cons r rs ih =>
    intro w m v tr pc checked
    simp only [valid3,Bool.and_eq_true,decide_eq_true_eq] at checked
    obtain ⟨ready,next⟩:=progress3 e tr r checked.1
    obtain ⟨ord,pc1⟩:=op3_step r m ready
    have pcN : (execInstrBr m (op3 r)).pc=address (w+1) := by rw [pc1,pc,address_succ]
    obtain ⟨l,p2,t2⟩:=ih (w+1) _ _ next pcN checked.2
    have step : walkRows m (rowsFrom w ((r::rs).map op3))=walkRows (execInstrBr m (op3 r)) (rowsFrom (w+1) (rs.map op3)) :=
      rfl
    refine ⟨⟨pc,ord,l⟩,?_,?_⟩
    · rw [step,p2,List.length_cons]; congr 1; omega
    · rw [step]; exact t2

/-! ### The whole writer -/

/-- Entry of the fused writer of phase `p` (at any word): position in `t1`, block start in `s5`, the saved L22 node
address in `s2`, the carry in `tp`. -/
structure Entry3 (s : MachineState) (p pos B l22 : Nat) (c : Word) : Prop where
  phase : p<4
  index : pos<16777216
  posReg : s.getReg .x6=addr pos
  dest : s.getReg .x21=addr B
  aligned : B%8=0
  room : recordBase0 ≤ B ∧ B+stride p ≤ MEMORY_BYTES
  carry : s.getReg .x4=c
  heap : s.getReg .x9=addr heapBase
  leaves : s.getReg .x19=addr 4194304
  ptr : s.getReg .x18=addr l22
  quad : l22%8=0 ∧ heapBase ≤ l22 ∧ l22+32 ≤ saltBase

/-- The writer's rows at word `w`. -/
def writerRows (w p : Nat) : List (Nat × Instr) := rowsFrom w (listing3 p 0)

private theorem mask (n : Nat) (small : n<2^64) : addr n &&& 3#64=addr (n%4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,show (3#64).toNat=2^2-1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n%4<2^64 by omega)]

private theorem rd (m : MachineState) (t r : Reg) (x : Word) (nz : t≠.x0) :
    (m.setReg t x).getReg r=if t=r then x else m.getReg r := by
  by_cases eq : t=r
  · subst r;simp [MachineState.getReg_setReg_eq nz]
  · simp [eq,MachineState.getReg_setReg_ne _ _ _ _ eq]

theorem head3 {s p pos B l22 c} (w : Nat) (e : Entry3 s p pos B l22 c) (pc : s.pc=address w) :
    let a:=walkRows s (rowsFrom w headOps3)
    legal (rowsFrom w headOps3) s ∧ a.pc=address (w+3) ∧ a.mem=s.mem ∧
      (∀ r, r≠.x10 → r≠.x28 → a.getReg r=s.getReg r) ∧ Core3 a p pos B l22 c := by
  intro a
  have sel := mask pos (by have:=e.index;omega)
  have scale : addr (pos%4) <<< (5:Nat)=addr (32*(pos%4)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow];change addr (pos%4)*addr 32=_
    rw [←BitVec.ofNat_mul,Nat.mul_comm]
  have loc : addr B+addr (32*(pos%4))=addr (B+32*(pos%4)) := (BitVec.ofNat_add ..).symm
  let a1:=execInstrBr s (.ANDI .x10 .x6 3)
  have mem1 : a1.mem=s.mem := rfl
  have reg1 (r : Reg) : a1.getReg r=if .x10=r then addr (pos%4) else s.getReg r := by
    cases r <;> simp [a1,execInstrBr,rd,signExtend12,e.posReg,sel] <;> rfl
  have pc1 : a1.pc=address (w+1) := by change s.pc+4=_; rw [pc,address_succ]
  let a2:=execInstrBr a1 (.SLLI .x10 .x10 5)
  have mem2 : a2.mem=s.mem := rfl
  have reg2 (r : Reg) : a2.getReg r=if .x10=r then addr (32*(pos%4)) else s.getReg r := by
    cases r <;> simp [a2,execInstrBr,rd,reg1,scale] <;> rfl
  have pc2 : a2.pc=address (w+2) := by change a1.pc+4=_; rw [pc1,address_succ]
  let a3:=execInstrBr a2 (.ADD .x28 .x21 .x10)
  have mem3 : a3.mem=s.mem := rfl
  have reg3' (r : Reg) : a3.getReg r=if .x28=r then addr (B+32*(pos%4)) else if .x10=r then addr (32*(pos%4))
      else s.getReg r := by
    cases r <;> simp [a3,execInstrBr,rd,reg2,e.dest,loc] <;> rfl
  have pc3 : a3.pc=address (w+3) := by change a2.pc+4=_; rw [pc2,address_succ]
  have aEq : a=a3 := rfl
  have keep : ∀ r, r≠.x10 → r≠.x28 → a.getReg r=s.getReg r := by
    intro r h10 h28; rw [aEq, reg3', if_neg (Ne.symm h28), if_neg (Ne.symm h10)]
  refine ⟨?_,by rw [aEq]; exact pc3,by rw [aEq]; exact mem3,keep,⟨e.index,e.aligned,e.room,e.quad,
    (keep _ (by decide) (by decide)).trans e.posReg,(keep _ (by decide) (by decide)).trans e.ptr,
    by rw [aEq, reg3']; simp,(keep _ (by decide) (by decide)).trans e.dest,
    (keep _ (by decide) (by decide)).trans e.carry,(keep _ (by decide) (by decide)).trans e.heap,
    (keep _ (by decide) (by decide)).trans e.leaves⟩⟩
  exact ⟨pc,rfl,pc1,rfl,pc2,rfl,trivial⟩

private theorem byte_frame {s t : MachineState} (p B a : Nat) (alg : B%8=0) (fit : a<2^64)
    (outside : a<B ∨ B+stride p≤a)
    (frame : ∀ q : Word, q.toNat<B ∨ B+stride p≤q.toNat → t.getMem q=s.getMem q) :
    t.getByte (addr a)=s.getByte (addr a) := by
  have width : stride p%8=0 := by unfold stride;split <;> decide
  let base:=8*(a/8)
  have e : base+a%8=a := by dsimp [base];omega
  have n : (addr base).toNat=base := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [base];omega)]
  have outside' : base<B ∨ B+stride p≤base := by dsimp [base];omega
  have same:=frame (addr base) (by rw [n];exact outside')
  have atByte (m : MachineState) := aligned_byte' m base (a%8) (by dsimp [base];omega) (by omega)
  have lhs:=atByte t;have rhs:=atByte s
  rw [e] at lhs rhs
  exact lhs.trans ((congrArg (fun x=>extractByte x (a%8)) same).trans rhs.symm)

attribute [local irreducible] rows expected symStream streamRun writerDwords writerCarry

private theorem carry_value (s : MachineState) (pos l22 : Nat) (c : Word) (p : Nat) :
    denote s pos l22 c (symStream p).1=writerCarry p (recordSource s l22 pos) c := by
  have h:=congrArg (fun q : Word × Nat × List Word=>q.1) (eval_stream s pos l22 c p)
  dsimp only [mapStream] at h
  unfold writerCarry
  exact h

theorem program3_facts (p q : Nat) (hp : p<4) (hq : q<4) : correct3 p q := by
  interval_cases p
  · exact correct3_phase_0 ⟨q,hq⟩
  · exact correct3_phase_1 ⟨q,hq⟩
  · exact correct3_phase_2 ⟨q,hq⟩
  · exact correct3_phase_3 ⟨q,hq⟩

/-- The fused writer of phase `p` at word `w`: `writerLen p` unit-cost rows to `w + writerLen p`; the written dwords
hold V1's writer dwords as in V2a, the carry is in `tp`, `t1` holds the position's level-13 node; the other
registers but `t2, a0, t3, t6`, the retained block bytes, every byte outside the block and every raw word outside the
block are unchanged. -/
theorem writer3_run {s p pos B l22 c} (w : Nat) (e : Entry3 s p pos B l22 c) (pc : s.pc=address w) :
    let t:=walkRows s (writerRows w p)
    legal (writerRows w p) s ∧ t.pc=address (w+writerLen p) ∧
      (∀ j<stride p, Layout2Phase2.written (pos%4) (j/8) →
        t.getByte (addr (B+j))=Layout2Phase2.writtenByte p (recordSource s l22 pos) c j) ∧
      t.getReg .x4=writerCarry p (recordSource s l22 pos) c ∧
      t.getReg .x6=addr (512+pos/32768) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x4 → r ≠ .x28 → r ≠ .x31 → t.getReg r=s.getReg r) ∧
      (∀ a<2^64, ¬(B ≤ a ∧ a<B+stride p ∧ Layout2Phase2.written (pos%4) ((a-B)/8)) →
        t.getByte (addr a)=s.getByte (addr a)) ∧
      (∀ x : Word, x.toNat<B ∨ B+stride p ≤ x.toNat → t.getMem x=s.getMem x) := by
  intro t
  let q:=pos%4
  have qfit : q<4 := Nat.mod_lt _ (by decide)
  obtain ⟨good,len,carry,nodeR,stored⟩:=program3_facts p q e.phase qfit
  obtain ⟨hl,hpc,hmem,hkeep,ctx⟩:=head3 w e pc
  set a:=walkRows s (rowsFrom w headOps3) with ha
  obtain ⟨rl,rpc,h⟩:=execute_rows3 ctx (rows p q) (w+3) a start3 (begin_track3 ctx) hpc good
  change Track3 a _ p pos B l22 c (finalModel3 p q) at h
  have split : writerRows w p=rowsFrom w headOps3 ++ rowsFrom (w+3) ((rows p q).map op3) := by
    unfold writerRows
    rw [← same_listing3 ⟨p,e.phase⟩ ⟨q,qfit⟩]
    exact rowsFrom_append w headOps3 _
  have tEq : t=walkRows a (rowsFrom (w+3) ((rows p q).map op3)) := by
    show walkRows s (writerRows w p)=_; rw [split, walk_join]
  have agree : recordSource a l22 pos=recordSource s l22 pos := by
    funext k;simp only [recordSource,MachineState.getByte,MachineState.getMem,hmem]
  have aligned:=e.aligned
  have wid : stride p%8=0 := by unfold stride;split <;> decide
  have minimum : 528≤stride p := by unfold stride;split <;> decide
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [split];exact legal_append _ _ _ hl rl
  · rw [tEq,rpc];unfold writerLen;congr 1;omega
  · intro j inside hit
    rw [tEq]
    let i:=j/8
    have cell : 8*i+8≤stride p := by dsimp [i];omega
    have bytes:=aligned_byte' (walkRows a (rowsFrom (w+3) ((rows p q).map op3))) (B+8*i) (j%8) (by omega) (by omega)
    rw [show B+8*i+j%8=B+j by dsimp [i];omega] at bytes
    rw [bytes,h.block i cell,stored ⟨i,by omega⟩,if_pos hit]
    let d:=Layout2Phase2.v1Dword i
    change extractByte (denote a pos l22 c ((expected p).getD d (.data 0))) (j%8)=_
    rw [extract_eq,Layout2Phase2.writtenByte,←agree,←eval_expected a pos l22 c p]
    have length:=writer_dwords_length p (recordSource a l22 pos) c e.phase
    rw [←eval_expected a pos l22 c p,List.length_map] at length
    have isLt : d<(expected p).length := by dsimp [d,Layout2Phase2.v1Dword];split_ifs <;> omega
    change _=(((expected p).map (denote a pos l22 c)).getD d 0).extractLsb' _ _
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem isLt,Option.map_some,Option.getD_some]
  · rw [tEq]
    have v:=h.reg .c;rw [carry] at v
    exact v.trans ((carry_value a pos l22 c p).trans (congrArg (fun src=>writerCarry p src c) agree))
  · rw [tEq]
    have v:=h.reg .n;rw [nodeR] at v
    refine v.trans (congrArg addr ?_);unfold node;rw [Nat.shiftRight_eq_div_pow];omega
  · intro r b d f g i j
    rw [tEq]
    exact (h.fixed r ⟨b,d,f,g,i,j⟩).trans (hkeep r f i)
  · intro x fit away
    rw [tEq]
    by_cases inside : B≤x ∧ x<B+stride p
    · let j:=x-B
      let i:=j/8
      have hit : Layout2Phase2.written q i=false := by
        apply Bool.eq_false_iff.mpr;intro yes;exact away ⟨inside.1,inside.2,yes⟩
      have cell : 8*i+8≤stride p := by dsimp [i,j];omega
      have line:=h.block i cell
      rw [stored ⟨i,by omega⟩,if_neg (by simp [hit])] at line
      change (walkRows a (rowsFrom (w+3) ((rows p q).map op3))).getMem (addr (B+8*i))=a.getMem (addr (B+8*i)) at line
      have lane := fun (u : MachineState)=>aligned_byte' u (B+8*i) (j%8) (by omega) (by omega)
      have out:=lane (walkRows a (rowsFrom (w+3) ((rows p q).map op3)));have src:=lane a
      rw [show B+8*i+j%8=x by dsimp [i,j];omega] at out src
      exact out.trans ((congrArg (fun z=>extractByte z (j%8)) line).trans (src.symm.trans (by simp only [MachineState.getByte,MachineState.getMem,hmem])))
    · exact (byte_frame p B x aligned fit (by omega) h.frame).trans (by simp only [MachineState.getByte,MachineState.getMem,hmem])
  · intro x away;rw [tEq];exact (h.frame x away).trans (by simp only [MachineState.getMem,hmem])

end CommitGolfCandidate.Layout2Writer3
