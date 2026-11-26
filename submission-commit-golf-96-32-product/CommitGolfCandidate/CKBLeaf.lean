import CommitGolfCandidate.LateCheckLeafEnd
import CommitGolfCandidate.CKBHalf

/-! A96 batch leaf `bleaf` (check words 632..698). It is the shared leaf subroutine (words 384..432)
moved by 248 words, except that the 24-byte salt is read with twelve halfword copies (words 669..692,
the batch records are only 2-aligned); the final call, pointer advance and return sit 266 words
after their originals. The subroutine returns to word 218. -/
namespace CommitGolfCandidate.Late.Check.Micro.CKBLeaf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W AddrOK Calc Expr original evaluated price requirements live bump)
set_option maxRecDepth 8000

/-! ### Straight-line blocks at shifted words -/

def shift : Part → Nat | .advance => 266 | _ => 248

def leafParts : List Part := [.leafReady, .parity, .oddDest, .evenDest, .advance]

private def represents (n : Nat) (op : Instr) : Bool :=
  match decodeInstruction (checkWord n) with
  | some (.base actual) => decide (actual=op)
  | _ => false

private theorem represented {n : Nat} {op : Instr} (h : represents n op) :
    decodeInstruction (checkWord n) = some (.base op) := by
  unfold represents at h
  split at h
  · next actual eq => rw [eq,of_decide_eq_true h]
  · contradiction

private theorem checked (b : Part) (hb : b ∈ leafParts) :
    b.start+b.ops.length=b.stop ∧ b.start+shift b+b.ops.length≤814 ∧ b.ops.length=b.stop-b.start ∧
    price b.ops=b.cycles ∧ b.ops.all (fun c => c.dst != .x0) = true ∧
    requirements original b.ops=b.reads ∧ b.reads=[] ∧
    ∀ j : Fin b.ops.length, represents (b.start+shift b+j.val) b.ops[j.val].instr := by
  simp only [leafParts,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl <;> decide

set_option maxHeartbeats 4000000 in
private theorem outputs (b : Part) (hb : b ∈ leafParts) (r : Reg) :
    (b.ops.foldl bump original) r = b.equation r := by
  simp only [leafParts,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl <;> cases r <;> rfl

structure Shifted (b : Part) (s : MachineState) : Prop where
  runs : Runs s (b.after s) (b.stop-b.start) b.cycles
  regs : ∀ r, (b.after s).getReg r = (b.equation r).eval s
  mem : (b.after s).mem=s.mem
  pc : (b.after s).pc=pcAt (b.stop+shift b)

theorem shifted (b : Part) (hb : b ∈ leafParts) (s : MachineState) (pc : s.pc=pcAt (b.start+shift b)) :
    Shifted b s := by
  obtain ⟨edge,bound,size,cost,ok,reads,none,enc⟩ := checked b hb
  have regs : live s s original := by intro r;cases r <;> rfl
  have r := evaluate_block b.ops (b.start+shift b) s s original regs rfl pc (by omega)
    (fun c h => bne_iff_ne.mp (List.all_eq_true.mp ok c h)) (by rw [reads,none];simp)
    (fun j hj => represented (enc ⟨j,hj⟩))
  dsimp only at r
  refine ⟨?_,fun k => (r.2.1 k).trans (congrArg (Expr.eval s) (outputs b hb k)),r.2.2.1,?_⟩
  · rw [←size,←cost]; exact r.1
  · exact r.2.2.2.trans (congrArg pcAt (by omega))

theorem Shifted.keep {s : MachineState} {b : Part} (h : Shifted b s) (r : Reg)
    (eq : b.equation r=Open.original r) : (b.after s).getReg r=s.getReg r := by
  rw [h.regs,eq];cases r <;> rfl

private def canKeep (part : Part) := anchors.all fun r => decide (part.equation r=Open.original r)
theorem shiftedKeeps {s : MachineState} {p : Part} (x : Shifted p s) (ok : canKeep p) : Keeps s (p.after s) :=
  fun r hr=>x.keep r (of_decide_eq_true (List.all_eq_true.mp ok r hr))

/-! ### Branches at shifted words -/

def bafter (b : Test) (s : MachineState) :=
  s.setPC (pcAt (if b.taken s then b.target+248 else b.start+249))

theorem btest_run (b : Test) (hb : b = .parity ∨ b = .skipEven) (s : MachineState) (pc : s.pc=pcAt (b.start+248)) :
    Runs s (bafter b s) 1 1 := by
  have enc : decodeInstruction (checkWord (b.start+248))=some (.base b.instr) := by rcases hb with rfl|rfl <;> rfl
  have bound : b.start+248<814 := by rcases hb with rfl|rfl <;> decide
  have rs : Runs s (execInstrBr s b.instr) 1 1 := by
    have st : ordinaryStep s (.base b.instr)=some (execInstrBr s b.instr) := by rcases hb with rfl|rfl <;> rfl
    have cost : instructionCycles (.base b.instr)=1 := by rcases hb with rfl|rfl <;> rfl
    exact cost ▸ one _ bound _ enc s _ pc st
  have tgt : pcAt (b.start+248)+signExtend13 b.bits=pcAt (b.target+248) := by rcases hb with rfl|rfl <;> rfl
  have fall := pc_succ (b.start+248)
  have same : execInstrBr s b.instr = bafter b s := by
    have choose (c : Bool) :
        (if c then s.setPC (s.pc+signExtend13 b.bits) else s.setPC (s.pc+4)) =
          s.setPC (pcAt (if c then b.target+248 else b.start+249)) := by
      cases c <;> simp only [Bool.false_eq_true,if_false,if_true,pc,tgt,fall]
    by_cases eq : b.beq = true
    · simp only [Test.instr,bafter,Test.taken,if_pos eq]
      exact choose (s.getReg b.args.1 == s.getReg b.args.2)
    · simp only [Test.instr,bafter,Test.taken,if_neg eq]
      exact choose (s.getReg b.args.1 != s.getReg b.args.2)
  exact same ▸ rs

/-! ### Compression calls at shifted words -/

def bpc : Op → Nat | .first=>635 | .middle=>657 | .last=>660 | .final=>693

private theorem code (op : Op) :
    decodeInstruction (checkWord (bpc op))=some (.base (.ADDI .x10 op.src op.a)) ∧
    decodeInstruction (checkWord (bpc op+1))=some (.base (.ADDI .x12 op.dst op.b)) ∧
    decodeInstruction (checkWord (bpc op+2))=some (.base .ECALL) := by
  cases op <;> exact ⟨rfl,rfl,rfl⟩

structure BCall (o : Oracle) (op : Op) (s t : MachineState) (src dst : Nat) : Prop where
  runs : Late.Check.Normal.Runs o s t 3 1
  pc : t.pc=pcAt (bpc op+3)
  mem : t.mem=(store s dst (o.compression (readBuffer s src 96))).mem
  keep : ∀ r, .x10≠r → .x12≠r → t.getReg r=s.getReg r
  dest : t.getReg .x12=W dst

theorem doCall (o : Oracle) (op : Op) (s : MachineState) (src dst : Nat) (pc : s.pc=pcAt (bpc op))
    (mode : Mode s) (sp : s.getReg op.src+signExtend12 op.a=W src) (dp : s.getReg op.dst+signExtend12 op.b=W dst)
    (sa : AddrOK src 96) (da : AddrOK dst 32) :
    BCall o op s (result op s (o.compression (readBuffer s src 96))) src dst := by
  let u:=execInstrBr s (.ADDI .x10 op.src op.a)
  let r:=prepareCall s op.src op.dst op.a op.b
  let ans:=o.compression (readBuffer s src 96)
  have bound : bpc op+2<814 := by cases op <;> decide
  obtain ⟨a,b,c⟩:=code op
  have pc1 : u.pc=pcAt (bpc op+1) := by change s.pc+4=_;rw [pc,pc_succ]
  have pc2 : r.pc=pcAt (bpc op+2) := by change u.pc+4=_;rw [pc1,pc_succ (bpc op+1)]
  have first : Runs s u 1 1 := one _ (by omega) _ a _ _ pc rfl
  have next : Runs u r 1 1 := one _ (by omega) _ b _ _ pc1 rfl
  have indep : Reg.x10≠op.dst := by cases op <;> decide
  obtain ⟨src',dst'⟩:=call_addresses s op.src op.dst op.a op.b indep
  have rs : r.getReg .x10=W src := src'.trans sp
  have rd : r.getReg .x12=W dst := dst'.trans dp
  have endRun:=Late.Check.Normal.syscall o r (bpc op+2) src dst bound pc2 c mode.select mode.kind mode.width rs rd sa da
  have read : readBuffer r src 96=readBuffer s src 96 := read_congr_mem _ _ _ _ rfl
  have same : Late.Check.Normal.afterCall o r src dst=result op s ans := by
    change writeBits r (W dst) (o.compression (readBuffer r src 96))=writeBits r (r.getReg .x12) ans
    rw [rd,read]
  rw [same] at endRun
  constructor
  · exact (Late.Check.Normal.deterministic o (first.trans next)).trans endRun
  · have h:=call_pc s op.src op.dst op.a op.b ans
    exact h.trans (by rw [pc];cases op <;> rfl)
  · change (callState s _ _ _ _ _).mem=_
    exact (call_memory s op.src op.dst op.a op.b _ indep).trans (by rw [dp];rfl)
  · intro reg h k;exact call_register s op.src op.dst reg op.a op.b ans h k
  · change (writeBits r (r.getReg .x12) ans).getReg .x12=_
    rw [writeBits_register,rd]

theorem BCall.mode {o op s t src dst} (h : BCall o op s t src dst) (m : Mode s) : Mode t :=
  ⟨(h.keep _ (by decide) (by decide)).trans m.select,(h.keep _ (by decide) (by decide)).trans m.kind,
   (h.keep _ (by decide) (by decide)).trans m.width⟩

theorem BCall.written {o op s t src dst} (h : BCall o op s t src dst) :
    readBuffer t dst 32=o.compression (readBuffer s src 96) :=
  (read_congr_mem _ _ _ _ h.mem).trans (store_read ..)

theorem BCall.away {o op s t src dst} (h : BCall o op s t src dst) (a n : Nat)
    (db : dst+32≤2^64) (bound : a+n≤2^64) (sep : a+n≤dst ∨ dst+32≤a) : readBuffer t a n=readBuffer s a n :=
  (read_congr_mem _ _ _ _ h.mem).trans (store_away _ _ _ _ _ db bound sep)

theorem BCall.high {o op s t src dst} (h : BCall o op s t src dst) (lo : dst+32≤448) : High s t :=
  fun a n ha bound => h.away a n (by omega) (by unfold MEMORY_BYTES at bound;omega) (Or.inr (by omega))

theorem bcallKeeps {o op s t src dst} (x : BCall o op s t src dst) : Keeps s t := by
  intro r hr
  exact x.keep r (by intro e;subst r;exact (by decide : ¬Reg.x10∈anchors) hr)
    (by intro e;subst r;exact (by decide : ¬Reg.x12∈anchors) hr)

/-! ### The 64-byte middle copy at words 638..653 -/

private theorem encodingM (j : Fin 8) :
    decodeInstruction (checkWord (638+2*j.val))=some (.base (Site.middle.ld j.val)) ∧
    decodeInstruction (checkWord (638+2*j.val+1))=some (.base (Site.middle.sd j.val)) := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

private theorem offsetM (j : Fin 8) :
    signExtend12 (BitVec.ofNat 12 (Site.middle.sOff+8*j.val))=W Site.middle.sOff+W (8*j.val) ∧
    signExtend12 (BitVec.ofNat 12 (Site.middle.dOff+8*j.val))=W Site.middle.dOff+W (8*j.val) := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

private theorem bvaddrM (s : MachineState) (j : Fin 8) (src dst : Nat) (reg : Pointers .middle s src dst) :
    s.getReg Site.middle.source+signExtend12 (BitVec.ofNat 12 (Site.middle.sOff+8*j.val))=W (src+8*j.val) ∧
    s.getReg .x12+signExtend12 (BitVec.ofNat 12 (Site.middle.dOff+8*j.val))=W (dst+8*j.val) := by
  obtain ⟨a,b⟩:=offsetM j
  rw [a,b,←BitVec.add_assoc,←BitVec.add_assoc,reg.src,reg.dst]
  exact ⟨(BitVec.ofNat_add _ _).symm,(BitVec.ofNat_add _ _).symm⟩

private theorem move_runM (s : MachineState) (j : Fin 8)
    (pc : s.pc=pcAt (638+2*j.val)) (src dst : Nat) (ptr : Pointers .middle s src dst)
    (sa : AddrOK src (8*(j.val+1))) (da : AddrOK dst (8*(j.val+1))) :
    Runs s (move .middle s j) 2 2 := by
  obtain ⟨x,y⟩:=encodingM j
  obtain ⟨sp,dp⟩:=bvaddrM s j src dst ptr
  have j8:=j.isLt
  have range : 638+2*j.val+1<814 := by omega
  let t:=execInstrBr s (Site.middle.ld j)
  have pc' : t.pc=pcAt (638+2*j.val+1) := by change s.pc+4=_;rw [pc,pc_succ]
  have ok : memoryArgumentsValid s (Site.middle.ld j)=true := by
    change accessValid (_+_) 8=true;rw [sp];exact Open.access_at _ (by have :=sa.2;omega) (by have :=sa.1;omega)
  have ok' : memoryArgumentsValid t (Site.middle.sd j)=true := by
    change accessValid (s.getReg .x12+_) 8=true;rw [dp];exact Open.access_at _ (by have :=da.2;omega) (by have :=da.1;omega)
  have a : Runs s t 1 1 := one _ (by omega) _ x _ _ pc (by change (if memoryArgumentsValid s (Site.middle.ld j) then some (execInstrBr s (Site.middle.ld j)) else none)=_;rw [if_pos ok])
  have b : Runs t (move .middle s j) 1 1 := one _ range _ y _ _ pc' (by change (if memoryArgumentsValid t (Site.middle.sd j) then some (execInstrBr t (Site.middle.sd j)) else none)=_;rw [if_pos ok'] <;> rfl)
  exact a.trans b

theorem copies_runM (s : MachineState) (n src dst : Nat) (pc : s.pc=pcAt 638)
    (len : n≤8) (ptr : Pointers .middle s src dst) (sa : AddrOK src (8*n)) (da : AddrOK dst (8*n)) :
    Runs s (copies .middle s n) (2*n) (2*n) ∧ (copies .middle s n).pc=pcAt (638+2*n) := by
  induction n with
  | zero=> exact ⟨Runs.refl s,pc⟩
  | succ n ih=>
    have bound : n<8 := by omega
    obtain ⟨prev,pos⟩:=ih (by omega) ⟨sa.1,by have :=sa.2;omega⟩ ⟨da.1,by have :=da.2;omega⟩
    have next:=move_runM _ ⟨n,bound⟩ pos src dst (copies_ptr .middle s src dst n ptr) sa da
    constructor
    · rw [copies,Nat.mul_succ];exact prev.trans next
    · rw [copies,move_pc,pos,show 638+2*(n+1)=(638+2*n+1)+1 by omega,pc_succ,pc_succ];rw [BitVec.add_assoc];rfl

/-! ### The halfword salt copy at words 669..692 -/

private theorem saltWords (j : Nat) (hj : j<12) :
    decodeInstruction (checkWord (669+2*j))=some (.base (.LHU .x6 .x25 (BitVec.ofNat 12 (0+2*j)))) ∧
    decodeInstruction (checkWord (669+2*j+1))=some (.base (.SH .x12 .x6 (BitVec.ofNat 12 (0+2*j)))) := by
  interval_cases j <;> exact ⟨rfl,rfl⟩

private theorem pc_add (n k : Nat) : pcAt n+BitVec.ofNat 64 (4*k)=pcAt (n+k) := by
  unfold pcAt;rw [←BitVec.ofNat_add];congr 1;omega

theorem saltRun (s : MachineState) (pc : s.pc=pcAt 669) (S D : Nat)
    (source : s.getReg .x25=W S) (target : s.getReg .x12=W D)
    (se : S%2=0) (de : D%2=0) (sb : S+24≤MEMORY_BYTES) (db : D+24≤MEMORY_BYTES) :
    Runs s (CKBHalf.halfRun .x25 .x12 s 0 0 12) 24 24 := by
  intro fuel
  have run := CKBHalf.half_run_execute image .x25 .x12 s 0 0 S D 12 (by decide) (by decide) source target
    (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
    (fun j hj t tp => by
      apply fetched (669+2*j) (by omega) _ (saltWords j hj).1 t
      rw [tp,pc,show 8*j=4*(2*j) by omega,pc_add])
    (fun j hj t tp => by
      apply fetched (669+2*j+1) (by omega) _ (saltWords j hj).2 t
      rw [tp,pc,show 8*j+4=4*(2*j+1) by omega,pc_add,Nat.add_assoc])
    fuel false
  rw [show fuel+24=2*12+fuel by omega,run]

/-! ### The gap word: words 663..668 (the shared code's 415..420 moved by 248) -/

structure BGap (s t : MachineState) (odd : Bool) : Prop where
  pc : t.pc=pcAt 669
  dest : t.getReg .x12=W (sa odd)
  keep : ∀ r, r≠.x12 → t.getReg r=s.getReg r
  outside : Open.Outside s t (ga odd) 8
  zero : readBuffer t (ga odd) 8=0

private theorem word_read (s : MachineState) (a : Nat) (al : a%8=0) :
    Open.wordAt s a=readBuffer s a 8 :=
  (read_digest_word s a 0 al (by decide)).symm.trans (read_buffer_slice s a 32 0 8 (by decide))

private theorem written (s : MachineState) (a : Nat) (v : Word) (t : MachineState)
    (mem : t.mem=(s.setMem (W a) v).mem) (al : a%8=0) (small : a<2^64) :
    Open.Outside s t a 8 ∧ readBuffer t a 8=v := by
  have word (q : Nat) (hq : q<2^64) :
      Open.wordAt t q=if q=a then v else Open.wordAt s q := by
    change t.mem (W q)=_;rw [mem];change (if W q == W a then v else s.mem (W q))=_
    by_cases same : q=a
    · subst q;simp [Open.wordAt,W]
    · have ne : W q≠W a := by intro e;have :=congrArg BitVec.toNat e;simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hq,Nat.mod_eq_of_lt small] at this;contradiction
      rw [if_neg (fun h=>ne (beq_iff_eq.mp h)),if_neg same];rfl
  constructor
  · intro q hq _ out;rw [word _ (by unfold MEMORY_BYTES at hq;omega),if_neg (by omega)]
  · rw [←word_read _ _ al,word _ small,if_pos rfl]

private theorem clearAt (odd : Bool) (s : MachineState) (pc : s.pc=pcAt (if odd then 665 else 668))
    (dest : s.getReg .x12=W (sa odd)) :
    let t:= (s.setMem (W (ga odd)) 0).setPC (s.pc+4)
    Runs s t 1 1 ∧ t.pc=pcAt (if odd then 666 else 669) := by
  cases odd
  · constructor
    · apply one 668 (by decide) (.SD .x12 .x0 4088) (by rfl) _ _ pc
      have addr : s.getReg .x12+signExtend12 4088=W 224 := by rw [dest];rfl
      have ok : memoryArgumentsValid s (.SD .x12 .x0 4088)=true := by change accessValid (_+_) 8=true;rw [addr];decide
      simp only [ordinaryStep,ok,↓reduceIte,execInstrBr,addr];rfl
    · change s.pc+4=_;rw [pc];rfl
  · constructor
    · apply one 665 (by decide) (.SD .x12 .x0 24) (by rfl) _ _ pc
      have addr : s.getReg .x12+signExtend12 24=W 184 := by rw [dest];rfl
      have ok : memoryArgumentsValid s (.SD .x12 .x0 24)=true := by change accessValid (_+_) 8=true;rw [addr];decide
      simp only [ordinaryStep,ok,↓reduceIte,execInstrBr,addr];rfl
    · change s.pc+4=_;rw [pc];rfl

attribute [local irreducible] Runs Late.Check.Normal.Runs

theorem clearGap (o : Oracle) (s : MachineState) (odd : Bool) (pc : s.pc=pcAt 663) (bit : s.getReg .x28=regBit odd) :
    ∃ t n, n≤4 ∧ Late.Check.Normal.Runs o s t n 0 ∧ BGap s t odd := by
  let a:=bafter .parity s
  have jump:=btest_run .parity (Or.inl rfl) s pc
  have beginPC : a.pc=pcAt (if odd then 664 else 667) := by
    change pcAt (if s.getReg .x28 == (0 : Word) then 419+248 else 415+249)=_
    rw [bit];cases odd <;> rfl
  let b : Part := if odd then .oddDest else .evenDest
  have hb : b ∈ leafParts := by cases odd <;> decide
  have setup := shifted b hb a (by cases odd <;> exact beginPC)
  let r:=b.after a
  have rp : r.pc=pcAt (if odd then 665 else 668) := by cases odd <;> exact setup.pc
  have rd : r.getReg .x12=W (sa odd) := by rw [setup.regs];cases odd <;> rfl
  let t:=(r.setMem (W (ga odd)) 0).setPC (r.pc+4)
  obtain ⟨storeRun,tp⟩:=clearAt odd r rp rd
  have steps : Runs s t 3 3 := by
    have widths : b.stop-b.start=1 ∧ b.cycles=1 := by dsimp only [b]; split <;> exact ⟨rfl,rfl⟩
    have setupRun := setup.runs
    rw [widths.1,widths.2] at setupRun
    exact jump.trans (setupRun.trans storeRun)
  have rkeep (k : Reg) (ne : k≠.x12) : t.getReg k=s.getReg k := by
    have z (x : MachineState) (a v : Word) : (x.setMem a v).getReg k=x.getReg k := by cases k <;> rfl
    change ((r.setMem _ _).setPC _).getReg k=_
    have e := setup.keep k (by cases odd <;> cases k <;> first | rfl | contradiction)
    rw [MachineState.getReg_setPC,z]
    exact e.trans MachineState.getReg_setPC
  have dest : t.getReg .x12=W (sa odd) := rd
  have mem : r.mem=s.mem := setup.mem
  have altered : t.mem=(s.setMem (W (ga odd)) 0).mem := by
    change (r.setMem _ _).mem=_;simp only [MachineState.setMem,mem]
  obtain ⟨out,zero⟩:=written s (ga odd) 0 t altered (by cases odd <;> decide) (by cases odd <;> decide)
  cases odd with
  | false=> exact ⟨t,3,by decide,Late.Check.Normal.deterministic o steps,⟨tp,dest,rkeep,out,zero⟩⟩
  | true=>
    let u:=bafter .skipEven t
    have lastRun:=btest_run .skipEven (Or.inr rfl) t tp
    have endPC : u.pc=pcAt 669 := by change pcAt (if t.getReg .x0 == t.getReg .x0 then 421+248 else 418+249)=_;simp
    exact ⟨u,4,by decide,Late.Check.Normal.deterministic o (steps.trans lastRun),⟨endPC,dest,
      fun k ne=>rkeep k ne,out,zero⟩⟩

/-! ### First and middle part (words 632..662) -/

theorem copyKeepsM (s : MachineState) (n : Nat) : Keeps s (copies .middle s n) :=
  fun r hr => copies_keep .middle s n r (by intro e;subst r;exact (by decide : ¬Reg.x6∈anchors) hr)

structure First (o : Oracle) (s t : MachineState) (v : CommitGolf.Entry) : Prop where
  pc : t.pc=pcAt 654
  keep : Keeps s t
  mode : Mode t
  high : High s t
  middle : readBuffer t 352 96=middleBlock v (o.compression (firstBlock v))
  runs : Late.Check.Normal.Runs o s t 22 1

theorem first (o : Oracle) (s : MachineState) (v : CommitGolf.Entry) (a : Nat)
    (pc : s.pc=pcAt 632) (value : s.getReg .x8=W a) (range : AddrOK a 256) (highA : 448≤a)
    (vread : readBuffer s a 256=v) : ∃ t, First o s t v := by
  let r:=Part.leafReady.after s
  have prefixRun:=shifted .leafReady (by decide) s pc
  have keep:=shiftedKeeps prefixRun (by decide)
  have mode : Mode r:=⟨prefixRun.regs .x5,prefixRun.regs .x13,prefixRun.regs .x11⟩
  have r8 : r.getReg .x8=W a := (keep .x8 (by decide)).trans value
  have firstRead : readBuffer r a 96=firstBlock v := by
    exact (read_congr_mem r s a 96 prefixRun.mem).trans ((read_buffer_slice s a 256 0 96 (by decide)).symm.trans (congrArg firstBlock vread))
  let u:=result .first r (o.compression (readBuffer r a 96))
  have call:=doCall o .first r a 352 prefixRun.pc mode
    (by change r.getReg .x8+0=W a;rw [r8];exact BitVec.add_zero _) (by rfl)
    ⟨range.1,by have :=range.2;omega⟩ (by decide)
  change BCall o .first r u a 352 at call
  have ptr : Pointers .middle u (a+96) 384 := by
    constructor
    · change u.getReg .x8+W 96=_;rw [call.keep _ (by decide) (by decide),r8];exact (BitVec.ofNat_add _ _).symm
    · change u.getReg .x12+W 32=_;rw [call.dest];rfl
  have srcok : AddrOK (a+96) 64 := ⟨by have :=range.1;omega,by have :=range.2;omega⟩
  have cp:=copies_runM u 8 (a+96) 384 call.pc (by decide) ptr srcok (by decide)
  have copied:=copies_effect .middle u (a+96) 384 8 (by decide) ptr srcok (by decide) (by omega)
  let t:=copies .middle u 8
  have high1 : High s u := (High.memory prefixRun.mem).trans (call.high (by decide))
  have original : readBuffer u (a+96) 64=v.extractLsb' 768 512 := by
    rw [high1 _ _ (by omega) (by have :=range.2;omega),←read_buffer_slice s a 256 96 64 (by decide),vread] <;> rfl
  have tail : readBuffer t 384 64=v.extractLsb' 768 512 := (copied_read copied srcok.1 (by decide)).trans original
  have head : readBuffer t 352 32=o.compression (firstBlock v) := by
    rw [Open.outside_read copied.outside (by decide) (by decide) 352 32 (by decide) (Or.inl (by decide)),call.written,firstRead]
  have joined : readBuffer t 384 64 ++ readBuffer t 352 32=readBuffer t 352 96 :=
    (read_join t 352 32 64).trans BitVec.extractLsb'_eq_self
  refine ⟨t,cp.2,(keep.then (bcallKeeps call)).then (copyKeepsM u 8),copiesMode _ _ _ (call.mode mode),
    high1.trans (high_write copied.outside (by decide) (by decide) (by decide)),?_,?_⟩
  · rw [←joined,tail,head];rfl
  · exact ((Late.Check.Normal.deterministic o prefixRun.runs).trans call.runs).trans (Late.Check.Normal.deterministic o cp.1)

structure Middle (o : Oracle) (s t : MachineState) (v : CommitGolf.Entry) (odd : Bool) : Prop where
  pc : t.pc=pcAt 663
  keep : Keeps s t
  mode : Mode t
  bit : t.getReg .x28=regBit odd
  high : High s t
  a : readBuffer t (da odd) 32=o.compression (middleBlock v (o.compression (firstBlock v)))
  b : readBuffer t (da odd+32) 32=o.compression (lastBlock v)
  runs : Late.Check.Normal.Runs o s t 31 3

private theorem parity (i : Index) : (W i.val &&& 1)=regBit (i.val.testBit 0) := by
  change (BitVec.ofNat 64 i.val &&& BitVec.ofNat 64 (2^1-1)) = _
  rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod,Nat.testBit_eq_decide_div_mod_eq]
  simp only [Nat.pow_zero,Nat.div_one]
  have split : i.val%2=0 ∨ i.val%2=1 := by omega
  rcases split with e|e <;> rw [e] <;> rfl

theorem middle (o : Oracle) (s : MachineState) (v : CommitGolf.Entry) (a : Nat) (i : Index)
    (pc : s.pc=pcAt 632) (value : s.getReg .x8=W a) (index : s.getReg .x20=W i.val)
    (range : AddrOK a 256) (highA : 448≤a) (vread : readBuffer s a 256=v) :
    ∃ t, Middle o s t v (i.val.testBit 0) := by
  let odd:=i.val.testBit 0
  obtain ⟨t,f⟩:=first o s v a pc value range highA vread
  let r:=Part.parity.after t
  have setup:=shifted .parity (by decide) t f.pc
  have keep:=shiftedKeeps setup (by decide)
  have ix : t.getReg .x20=W i.val := (f.keep _ (by decide)).trans index
  have flag : r.getReg .x28=regBit odd := by rw [setup.regs];change (t.getReg .x20 &&& 1)=_;rw [ix,parity]
  have off : r.getReg .x7=W (da odd) := by
    rw [setup.regs];change ((t.getReg .x20 &&& 1) <<< 5)+160=_
    rw [ix,parity];change (regBit odd <<< 5)+160=_;cases odd <;> rfl
  have mode : Mode r := ⟨(setup.keep _ rfl).trans f.mode.select,(setup.keep _ rfl).trans f.mode.kind,
    (setup.keep _ rfl).trans f.mode.width⟩
  have mid : readBuffer r 352 96=middleBlock v (o.compression (firstBlock v)) :=
    (read_congr_mem _ _ _ _ setup.mem).trans f.middle
  let u:=result .middle r (o.compression (readBuffer r 352 96))
  have left:=doCall o .middle r 352 (da odd) setup.pc mode (by rfl)
    (by change r.getReg .x7+0=_;simpa using off) (by decide) (by cases odd <;> decide)
  change BCall o .middle r u 352 (da odd) at left
  have a8 : u.getReg .x8=W a := (left.keep _ (by decide) (by decide)).trans ((keep _ (by decide)).trans ((f.keep _ (by decide)).trans value))
  have high1:=f.high.trans ((High.memory setup.mem).trans (left.high (by cases odd <;> decide)))
  have last : readBuffer u (a+160) 96=lastBlock v := by
    rw [high1 _ _ (by omega) (by have :=range.2;omega),←read_buffer_slice s a 256 160 96 (by decide),vread];rfl
  let z:=result .last u (o.compression (readBuffer u (a+160) 96))
  have right:=doCall o .last u (a+160) (da odd+32) left.pc (left.mode mode)
    (by change u.getReg .x8+W 160=_;rw [a8];exact (BitVec.ofNat_add _ _).symm)
    (by change u.getReg .x7+W 32=_;rw [left.keep _ (by decide) (by decide),off];exact (BitVec.ofNat_add _ _).symm)
    ⟨by have :=range.1;omega,by have :=range.2;omega⟩ (by cases odd <;> decide)
  change BCall o .last u z (a+160) (da odd+32) at right
  refine ⟨z,right.pc,((f.keep.then keep).then (bcallKeeps left)).then (bcallKeeps right),right.mode (left.mode mode),
    (right.keep _ (by decide) (by decide)).trans ((left.keep _ (by decide) (by decide)).trans flag),
    high1.trans (right.high (by cases odd <;> decide)),?_,?_,?_⟩
  · rw [right.away _ _ (by cases odd <;> decide) (by cases odd <;> decide) (Or.inl le_rfl),left.written,mid]
  · rw [right.written,last]
  · exact ((f.runs.trans (Late.Check.Normal.deterministic o setup.runs)).trans left.runs).trans right.runs

/-! ### The whole batch leaf -/

structure LeafEnd (o : Oracle) (s t : MachineState) (i : Index) (salt : Salt) (v : CommitGolf.Entry) (a p n : Nat) : Prop where
  budget : n≤70
  runs : Late.Check.Normal.Runs o s t n 4
  pc : t.pc=pcAt 218
  valPtr : t.getReg .x8=W (a+256)
  proofPtr : t.getReg .x25=W (p+24)
  keep : ∀ reg∈stable, t.getReg reg=s.getReg reg
  high : High s t
  digest : readBuffer t 256 32=leaf o.compression (i.val.testBit 0) salt v

private theorem returnRun (s : MachineState) (pc : s.pc=pcAt 698) (reg : s.getReg .x1=pcAt 218) :
    Runs s (s.setPC (pcAt 218)) 1 1 := by
  apply one 698 (by decide) (.JALR .x0 .x1 0) (by rfl) _ _ pc
  change some (s.setPC ((s.getReg .x1+signExtend12 0) &&& ~~~1))=_
  rw [reg];rfl

private theorem gapKeep {s t odd} (g : BGap s t odd) : Keeps s t :=
  fun r hr=>g.keep r (by intro e;subst r;exact (by decide : ¬Reg.x12∈anchors) hr)

private theorem rowFields (t : MachineState) (odd : Bool) (salt : Salt) (a b : Digest)
    (left : readBuffer t (da odd) 32=a) (right : readBuffer t (da odd+32) 32=b)
    (gap : readBuffer t (ga odd) 8=0) (salts : readBuffer t (sa odd) 24=salt) :
    readBuffer t 160 96=finalBlock odd salt a b := by
  cases odd with
  | false=>exact even_row t 160 a b salt left right gap salts
  | true=>exact odd_row t 160 a b salt salts gap left right

private theorem advancePtrs (z : MachineState) (h : Shifted .advance z) (a p : Nat)
    (va : z.getReg .x8=W a) (sp : z.getReg .x25=W p) :
    (Part.advance.after z).getReg .x8=W (a+256) ∧ (Part.advance.after z).getReg .x25=W (p+24) := by
  constructor
  · rw [h.regs];change z.getReg .x8+W 256=_;rw [va];exact (BitVec.ofNat_add _ _).symm
  · rw [h.regs];change z.getReg .x25+W 24=_;rw [sp];exact (BitVec.ofNat_add _ _).symm

private theorem halfKeeps (s : MachineState) : Keeps s (CKBHalf.halfRun .x25 .x12 s 0 0 12) :=
  fun r hr => CKBHalf.half_run_register _ _ _ _ _ _ r (by intro e;subst r;exact (by decide : ¬Reg.x6∈anchors) hr)

set_option maxHeartbeats 900000
attribute [local irreducible] result copies Part.after readBuffer
theorem leafRun (o : Oracle) (s : MachineState) (i : Index) (salt : Salt) (v : CommitGolf.Entry) (a p : Nat)
    (pc : s.pc=pcAt 632) (value : s.getReg .x8=W a) (index : s.getReg .x20=W i.val)
    (sp : s.getReg .x25=W p) (scratch : s.getReg .x21=256) (reg : s.getReg .x1=pcAt 218)
    (ar : AddrOK a 256) (pe : p%2=0) (pb : p+24≤MEMORY_BYTES) (ah : 448≤a) (ph : 448≤p)
    (vread : readBuffer s a 256=v) (sread : readBuffer s p 24=salt) :
    ∃ t n, LeafEnd o s t i salt v a p n := by
  let odd:=i.val.testBit 0
  obtain ⟨r,mid⟩:=middle o s v a i pc value index ar ah vread
  obtain ⟨u,n,nb,gRun,g⟩:=clearGap o r odd mid.pc mid.bit
  have k:=mid.keep.then (gapKeep g)
  have u25 : u.getReg .x25=W p := (k _ (by decide : Reg.x25∈anchors)).trans sp
  have dr : AddrOK (sa odd) 24 := by cases odd <;> decide
  have cp:=saltRun u g.pc p (sa odd) u25 g.dest pe (by cases odd <;> decide) pb (by cases odd <;> decide)
  let t:=CKBHalf.halfRun .x25 .x12 u 0 0 12
  have tpc : t.pc=pcAt 693 := by
    rw [CKBHalf.half_run_pc,g.pc];rfl
  have saEnd : sa odd+24≤448 := by cases odd <;> decide
  have sepSalt : p+0+2*12≤sa odd+0 ∨ sa odd+0+2*12≤p+0 := by right;omega
  have saltCopy : readBuffer t (sa odd) 24=readBuffer u p 24 := by
    have h:=CKBHalf.half_run_copy .x25 .x12 u 0 0 p (sa odd) 12 (by decide) (by decide) u25 g.dest
      (by decide) (by decide) (by omega) (by cases odd <;> decide) (by unfold MEMORY_BYTES at pb;omega)
      (by cases odd <;> decide) sepSalt
    simpa using h
  have keepT (x m : Nat) (fit : x+m≤MEMORY_BYTES) (sep : x+m≤sa odd ∨ sa odd+24≤x) :
      readBuffer t x m=readBuffer u x m := by
    have h:=CKBHalf.half_run_preserves .x25 .x12 u 0 0 p (sa odd) 12 x m (by decide) (by decide) u25 g.dest
      (by decide) (by decide) (by omega) (by cases odd <;> decide) (by unfold MEMORY_BYTES at pb;omega)
      (by cases odd <;> decide) sepSalt (by unfold MEMORY_BYTES at fit;omega) (by simpa using sep)
    exact h
  have gh : High r u:=high_write g.outside (by cases odd <;> decide) (by decide) (by cases odd <;> decide)
  have ch : High u t:=fun x m lo hi => keepT x m hi (Or.inr (by omega))
  have high:=mid.high.trans (gh.trans ch)
  have anchor:=k.then (halfKeeps u)
  have saltRead : readBuffer t (sa odd) 24=salt :=
    saltCopy.trans (((mid.high.trans gh) _ _ ph pb).trans sread)
  have gapRead : readBuffer t (ga odd) 8=0 :=
    (keepT _ _ (by cases odd <;> decide) (by cases odd <;> decide)).trans g.zero
  have keepRead (x : Nat) (fit : x+32≤MEMORY_BYTES)
      (sep1 : x+32≤ga odd ∨ ga odd+8≤x) (sep2 : x+32≤sa odd ∨ sa odd+24≤x) :
      readBuffer t x 32=readBuffer r x 32 :=
    (keepT x 32 fit sep2).trans
      (Open.outside_read g.outside (by cases odd <;> decide) (by decide) _ _ fit sep1)
  let A:=o.compression (middleBlock v (o.compression (firstBlock v)))
  let B:=o.compression (lastBlock v)
  have left : readBuffer t (da odd) 32=A :=
    (keepRead _ (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide)).trans mid.a
  have right : readBuffer t (da odd+32) 32=B :=
    (keepRead _ (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide)).trans mid.b
  have row := rowFields t odd salt A B left right gapRead saltRead
  have modeU : Mode u:=⟨(g.keep _ (by decide)).trans mid.mode.select,(g.keep _ (by decide)).trans mid.mode.kind,
    (g.keep _ (by decide)).trans mid.mode.width⟩
  have modeT : Mode t:=⟨(CKBHalf.half_run_register _ _ _ _ _ _ _ (by decide)).trans modeU.select,
    (CKBHalf.half_run_register _ _ _ _ _ _ _ (by decide)).trans modeU.kind,
    (CKBHalf.half_run_register _ _ _ _ _ _ _ (by decide)).trans modeU.width⟩
  have sc : t.getReg .x21=256 := (anchor _ (by decide)).trans scratch
  have last:=doCall o .final t 160 256 tpc modeT (by rfl)
    (by change t.getReg .x21+0=256;exact (BitVec.add_zero _).trans sc) (by decide) (by decide)
  let z:=result .final t (o.compression (readBuffer t 160 96))
  change BCall o .final t z 160 256 at last
  have next:=shifted .advance (by decide) z last.pc
  let q:=Part.advance.after z
  have preserve := anchor.then (bcallKeeps last)
  have linkQ : q.getReg .x1=pcAt 218 := (next.keep _ rfl).trans ((preserve _ (by decide)).trans reg)
  let out:=q.setPC (pcAt 218)
  have rt:=returnRun q next.pc linkQ
  have moved:=advancePtrs z next a p ((preserve _ (by decide)).trans value) ((preserve _ (by decide)).trans sp)
  have outReg (reg : Reg) : out.getReg reg=q.getReg reg := MachineState.getReg_setPC
  refine ⟨out,31+n+24+3+2+1,⟨by omega,?_,rfl,?_,?_,?_,?_,?_⟩⟩
  · have before := ((mid.runs.trans gRun).trans (Late.Check.Normal.deterministic o cp)).trans last.runs
    exact (before.trans (Late.Check.Normal.deterministic o next.runs)).trans (Late.Check.Normal.deterministic o rt)
  · exact (outReg .x8).trans moved.1
  · exact (outReg .x25).trans moved.2
  · intro j hj;apply (outReg j).trans
    have mem : j∈anchors := (by intro r;cases r <;> decide : ∀ j : Reg, j∈stable → j∈anchors) j hj
    exact (next.keep j ((by intro r;cases r <;> decide : ∀ r : Reg,r∈stable → Part.advance.equation r=Open.original r) j hj)).trans (preserve j mem)
  · exact high.trans ((last.high (by decide)).trans (High.memory (show out.mem=z.mem from next.mem)))
  · have digest := (read_congr_mem out z 256 32 (show out.mem=z.mem from next.mem)).trans last.written
    rw [row] at digest;exact digest

end CommitGolfCandidate.Late.Check.Micro.CKBLeaf
