import CommitGolfCandidate.TwoPermutationPackedOpeningImage
import CommitGolfCandidate.Execution
import CommitGolfCandidate.TwoPermutationOpeningCopy
import CommitGolfCandidate.GroupedPacket
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.CounterSaltWindows

/-! P4 opener, salt-materialising prefix loop (words 1463-1485). Ported from dadon's 2a19be00 `GroupOpen{Walk,Step,
Select,Latch}`: the same rows shifted by +726 words, resume at word 13 instead of 15, the tape at
5637148704 = nonceBase and the indices at 5905584160 = indicesBase of 04680e02's opening layout. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

abbrev openingImage : Image := PackedOpening.openingImage

theorem prefix_fetch_base (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 1486) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (openingImage.code[index]?).bind Opening.decodeBase = some instruction) :
    fetch openingImage state = some (.base instruction) := by
  have current : state.pc.toNat = 4096+4*index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, current, ite_eq_left (by omega), show (4096+4*index-4096)/4=index by omega]
  cases code : openingImage.code[index]? with
  | none => simp [code] at decoded
  | some word =>
    simp [code, Opening.decodeBase] at decoded
    cases dec : decodeInstruction word with
    | none => simp [dec] at decoded
    | some result =>
      cases result with
      | base inst =>
        simp [dec] at decoded
        simpa [decoded] using dec
      | word op rd rs₁ rs₂ => simp [dec] at decoded
      | sraiw rd rs sh => simp [dec] at decoded

def address (i : Nat) := BitVec.ofNat 64 (4096+4*i)
abbrev Row := Nat × Instr

def walkRows (s : MachineState) (rows : List Row) := rows.foldl (fun t p => execInstrBr t p.2) s
def price (rows : List Row) := (rows.map fun p => instructionCycles (.base p.2)).sum

def legal : List Row → MachineState → Prop
  | [],_ => True
  | (i,op)::tail,s =>
      s.pc=address i ∧ ordinaryStep s (.base op)=some (execInstrBr s op) ∧ legal tail (execInstrBr s op)

def presentRows (rows : List Row) :=
  ∀ p∈rows, ∀ st : MachineState, st.pc=address p.1 → fetch openingImage st=some (.base p.2)

theorem walk_rows_run (s : MachineState) (rows : List Row) (valid : legal rows s) (code : presentRows rows)
    (fuel : Nat) (coins : Bool) :
    execute openingImage (rows.length+fuel) s coins =
      (do let z ← execute openingImage fuel (walkRows s rows) coins;return z.charge (price rows) 0) := by
  induction rows generalizing s with
  | nil => simp [walkRows,price,Execution.charge]
  | cons p tail ih =>
    rcases p with ⟨i,op⟩
    obtain ⟨pc,ord,more⟩ := valid
    have fetch := code (i,op) (by simp) s pc
    rw [show ((i,op)::tail).length+fuel=(tail.length+fuel)+1 by simp;omega,
      execute_ordinary_step _ _ _ _ _ _ fetch ord,ih _ more (fun p hp => code p (List.mem_cons_of_mem _ hp))]
    simp [walkRows,price,Execution.charge,bind_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

def plain (op : Instr) := match op with
  | .ECALL | .EBREAK | .CSRS .. | .LI .. | .MV .. | .NOP => false
  | _ => true

theorem ord_iff (s : MachineState) (op : Instr) (yes : plain op=true) :
    ordinaryStep s (.base op)=some (execInstrBr s op) ↔ memoryArgumentsValid s op=true := by
  cases op <;> simp_all [plain,ordinaryStep] <;> split <;> simp_all

def preRows : List Row := [(1463,.LD .x6 .x14 0),(1464,.ANDI .x28 .x6 63),(1465,.REMU .x28 .x28 .x29),
  (1466,.SUB .x7 .x6 .x28),(1467,.SLLI .x7 .x7 8),(1468,.ADD .x7 .x7 .x26),(1469,.SD .x10 .x7 0)]

def postRows (direct last : Bool) : List Row :=
  [(1471,.ADDI .x7 .x28 (-1)),(1472,.SLLI .x7 .x7 4),(1473,.BNE .x28 .x0 8)] ++
  (if direct then [(1474,.ADDI .x7 .x0 184)] else []) ++
  [(1475,.ADD .x7 .x7 .x12),(1476,.SLLI .x30 .x6 4),(1477,.ADD .x30 .x30 .x22),
   (1478,.LD .x31 .x7 0),(1479,.SD .x30 .x31 0),(1480,.LD .x31 .x7 8),(1481,.SD .x30 .x31 8),
   (1482,.ADDI .x14 .x14 8),(1483,.ADDI .x17 .x17 (-1)),(1484,.BNE .x17 .x0 8108)] ++
  (if last then [(1485,.JAL .x0 2091264)] else [])

private theorem row_fetch (row : Row) (bounded : row.1<1486) (dec : (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2) :
    ∀ st : MachineState, st.pc=address row.1 → fetch openingImage st=some (.base row.2) :=
  fun st pc => prefix_fetch_base st _ _ bounded pc dec

theorem pre_row_fetch : presentRows preRows := by
  intro p hp
  apply row_fetch
  · simp only [preRows,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h|h|h|h|h|h|h <;> subst p <;> decide
  · simp only [preRows,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h|h|h|h|h|h|h <;> subst p <;> decide +kernel

theorem post_row_fetch (direct last : Bool) : presentRows (postRows direct last) := by
  have raw : ∀ d l : Bool, ∀ i : Fin (postRows d l).length, let row := (postRows d l)[i];
      row.1<1486 ∧ (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2 := by decide +kernel
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact row_fetch _ (raw direct last ⟨i,hi⟩).1 (raw direct last ⟨i,hi⟩).2

end TwoPermutationPrototype.GroupedOpening

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (rank msgWord)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000

def indexAt (j : Nat) := BitVec.ofNat 64 (5905584160+8*j)
def destAt (i : Index) := BitVec.ofNat 64 (5637148704+16*i.val)
def countWord (n : Nat) := BitVec.ofNat 64 n
def offAt (i : Index) := if rank i.val=0 then 184 else 16*(rank i.val-1)
def readAt (i : Index) := BitVec.ofNat 64 (1536+offAt i)
def ctrAt (i : Index) := wordAddress (msgWord (i.val-rank i.val))

structure Registers (s : MachineState) (ord left : Nat) : Prop where
  input : s.getReg .x10=1024
  output : s.getReg .x12=1536
  selector : s.getReg .x5=0
  width : s.getReg .x11=200
  primitive : s.getReg .x13=1
  index : s.getReg .x14=indexAt ord
  leftReg : s.getReg .x17=countWord left
  salt : s.getReg .x22=5637148704
  base : s.getReg .x26=4096
  divReg : s.getReg .x29=11

private theorem masked (i : Index) : (BitVec.ofNat 64 i.val &&& signExtend12 63)=BitVec.ofNat 64 (i.val%64) := by
  apply BitVec.eq_of_toNat_eq
  have h : i.val<16777216:=i.isLt
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  change i.val &&& (2^6-1)=(i.val%64)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (show i.val%64<2^64 by omega)]

theorem decoded_rank (i : Index) : rv64_remu (BitVec.ofNat 64 (i.val%64)) 11=BitVec.ofNat 64 (rank i.val) := by
  unfold rv64_remu rank
  change BitVec.ofNat 64 _ % 11#64=_
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show i.val%64<2^64 by omega),
    Nat.mod_eq_of_lt (show i.val%64%11<2^64 by omega)] <;> omega

theorem counter_address (i : Index) :
    ((BitVec.ofNat 64 i.val - BitVec.ofNat 64 (rank i.val)) <<< (8 : Nat))+4096 = ctrAt i := by
  have sub : rank i.val ≤ i.val := by unfold rank;omega
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by unfold rank;omega) sub,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 _*BitVec.ofNat 64 256+BitVec.ofNat 64 4096=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add];unfold ctrAt wordAddress msgWord;congr 1 <;> omega

theorem salt_address (i : Index) : ((BitVec.ofNat 64 i.val) <<< (4 : Nat))+5637148704=destAt i := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 i.val*BitVec.ofNat 64 16+BitVec.ofNat 64 5637148704=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add];unfold destAt;congr 1 <;> omega

theorem output_address (i : Index) (nz : rank i.val≠0) :
    (((BitVec.ofNat 64 (rank i.val))+signExtend12 (-1)) <<< (4 : Nat))+1536=readAt i := by
  have one : 1≤rank i.val := by omega
  rw [show signExtend12 (-1) = -(BitVec.ofNat 64 1) by decide]
  rw [←BitVec.sub_eq_add_neg]
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) one,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 _*BitVec.ofNat 64 16+BitVec.ofNat 64 1536=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add];unfold readAt offAt;rw [if_neg nz];congr 1 <;> omega

def beforeCall (s : MachineState) := walkRows s preRows

structure Input (s : MachineState) (i : Index) (ord left : Nat) extends Registers s ord left where
  pc : s.pc=address 1463
  loaded : s.getMem (indexAt ord)=BitVec.ofNat 64 i.val
  access : accessValid (indexAt ord) 8=true

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local irreducible] wordAddress

@[local simp] theorem pc_of_set (s : MachineState) (p : Word) : (s.setPC p).pc=p := rfl
@[local simp] theorem mem_of_set (s : MachineState) (p : Word) : (s.setPC p).mem=s.mem := rfl
@[local simp] theorem mem_of_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem=s.mem := by cases r <;> rfl
@[local simp] theorem mem_of_store (s : MachineState) (a v : Word) : (s.setMem a v).mem=fun w => if w==a then v else s.mem w := rfl
@[local simp] theorem open_zero (s : MachineState) : s.getReg .x0=0 := rfl
private theorem room_input (i : Index) (s : MachineState) (ord left : Nat) (r : Input s i ord left) :
    legal preRows s := by
  have first : memoryArgumentsValid s (.LD .x6 .x14 0)=true := by
    simpa [memoryArgumentsValid,memAccess,r.index,signExtend12] using r.access
  simp [preRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
    r.pc,address,r.index,r.access,r.input,signExtend12] <;> decide

theorem pre_run (i : Index) (s : MachineState) (ord left fuel : Nat) (r : Input s i ord left) :
    execute openingImage (7+fuel) s true =
      (do let z ← execute openingImage fuel (beforeCall s) true; return z.charge 10 0) :=
  walk_rows_run s preRows (room_input i s ord left r) pre_row_fetch fuel true

theorem before_regs (s : MachineState) (i : Index) (ord left : Nat) (r : Input s i ord left) :
    let t:=beforeCall s
    Registers t ord left ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      t.getReg .x28=BitVec.ofNat 64 (rank i.val) ∧ t.pc=address 1470 ∧
      t.mem=(s.setMem 1024 (ctrAt i)).mem := by
  dsimp only
  have simple (k : Reg) (a : k≠.x6) (b : k≠.x7) (c : k≠.x28) :
      (beforeCall s).getReg k=s.getReg k := by
    simp [beforeCall,walkRows,preRows,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c]
  refine ⟨⟨(simple _ (by decide) (by decide) (by decide)).trans r.input,
    (simple _ (by decide) (by decide) (by decide)).trans r.output,
    (simple _ (by decide) (by decide) (by decide)).trans r.selector,
    (simple _ (by decide) (by decide) (by decide)).trans r.width,
    (simple _ (by decide) (by decide) (by decide)).trans r.primitive,
    (simple _ (by decide) (by decide) (by decide)).trans r.index,
    (simple _ (by decide) (by decide) (by decide)).trans r.leftReg,
    (simple _ (by decide) (by decide) (by decide)).trans r.salt,
    (simple _ (by decide) (by decide) (by decide)).trans r.base,
    (simple _ (by decide) (by decide) (by decide)).trans r.divReg⟩,?_,?_,?_,?_⟩
  all_goals simp [beforeCall,walkRows,preRows,execInstrBr,r.pc,r.index,r.input,r.divReg,r.base,r.loaded,
    masked,decoded_rank,counter_address,address,show signExtend12 0=0#64 by decide,MachineState.getMem_setPC,MachineState.getMem_setReg]
  all_goals simp only [show signExtend12 0#12=0#64 by decide,BitVec.add_zero,r.loaded,show signExtend12 63#12=63#64 by decide]
  all_goals simp only [show BitVec.ofNat 64 i.val &&& 63#64=BitVec.ofNat 64 (i.val%64) from masked i,
    show rv64_remu (BitVec.ofNat 64 (i.val%64)) 11#64=BitVec.ofNat 64 (rank i.val) from decoded_rank i,
    show ((BitVec.ofNat 64 i.val-BitVec.ofNat 64 (rank i.val)) <<< (8:Nat))+4096#64=ctrAt i from counter_address i]

end TwoPermutationPrototype.GroupedOpening

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (rank msgWord)
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

def selectRows (direct : Bool) : List Row :=
  [(1471,.ADDI .x7 .x28 (-1)),(1472,.SLLI .x7 .x7 4),(1473,.BNE .x28 .x0 8)] ++
  (if direct then [(1474,.ADDI .x7 .x0 184)] else []) ++
  [(1475,.ADD .x7 .x7 .x12),(1476,.SLLI .x30 .x6 4),(1477,.ADD .x30 .x30 .x22)]
def copyRows : List Row := [(1478,.LD .x31 .x7 0),(1479,.SD .x30 .x31 0),(1480,.LD .x31 .x7 8),(1481,.SD .x30 .x31 8)]
def nextRows (last : Bool) : List Row := [(1482,.ADDI .x14 .x14 8),(1483,.ADDI .x17 .x17 (-1)),(1484,.BNE .x17 .x0 8108)] ++
  (if last then [(1485,.JAL .x0 2091264)] else [])
theorem post_parts (direct last : Bool) : postRows direct last=selectRows direct++copyRows++nextRows last := by
  cases direct <;> cases last <;> rfl

theorem legal_append (s : MachineState) (a b : List Row) (head : legal a s) (tail : legal b (walkRows s a)) :
    legal (a++b) s := by
  induction a generalizing s with
  | nil => exact tail
  | cons p a ih =>
    rcases p with ⟨i,op⟩
    exact ⟨head.1,head.2.1,ih _ head.2.2 tail⟩

def Direct (i : Index) := decide (rank i.val=0)
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

theorem rank_zero (i : Index) : BitVec.ofNat 64 (rank i.val)=0#64 ↔ rank i.val=0 := by
  constructor
  · intro h;have e:=congrArg BitVec.toNat h
    have small : rank i.val<2^64 := by unfold rank;omega
    change rank i.val%2^64=0 at e;omega
  · intro h;rw [h]

theorem choose_legal (s : MachineState) (i : Index) (pc : s.pc=address 1471)
    (sub : s.getReg .x28=BitVec.ofNat 64 (rank i.val)) :
    legal (selectRows (Direct i)) s := by
  by_cases zero : rank i.val=0
  all_goals simp [selectRows,Direct,zero,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,sub,address,
    beq_iff_eq,rank_zero, show signExtend13 8#13=8#64 by decide] <;> decide

def choose (s : MachineState) (i : Index) := walkRows s (selectRows (Direct i))
theorem choose_keeps (s : MachineState) (i : Index) (r : Reg) (a : r≠.x7) (b : r≠.x30) :
    (choose s i).getReg r=s.getReg r := by
  unfold choose selectRows;cases (Direct i) <;> by_cases eq : s.getReg .x28=0#64 <;>
    simp [walkRows,execInstrBr,Ne.symm a,Ne.symm b,eq,beq_iff_eq]

theorem chosen_memory (s : MachineState) (i : Index) : (choose s i).mem=s.mem := by
  unfold choose selectRows;cases Direct i <;> by_cases eq : s.getReg .x28=0#64 <;> simp [walkRows,execInstrBr,eq,beq_iff_eq]

theorem chosen (s : MachineState) (i : Index) (pc : s.pc=address 1471)
    (idx : s.getReg .x6=BitVec.ofNat 64 i.val) (sub : s.getReg .x28=BitVec.ofNat 64 (rank i.val))
    (out : s.getReg .x12=1536) (salts : s.getReg .x22=5637148704) :
    (choose s i).pc=address 1478 ∧ (choose s i).getReg .x7=readAt i ∧ (choose s i).getReg .x30=destAt i := by
  have dst : BitVec.ofNat 64 i.val <<< (4:Nat)+5637148704#64=destAt i := salt_address i
  by_cases zero : rank i.val=0
  · simp [choose,walkRows,selectRows,Direct,zero,execInstrBr,pc,idx,sub,address,out,salts,beq_iff_eq,
      show signExtend12 184#12=184#64 by decide,show signExtend13 8#13=8#64 by decide,dst]
    simpa only [readAt,offAt,if_pos zero] using (show 184#64+1536#64=BitVec.ofNat 64 (1536+184) by decide)
  · have neq : BitVec.ofNat 64 (rank i.val)≠0#64 := mt (rank_zero i).mp zero
    have src := output_address i zero
    change ((BitVec.ofNat 64 (rank i.val)+signExtend12 4095#12) <<< (4:Nat))+1536#64=readAt i at src
    simp at src
    simp [choose,walkRows,selectRows,Direct,zero,execInstrBr,pc,idx,sub,neq,address,out,salts,beq_iff_eq,
      show signExtend13 8#13=8#64 by decide,dst]
    exact src

theorem copy_addresses (i : Index) :
    accessValid (readAt i) 8=true ∧ accessValid (readAt i+8) 8=true ∧
    accessValid (destAt i) 8=true ∧ accessValid (destAt i+8) 8=true ∧ readAt i+8≠destAt i := by
  have hi : i.val<16777216:=i.isLt
  have r : rank i.val<11 := by unfold rank;omega
  have off : offAt i<200 ∧ offAt i%8=0 := by unfold offAt;split <;> constructor <;> omega
  unfold readAt destAt
  rw [show (8 : Word)=BitVec.ofNat 64 8 from rfl,←BitVec.ofNat_add,←BitVec.ofNat_add]
  have valid (a : Nat) (al : a%8=0) (room : a+8≤2^36) : accessValid (BitVec.ofNat 64 a) 8=true := by
    exact Opening.aligned_access a al room
  refine ⟨valid _ (by omega) (by omega),valid _ (by omega) (by omega),
    valid _ (by omega) (by omega),valid _ (by omega) (by omega),?_⟩
  intro eq
  have := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 1536+offAt i+8<2^64),
    Nat.mod_eq_of_lt (by omega : 5637148704+16*i.val<2^64)] at this
  omega

def copied (s : MachineState) := walkRows s copyRows
def installed (s : MachineState) (i : Index) :=
  (s.setMem (destAt i) (s.getMem (readAt i))).setMem (destAt i+8) (s.getMem (readAt i+8))

theorem copy_legal (s : MachineState) (i : Index) (pc : s.pc=address 1478) (r : s.getReg .x7=readAt i)
    (d : s.getReg .x30=destAt i) : legal copyRows s := by
  obtain ⟨a,b,c,e,_⟩:=copy_addresses i
  simp [copyRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,r,d,address,a,b,c,e,
    show signExtend12 8#12=8#64 by decide,show signExtend12 0#12=0#64 by decide] <;> exact ⟨b,e⟩

theorem copied_mem (s : MachineState) (i : Index) (r : s.getReg .x7=readAt i) (d : s.getReg .x30=destAt i) :
    (copied s).mem=(installed s i).mem := by
  obtain ⟨_,_,_,_,ne⟩:=copy_addresses i
  have ne' : readAt i+8#64≠destAt i:=ne
  simp [copied,walkRows,copyRows,execInstrBr,r,d,installed,MachineState.getMem_setMem_ne ne',mem_of_store,
    show signExtend12 8#12=8#64 by decide,show signExtend12 0#12=0#64 by decide]

theorem copied_keeps (s : MachineState) (r : Reg) (ne : r≠.x31) : (copied s).getReg r=s.getReg r := by
  simp [copied,walkRows,copyRows,execInstrBr,Ne.symm ne]

theorem copied_pc (s : MachineState) (pc : s.pc=address 1478) : (copied s).pc=address 1482 := by
  simp [copied,walkRows,copyRows,execInstrBr,pc,address]

end TwoPermutationPrototype.GroupedOpening

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (rank)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set open_zero
attribute [local simp] mem_of_reg MachineState.getMem_setPC MachineState.getMem_setReg

def finalPC (left : Nat) := if left=1 then address 13 else address 1463
def advanced (s : MachineState) (left : Nat) := walkRows s (nextRows (decide (left=1)))

private theorem decremented (left : Nat) (l : 0<left) :
    countWord left+signExtend12 (-1)=countWord (left-1) := by
  have sub := BitVec.ofNat_sub_ofNat_of_le (w:=64) left 1 (by decide) l
  rw [BitVec.sub_eq_add_neg] at sub
  exact sub

private theorem counter_zero (left : Nat) (l : 0<left) (small : left≤16777216) :
    countWord (left-1)=0#64 ↔ left=1 := by
  constructor
  · intro h;have z:=congrArg BitVec.toNat h
    change (left-1)%2^64=0 at z;omega
  · intro h;subst left;rfl

private theorem index_bump (ord : Nat) : indexAt ord+signExtend12 8=indexAt (ord+1) := by
  change BitVec.ofNat 64 _+BitVec.ofNat 64 8=_
  rw [←BitVec.ofNat_add];unfold indexAt;congr 1 <;> omega

private def bump (s : MachineState) :=
  execInstrBr (execInstrBr s (.ADDI .x14 .x14 8)) (.ADDI .x17 .x17 (-1))

private theorem bump_info (s : MachineState) (ord left : Nat) (l : 0<left)
    (pc : s.pc=address 1482) (idx : s.getReg .x14=indexAt ord) (count : s.getReg .x17=countWord left) :
    (bump s).pc=address 1484 ∧ (bump s).getReg .x14=indexAt (ord+1) ∧
    (bump s).getReg .x17=countWord (left-1) ∧ (bump s).mem=s.mem := by
  refine ⟨?_,?_,?_,?_⟩
  · change s.pc+4+4=_;rw [pc];rfl
  · change s.getReg .x14+signExtend12 8=_;rw [idx];exact index_bump ord
  · change s.getReg .x17+signExtend12 (-1)=_;rw [count];exact decremented left l
  · rfl

private theorem back (s : MachineState) (pc : s.pc=address 1484) (nz : s.getReg .x17≠0#64) :
    execInstrBr s (.BNE .x17 .x0 8108)=s.setPC (address 1463) := by
  have yes : (s.getReg .x17 != s.getReg .x0)=true := by simp [open_zero,nz]
  simp only [execInstrBr,yes,ite_true,pc]
  exact congrArg s.setPC (by decide : address 1484+signExtend13 8108=address 1463)

private theorem fall (s : MachineState) (pc : s.pc=address 1484) (z : s.getReg .x17=0#64) :
    execInstrBr s (.BNE .x17 .x0 8108)=s.setPC (address 1485) := by
  simp only [execInstrBr,open_zero,z,beq_self_eq_true,ite_true,pc]
  exact congrArg s.setPC (by decide : address 1484+4=address 1485)

private theorem exit_jump (s : MachineState) (pc : s.pc=address 1485) :
    execInstrBr s (.JAL .x0 2091264)=s.setPC (address 13) := by
  change s.setPC (s.pc+signExtend21 2091264)=_
  rw [pc];exact congrArg s.setPC (by decide : address 1485+signExtend21 2091264=address 13)

private def firstMoves : List Row := [(1482,.ADDI .x14 .x14 8),(1483,.ADDI .x17 .x17 (-1))]
private def lastMoves (last : Bool) : List Row := if last then [(1484,.BNE .x17 .x0 8108),(1485,.JAL .x0 2091264)]
  else [(1484,.BNE .x17 .x0 8108)]

private theorem next_parts (last : Bool) : nextRows last=firstMoves++lastMoves last := by cases last <;> rfl
private theorem first_value (s : MachineState) : walkRows s firstMoves=bump s := rfl
private theorem first_legal (s : MachineState) (pc : s.pc=address 1482) : legal firstMoves s := by
  refine ⟨pc,rfl,?_,rfl,trivial⟩
  change s.pc+4=_
  rw [pc];rfl

private theorem last_done (s : MachineState) (pc : s.pc=address 1484) (z : s.getReg .x17=0#64) :
    legal (lastMoves true) s ∧ walkRows s (lastMoves true)=s.setPC (address 13) := by
  have first:=fall s pc z
  have atJump:=congrArg MachineState.pc first
  refine ⟨⟨pc,rfl,atJump,rfl,trivial⟩,?_⟩
  simp only [lastMoves,ite_true,walkRows,List.foldl_cons,List.foldl_nil,first,exit_jump _ (show (s.setPC (address 1485)).pc=address 1485 from rfl)]
  rfl

private theorem last_again (s : MachineState) (pc : s.pc=address 1484) (z : s.getReg .x17≠0#64) :
    legal (lastMoves false) s ∧ walkRows s (lastMoves false)=s.setPC (address 1463) :=
  ⟨⟨pc,rfl,trivial⟩,back s pc z⟩

private theorem walk_join (s : MachineState) (xs ys : List Row) :
    walkRows s (xs++ys)=walkRows (walkRows s xs) ys := by
  simp only [walkRows,List.foldl_append]

private theorem next_value (s : MachineState) (last : Bool) :
    walkRows s (nextRows last)=walkRows (bump s) (lastMoves last) := by
  rw [next_parts,walk_join,first_value]

private theorem next_legal (s : MachineState) (last : Bool) (pc : s.pc=address 1482)
    (good : legal (lastMoves last) (bump s)) : legal (nextRows last) s := by
  rw [next_parts];apply legal_append _ _ _ (first_legal s pc);rw [first_value];exact good

attribute [local irreducible] bump walkRows nextRows

theorem next_ok (s : MachineState) (ord left : Nat) (pc : s.pc=address 1482) (l : 0<left) (hi : left≤16777216)
    (index : s.getReg .x14=indexAt ord) (counter : s.getReg .x17=countWord left) :
    legal (nextRows (decide (left=1))) s ∧ (advanced s left).pc=finalPC left ∧
      (advanced s left).getReg .x14=indexAt (ord+1) ∧ (advanced s left).getReg .x17=countWord (left-1) ∧
      (advanced s left).mem=s.mem := by
  have br:=bump_info s ord left l pc index counter
  have test : (bump s).getReg .x17=0#64 ↔ left=1 := br.2.2.1 ▸ counter_zero left l hi
  by_cases last : left=1
  · have d:=last_done (bump s) br.1 (test.mpr last)
    rw [decide_eq_true last,advanced,decide_eq_true last,next_value,d.2,finalPC,if_pos last]
    exact ⟨next_legal s true pc d.1,rfl,br.2.1,br.2.2.1,br.2.2.2⟩
  · have d:=last_again (bump s) br.1 (mt test.mp last)
    rw [decide_eq_false last,advanced,decide_eq_false last,next_value,d.2,finalPC,if_neg last]
    exact ⟨next_legal s false pc d.1,rfl,br.2.1,br.2.2.1,br.2.2.2⟩

attribute [local semireducible] walkRows nextRows

private theorem rows_preserve (rows : List Row) (s : MachineState) (r : Reg)
    (each : ∀ p∈rows, ∀ st : MachineState, (execInstrBr st p.2).getReg r=st.getReg r) :
    (walkRows s rows).getReg r=s.getReg r := by
  induction rows generalizing s with
  | nil => unfold walkRows;rfl
  | cons p rest ih => unfold walkRows;exact (ih (execInstrBr s p.2) (fun t h => each t (List.mem_cons_of_mem _ h))).trans (each p (by simp) s)

private theorem branch_reg (u : MachineState) (r : Reg) (imm : BitVec 13) :
    (execInstrBr u (.BNE .x17 .x0 imm)).getReg r=u.getReg r := by
  change (if (u.getReg .x17 != u.getReg .x0) then u.setPC (u.pc+signExtend13 imm) else u.setPC (u.pc+4)).getReg r=_
  split <;> exact MachineState.getReg_setPC ..

private theorem jump_reg (u : MachineState) (r : Reg) (imm : BitVec 21) :
    (execInstrBr u (.JAL .x0 imm)).getReg r=u.getReg r := MachineState.getReg_setPC ..

theorem next_keeps (s : MachineState) (left : Nat) (r : Reg) (a : r≠.x14) (b : r≠.x17) :
    (advanced s left).getReg r=s.getReg r := by
  unfold advanced;apply rows_preserve;intro p h u
  unfold nextRows at h;cases tag : (decide (left=1)) <;>
    simp only [tag,Bool.false_eq_true,ite_false,ite_true,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
  · rcases h with h|h|h <;> subst p <;> first | exact branch_reg u r _ | simp [execInstrBr,Ne.symm a,Ne.symm b]
  · rcases h with h|h|h|h <;> subst p
    all_goals first | exact branch_reg u r _ | exact jump_reg u r _ |
      simp [execInstrBr,Ne.symm a,Ne.symm b]

def receives (s : MachineState) (y : BitVec 1600) := writeBits (beforeCall s) (wordAddress 192) y
def finishOne (s : MachineState) (i : Index) (left : Nat) (y : BitVec 1600) :=
  advanced (copied (choose (receives s y) i)) left

def perTrace (s : MachineState) (i : Index) (left : Nat) : OracleComp World MachineState := do
  let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (beforeCall s)) 128)))))
  return finishOne s i left y

def perSteps (i : Index) (left : Nat) := 21+(if rank i.val=0 then 1 else 0)+(if left=1 then 1 else 0)
def perCycles (i : Index) (left : Nat) := perSteps i left+10

theorem per_run (s : MachineState) (i : Index) (ord left fuel : Nat) (l : 0<left) (hi : left≤16777216)
    (r : Input s i ord left) : execute openingImage (perSteps i left+fuel) s true =
      (do let t ← perTrace s i left; let z ← execute openingImage fuel t true; return z.charge (perCycles i left) 1) := by
  let rows:=postRows (Direct i) (decide (left=1))
  have lengths : perSteps i left=7+1+rows.length ∧ perCycles i left=10+8+price rows := by
    dsimp [rows,Direct,perSteps,perCycles,postRows,price]
    by_cases z : rank i.val=0 <;> by_cases x : left=1 <;> simp [z,x,instructionCycles]
  obtain ⟨pr,idx,sub,pc,_⟩:=before_regs s i ord left r
  have fetch : fetch openingImage (beforeCall s)=some (.base .ECALL) :=
    prefix_fetch_base _ 1470 _ (by decide) pc (by decide +kernel)
  have call:=execute_permutation_call openingImage (rows.length+fuel) (beforeCall s) true 128 192
    (by decide) (by decide) pr.input pr.output pr.selector pr.width pr.primitive fetch
  rw [show perSteps i left+fuel=7+((rows.length+fuel)+1) by omega,pre_run i s ord left _ r]
  rw [call];simp only [perTrace,bind_assoc,pure_bind]
  apply bind_congr; intro y
  let w:=receives s y
  let a:=choose w i
  let b:=copied a
  have regs (k : Reg) : w.getReg k=(beforeCall s).getReg k := writeBits_register ..
  have wp : w.pc=address 1471 := by rw [show w.pc=(beforeCall s).pc+4 from written_pc ..,pc];rfl
  have chooseOk:=choose_legal w i wp ((regs _).trans sub)
  obtain ⟨ap,ar,ad⟩:=chosen w i wp ((regs _).trans idx) ((regs _).trans sub) ((regs _).trans pr.output) ((regs _).trans pr.salt)
  have keep (k : Reg) (h7 : k≠.x7 :=by decide) (h30 : k≠.x30 :=by decide) (h31 : k≠.x31 :=by decide) :
      b.getReg k=(beforeCall s).getReg k :=
    (copied_keeps a k h31).trans ((choose_keeps w i k h7 h30).trans (regs k))
  have t:=next_ok b ord left (copied_pc a ap) l hi ((keep .x14).trans pr.index) ((keep .x17).trans pr.leftReg)
  have ok : legal rows w := by
    rw [show rows=selectRows (Direct i)++copyRows++nextRows (decide (left=1)) from post_parts ..]
    apply legal_append
    · exact legal_append w _ _ chooseOk (copy_legal a i ap ar ad)
    · simpa only [b,a,copied,choose,walkRows,List.foldl_append] using t.1
  change (do let z ← execute openingImage (rows.length+fuel) w true;return (z.charge 8 1).charge 10 0)=_
  rw [walk_rows_run w rows ok (post_row_fetch (Direct i) (decide (left=1))) fuel true]
  have same : walkRows w rows=finishOne s i left y := by
    rw [show rows=selectRows (Direct i)++copyRows++nextRows (decide (left=1)) from post_parts ..]
    simp only [finishOne,advanced,copied,choose,walkRows,List.foldl_append];rfl
  rw [same,lengths.2];simp only [bind_assoc,pure_bind]
  apply bind_congr;intro z;apply congrArg pure;cases z;simp [Execution.charge,Nat.add_assoc] <;> omega

end TwoPermutationPrototype.GroupedOpening
