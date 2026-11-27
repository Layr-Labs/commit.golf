import CommitGolfCandidate.Stage3cPassEntry
import CommitGolfCandidate.Stage3cPointerNode
import CommitGolfCandidate.Stage3cPointerEffect
import CommitGolfCandidate.Stage3cPointerFrame
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option Elab.async false

def StageLaw (d : Height) : Prop := ∀ (o : Oracle) (s : MachineState) (base : Nat→Output) (salt : Late.SaltTape),
    s.pc=pcAt (passHeader d) → Common s → TreeState o.compression base salt d.val s →
    ∃ t, t.pc=pcAt (passEnd d) ∧ Common t ∧ TreeState o.compression base salt (d.val+1) t ∧
      Runs .commit true o s t (passSteps d) (passCycles d) (count d*calls d)

theorem pointer_shape : ∀ d : Height, ¬chained d →
    calls d=1 ∧ passEnd d≤11529 ∧
    (d.val=23 → wireWidth d=256 ∧ tileSize d=0 ∧ count d=1 ∧
      (headerOps d).length+1=passSteps d ∧ bodyEntry d=tailPC d ∧ tailPC d+1=passEnd d) ∧
    (tileSize d≠0 → (wireWidth d=256 ∨ wireWidth d=240) ∧ remainder d=0 ∧ count d=tiles d*128 ∧
      0<tiles d ∧ tiles d<2^20 ∧ (headerOps d).length+tiles d*(128*laneWords d+2)=passSteps d ∧
      bodyEntry d=mainPC d ∧ mainPC d+128*laneWords d+2=passEnd d ∧ 3≤laneWords d) ∧
    (tileSize d=0 ∧ d.val≠23 → wireWidth d=240 ∧ count d≤64 ∧ 0<count d ∧
      (headerOps d).length+count d*laneWords d=passSteps d ∧ bodyEntry d=tailPC d ∧
      tailPC d+count d*laneWords d=passEnd d ∧ 3≤laneWords d) := by
  decide +kernel

theorem tree_mem {H base salt d s t} (eq : s.mem=t.mem) (tree : TreeState H base salt d s) :
    TreeState H base salt d t := by
  refine ⟨?_,?_,?_⟩
  · intro k hk i hi;exact (read_only_mem s t _ _ eq).symm.trans (tree.nodes k hk i hi)
  · intro ix;exact (read_only_mem s t _ _ eq).symm.trans (tree.salts ix)
  · intro h j hj
    exact ⟨(read_only_mem s t _ _ eq).symm.trans (tree.pads h j hj).1,
      fun plain => (read_only_mem s t _ _ eq).symm.trans ((tree.pads h j hj).2 plain)⟩

theorem rows_mem {H base d n s t} (eq : s.mem=t.mem) (rows : doneRows H base d n s) :
    doneRows H base d n t := by
  intro j hj;exact (read_only_mem s t _ _ eq).symm.trans (rows j hj)

theorem common_keep {s t : MachineState} (c : Common s)
    (h : ∀ r, r≠.x10 → r≠.x12 → t.getReg r=s.getReg r) : Common t where
  mode := (h .x5 (by decide) (by decide)).trans c.mode
  len := (h .x11 (by decide) (by decide)).trans c.len
  kind := (h .x13 (by decide) (by decide)).trans c.kind
  base := (h .x18 (by decide) (by decide)).trans c.base
  root := (h .x9 (by decide) (by decide)).trans c.root
  scratch := (h .x24 (by decide) (by decide)).trans c.scratch
  stride₁ := (h .x25 (by decide) (by decide)).trans c.stride₁
  stride₂ := (h .x26 (by decide) (by decide)).trans c.stride₂
  stride₃ := (h .x27 (by decide) (by decide)).trans c.stride₃

private theorem common_setPC {s : MachineState} {v : BitVec 64} (c : Common s) : Common (s.setPC v) where
  mode := by simpa [MachineState.getReg_setPC] using c.mode
  len := by simpa [MachineState.getReg_setPC] using c.len
  kind := by simpa [MachineState.getReg_setPC] using c.kind
  base := by simpa [MachineState.getReg_setPC] using c.base
  root := by simpa [MachineState.getReg_setPC] using c.root
  scratch := by simpa [MachineState.getReg_setPC] using c.scratch
  stride₁ := by simpa [MachineState.getReg_setPC] using c.stride₁
  stride₂ := by simpa [MachineState.getReg_setPC] using c.stride₂
  stride₃ := by simpa [MachineState.getReg_setPC] using c.stride₃

private theorem sext96 : signExtend12 (96 : BitVec 12)=BitVec.ofNat 64 96 := by decide

private theorem bump_src (h p : Nat) :
    BitVec.ofNat 64 (nodeAddress h (2*p))+signExtend12 96=
      BitVec.ofNat 64 (nodeAddress h (2*(p+1))) := by
  have step : nodeAddress h (2*(p+1))=nodeAddress h (2*p)+96 := by
    rw [(children_contiguous h p).2,(children_contiguous h (p+1)).2];omega
  rw [sext96,step,←BitVec.ofNat_add]

private theorem dst_gap (p : Nat) :
    CommitGolfCandidate.Late.gapOffset (p+1)=
      CommitGolfCandidate.Late.gapOffset p+(if p%2=1 then 64 else 32) := by
  unfold CommitGolfCandidate.Late.gapOffset
  have div := Nat.div_add_mod p 2
  let q := p/2
  by_cases even : p%2=0
  · have half : p=2*q := by
      have h := div
      rw [even,Nat.add_zero] at h
      change p=2*q
      exact h.symm
    have sum : p+1=1+2*q := by rw [half,Nat.add_comm]
    have qdiv : (p+1)/2=q := by
      rw [sum,Nat.add_mul_div_left 1 q (by decide : 0<2),Nat.div_eq_of_lt (by decide : 1<2),Nat.zero_add]
    have qmod : (p+1)%2=1 := by
      rw [sum,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by decide : 1<2)]
    have hif : (if p%2=1 then 64 else 32)=32 := by rw [even];decide
    rw [qdiv,qmod,hif,show q=p/2 from rfl,even,Nat.mul_one,Nat.mul_zero,Nat.add_zero]
  · have odd : p%2=1 := by have lt : p%2<2 := Nat.mod_lt _ (by decide);omega
    have half : p=2*q+1 := by
      have h := div
      rw [odd] at h
      change p=2*q+1
      exact h.symm
    have packed : p+1=2*(q+1) := by
      rw [half,Nat.add_assoc,show (1:Nat)+1=2*1 by decide,←Nat.mul_add]
    have qdiv : (p+1)/2=q+1 := by rw [packed];exact Nat.mul_div_cancel_left _ (by decide : 0<2)
    have qmod : (p+1)%2=0 := by rw [packed,Nat.mul_mod_right]
    have hif : (if p%2=1 then 64 else 32)=64 := by rw [odd];decide
    rw [qdiv,qmod,hif,show q=p/2 from rfl,Nat.mul_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero]
    omega

private theorem bump_dst (h p : Nat) :
    BitVec.ofNat 64 (nodeAddress (h+1) p)+signExtend12 (ptrDstImm (decide (p%2=1)))=
      BitVec.ofNat 64 (nodeAddress (h+1) (p+1)) := by
  have step : nodeAddress (h+1) (p+1)=nodeAddress (h+1) p+(if p%2=1 then 64 else 32) := by
    unfold nodeAddress;rw [dst_gap];omega
  by_cases odd : p%2=1
  · have hd : decide (p%2=1)=true := by simp [odd]
    rw [hd]
    change BitVec.ofNat 64 (nodeAddress (h+1) p)+signExtend12 64=_
    rw [signExtend12_64,step,if_pos odd]
    change BitVec.ofNat 64 (nodeAddress (h+1) p)+BitVec.ofNat 64 64=
      BitVec.ofNat 64 (nodeAddress (h+1) p+64)
    rw [←BitVec.ofNat_add]
  · have hd : decide (p%2=1)=false := by simp [odd]
    rw [hd]
    change BitVec.ofNat 64 (nodeAddress (h+1) p)+signExtend12 32=_
    rw [signExtend12_32,step,if_neg odd]
    change BitVec.ofNat 64 (nodeAddress (h+1) p)+BitVec.ofNat 64 32=
      BitVec.ofNat 64 (nodeAddress (h+1) p+32)
    rw [←BitVec.ofNat_add]

private theorem dec_counter (n : Nat) (hn : 0<n) (h2 : n<2^64) :
    BitVec.ofNat 64 n+signExtend12 4095=BitVec.ofNat 64 (n-1) := by
  apply BitVec.eq_of_toNat_eq
  rw [signExtend12_4095,BitVec.toNat_add,BitVec.toNat_ofNat]
  have hto : BitVec.toNat (18446744073709551615 : BitVec 64)=2^64-1 := by decide
  rw [hto,Nat.mod_eq_of_lt h2]
  have hsum : n+(2^64-1)=(n-1)+2^64 := by omega
  rw [hsum,Nat.add_mod_right,BitVec.toNat_ofNat]

private theorem ofNat_bne_zero (n : Nat) (hn : n<2^64) :
    ((BitVec.ofNat 64 n) != (0 : BitVec 64))=decide (n≠0) := by
  by_cases h : n=0
  · subst h;simp
  · have ne : BitVec.ofNat 64 n≠0 := by
      intro eq
      have := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn] at this
      simp at this
      omega
    rw [bne_iff_ne.mpr ne]
    simp [h]

private theorem addi_go (s : MachineState) (rd : Reg) (imm : BitVec 12) :
    ordinaryStep s (.base (.ADDI rd rd imm))=
      some ((s.setReg rd (s.getReg rd+signExtend12 imm)).setPC (s.pc+4)) := by
  simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr]

private theorem slot_bounds (d : Height) (p : Nat) (inside : p<count d) :
    let src:=nodeAddress d.val (2*p)
    let dst:=nodeAddress (d.val+1) p
    src+96≤MEMORY_BYTES ∧ src%8=0 ∧ dst+32≤MEMORY_BYTES ∧ dst%8=0 := by
  refine ⟨?_,aligned_node _ _,?_,aligned_node _ _⟩
  · have disj:=parent_row_disjoint d.val p 0 d.isLt
      (by change p<levelCount (d.val+1);simpa [count] using inside)
    have below:=parent_below_salts (d.val+1) 0
      (by change 0<levelCount (d.val+1);simpa [count] using Nat.lt_of_le_of_lt (Nat.zero_le p) inside)
    change nodeAddress d.val (2*p)+96≤2^36
    unfold rowBase at below
    omega
  · have below:=parent_below_salts (d.val+1) p
      (by change p<levelCount (d.val+1);simpa [count] using inside)
    change nodeAddress (d.val+1) p+32≤2^36
    unfold rowBase at below
    omega

theorem run_range (d : Height) (o : Oracle) (origin loc g n : Nat) (s : MachineState)
    (base : Nat→Output) (salt : Late.SaltTape)
    (simple : ¬chained d) (wide : wireWidth d=256 ∨ wireWidth d=240) (lw3 : 3≤laneWords d)
    (limit : g+n≤count d) (room : origin+laneWords d*(loc+n)≤11529)
    (slots : ∀ i, i<n → PtrSlot (origin+laneWords d*(loc+i)) (wireWidth d) (decide ((g+i)%2=1)))
    (pc : s.pc=pcAt (origin+laneWords d*loc))
    (x10 : s.getReg .x10=BitVec.ofNat 64 (nodeAddress d.val (2*g)))
    (x12 : s.getReg .x12=BitVec.ofNat 64 (nodeAddress (d.val+1) g))
    (cm : Common s) (tree : TreeState o.compression base salt d.val s)
    (rows : doneRows o.compression base d.val g s) :
    ∃ t, t.pc=pcAt (origin+laneWords d*(loc+n)) ∧
      t.getReg .x10=BitVec.ofNat 64 (nodeAddress d.val (2*(g+n))) ∧
      t.getReg .x12=BitVec.ofNat 64 (nodeAddress (d.val+1) (g+n)) ∧
      (∀ r, r≠.x10 → r≠.x12 → t.getReg r=s.getReg r) ∧
      Common t ∧ TreeState o.compression base salt d.val t ∧ doneRows o.compression base d.val (g+n) t ∧
      Runs .commit true o s t (n*laneWords d) (n*(laneWords d+7)) n := by
  induction n generalizing loc g s with
  | zero =>
    refine ⟨s, by simpa using pc, by simpa using x10, by simpa using x12, fun _ _ _ => rfl, cm, tree,
      by simpa using rows, by simpa using runs_id .commit true o s⟩
  | succ n ih =>
    have inside : g<count d := by omega
    have code := slots 0 (by omega)
    have fit : origin+laneWords d*loc+5<11543 := by
      have mono : origin+laneWords d*loc≤origin+laneWords d*(loc+(n+1)) := by
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_left _ (Nat.le_add_right loc (n+1))
      omega
    obtain ⟨rs, asrc, rd, adst⟩ := slot_bounds d g inside
    obtain ⟨t, run, x10', x12', pc', keep, mem⟩ :=
      slot_run d o s (origin+laneWords d*loc) (decide (g%2=1)) fit wide code pc cm.mode cm.len cm.kind
        (nodeAddress d.val (2*g)) (nodeAddress (d.val+1) g) x10 x12 rs asrc rd adst
    have x10n : t.getReg .x10=BitVec.ofNat 64 (nodeAddress d.val (2*(g+1))) := by rw [x10'];exact bump_src d.val g
    have x12n : t.getReg .x12=BitVec.ofNat 64 (nodeAddress (d.val+1) (g+1)) := by rw [x12'];exact bump_dst d.val g
    have pcn : t.pc=pcAt (origin+laneWords d*(loc+1)) := by
      rw [pc'];congr 1
      rw [Nat.mul_add,Nat.mul_one,Nat.add_assoc]
    have cmt := common_keep cm keep
    have eff := pointer_effect o.compression d g s t simple inside tree.pads mem
    have tree' := node_frame tree eff inside
    have rows' := grow_row tree rows eff inside
    have slots' : ∀ i, i<n → PtrSlot (origin+laneWords d*((loc+1)+i)) (wireWidth d)
        (decide ((g+1+i)%2=1)) := by
      intro i hi
      have raw := slots (i+1) (by omega)
      have hidx : loc+(i+1)=(loc+1)+i := by omega
      have hglob : g+(i+1)=g+1+i := by omega
      rw [hidx,hglob] at raw
      exact raw
    have roomNext : origin+laneWords d*((loc+1)+n)≤11529 := by
      have eq : (loc+1)+n=loc+(n+1) := by omega
      simpa [eq] using room
    obtain ⟨u, upc, ux10, ux12, ukeep, ucm, utree, urows, utail⟩ :=
      ih (loc+1) (g+1) t (by omega) roomNext slots' pcn x10n x12n cmt tree' rows'
    have ug : g+1+n=g+(n+1) := by omega
    have ul : (loc+1)+n=loc+(n+1) := by omega
    rw [ug] at ux10 ux12 urows
    rw [ul] at upc
    refine ⟨u, upc, ux10, ux12, ?_, ucm, utree, urows, ?_⟩
    · intro r h10 h12;exact (ukeep r h10 h12).trans (keep r h10 h12)
    · have joined := runs_comp run utail
      have hs : laneWords d+n*laneWords d=(n+1)*laneWords d :=
        (Nat.add_comm _ _).trans (Nat.succ_mul n (laneWords d)).symm
      have hc : (laneWords d+7)+n*(laneWords d+7)=(n+1)*(laneWords d+7) :=
        (Nat.add_comm _ _).trans (Nat.succ_mul n (laneWords d+7)).symm
      have hq : 1+n=n+1 := by omega
      rw [hs,hc,hq] at joined
      exact joined

private theorem tile_code (d : Height) (simple : ¬chained d) (looped : tileSize d≠0) (j i : Nat) (hi : i<128) :
    PtrSlot (mainPC d+laneWords d*i) (wireWidth d) (decide ((j*128+i)%2=1)) := by
  have raw := ((pointer_sites d simple).2.1 looped).1 ⟨i,hi⟩
  have hmod : (j*128+i)%2=i%2 := by
    have : 128%2=0 := by decide
    rw [Nat.add_mod,Nat.mul_mod,this];simp
  simpa [hmod] using raw

private theorem straight_code (d : Height) (simple : ¬chained d) (tile0 : tileSize d=0) (notRoot : d.val≠23)
    (i : Nat) (hi : i<count d) :
    PtrSlot (tailPC d+laneWords d*i) (wireWidth d) (decide (i%2=1)) := by
  have info := (pointer_sites d simple).2.2 ⟨tile0,notRoot⟩
  exact info.2.1 ⟨i, by have := info.1;omega⟩ hi

private theorem loop_from (d : Height) (o : Oracle) (base : Nat→Output) (salt : Late.SaltTape)
    (simple : ¬chained d) (looped : tileSize d≠0)
    (wide : wireWidth d=256 ∨ wireWidth d=240) (lw3 : 3≤laneWords d)
    (parts : count d=tiles d*128) (gateAt : mainPC d+128*laneWords d+2=passEnd d)
    (endLe : passEnd d≤11529) (smallTiles : tiles d<2^20)
    (r : Nat) (hr : r≤tiles d) (s : MachineState)
    (pc : s.pc=pcAt (if r=0 then passEnd d else mainPC d))
    (x20 : s.getReg .x20=BitVec.ofNat 64 r)
    (x10 : s.getReg .x10=BitVec.ofNat 64 (nodeAddress d.val (2*((tiles d-r)*128))))
    (x12 : s.getReg .x12=BitVec.ofNat 64 (nodeAddress (d.val+1) ((tiles d-r)*128)))
    (cm : Common s) (tree : TreeState o.compression base salt d.val s)
    (rows : doneRows o.compression base d.val ((tiles d-r)*128) s) :
    ∃ t, t.pc=pcAt (passEnd d) ∧ Common t ∧ doneRows o.compression base d.val (count d) t ∧
      TreeState o.compression base salt d.val t ∧
      Runs .commit true o s t (r*(128*laneWords d+2)) (r*(128*(laneWords d+7)+2)) (r*128) := by
  induction r generalizing s with
  | zero =>
    refine ⟨s, by simpa using pc, cm, ?_, tree, by simpa using runs_id .commit true o s⟩
    simpa [parts, Nat.sub_zero] using rows
  | succ r ih =>
    have pcM : s.pc=pcAt (mainPC d) := by simpa using pc
    set doneIx : Nat := (tiles d-(r+1))*128
    have sub1 : tiles d-(r+1)+1=tiles d-r := by omega
    have advance : doneIx+128=(tiles d-r)*128 := by
      unfold doneIx
      rw [←sub1,Nat.add_mul,Nat.one_mul]
    have slots : ∀ i, i<128 → PtrSlot (mainPC d+laneWords d*(0+i)) (wireWidth d)
        (decide ((doneIx+i)%2=1)) := by
      intro i hi
      simpa [doneIx] using tile_code d simple looped (tiles d-(r+1)) i hi
    have room : mainPC d+laneWords d*(0+128)≤11529 := by
      rw [Nat.zero_add,Nat.mul_comm]
      have : mainPC d+128*laneWords d+2≤11529 := by rw [gateAt];exact endLe
      omega
    have lim : doneIx+128≤count d := by
      rw [advance,parts]
      exact Nat.mul_le_mul_right (k:=128) (Nat.sub_le (tiles d) r)
    obtain ⟨u, upc, ux10, ux12, ukeep, ucm, utree, urows, urun⟩ :=
      run_range d o (mainPC d) 0 doneIx 128 s base salt simple wide lw3 lim room slots pcM
        (by simpa [doneIx] using x10) (by simpa [doneIx] using x12) cm tree (by simpa [doneIx] using rows)
    have atAdd : u.pc=pcAt (mainPC d+128*laneWords d) := by
      simpa [Nat.zero_add,Nat.mul_comm] using upc
    have loop := (pointer_sites d simple).2.1 looped
    have insideCode : mainPC d+128*laneWords d<11543 := by
      have : mainPC d+128*laneWords d+2≤11529 := by rw [gateAt];exact endLe
      omega
    have found := decoded_site insideCode loop.2.1 u atAdd
    have st := addi_go u .x20 4095
    have runA := runs_step (coins := true) (o := o) found st
    let b := (u.setReg .x20 (u.getReg .x20+signExtend12 4095)).setPC (u.pc+4)
    have ux20 : u.getReg .x20=BitVec.ofNat 64 (r+1) := (ukeep .x20 (by decide) (by decide)).trans x20
    have rbound : r+1<2^64 := by have := smallTiles;omega
    have x20b : b.getReg .x20=BitVec.ofNat 64 r := by
      have step20 : b.getReg .x20=u.getReg .x20+signExtend12 4095 := by
        simp only [b,MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_eq (by decide : (.x20 : Reg)≠.x0)
      rw [step20,ux20,dec_counter (r+1) (by omega) rbound,Nat.add_sub_cancel]
    have x10b : b.getReg .x10=BitVec.ofNat 64 (nodeAddress d.val (2*((tiles d-r)*128))) := by
      have eq : b.getReg .x10=u.getReg .x10 := by
        simp only [b,MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ (by decide : (.x20 : Reg)≠.x10)
      rw [eq,ux10,advance]
    have x12b : b.getReg .x12=BitVec.ofNat 64 (nodeAddress (d.val+1) ((tiles d-r)*128)) := by
      have eq : b.getReg .x12=u.getReg .x12 := by
        simp only [b,MachineState.getReg_setPC]
        exact MachineState.getReg_setReg_ne _ _ _ _ (by decide : (.x20 : Reg)≠.x12)
      rw [eq,ux12,advance]
    have pcb : b.pc=pcAt (mainPC d+128*laneWords d+1) := by
      simp only [b,MachineState.setPC,atAdd,pc_succ]
    have keepB (reg : Reg) (ne : reg≠.x20) : b.getReg reg=u.getReg reg := by
      simp [b,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ ne.symm]
    have cmb : Common b := {
      mode := (keepB .x5 (by decide)).trans ucm.mode
      len := (keepB .x11 (by decide)).trans ucm.len
      kind := (keepB .x13 (by decide)).trans ucm.kind
      base := (keepB .x18 (by decide)).trans ucm.base
      root := (keepB .x9 (by decide)).trans ucm.root
      scratch := (keepB .x24 (by decide)).trans ucm.scratch
      stride₁ := (keepB .x25 (by decide)).trans ucm.stride₁
      stride₂ := (keepB .x26 (by decide)).trans ucm.stride₂
      stride₃ := (keepB .x27 (by decide)).trans ucm.stride₃ }
    have memB : b.mem=u.mem := by simp [b,MachineState.setReg,MachineState.setPC]
    have treeB := tree_mem memB.symm utree
    have rowsB := rows_mem memB.symm (by simpa [advance] using urows)
    set more : Bool := decide (r≠0)
    have flag : (b.getReg .x20 != 0)=more := by
      have rlt : r<2^64 := by have := smallTiles;omega
      rw [x20b,ofNat_bne_zero r rlt]
    have atGate : b.pc=pcAt (gatePos false (passEnd d)) := by
      have h : gatePos false (passEnd d)=mainPC d+128*laneWords d+1 := by
        unfold gatePos
        rw [show (if false then 2 else 1)=1 by rfl,←gateAt]
        omega
      simpa [h] using pcb
    have runG := gate_run false more (mainPC d) (passEnd d) b o atGate loop.2.2.2 flag
    let c := b.setPC (gatePC (mainPC d) (passEnd d) more)
    have cmc := common_setPC cmb (s:=b) (v:=gatePC (mainPC d) (passEnd d) more)
    have memC : c.mem=b.mem := by
      change (b.setPC (gatePC (mainPC d) (passEnd d) more)).mem=b.mem
      rfl
    have treeC := tree_mem memC.symm treeB
    have rowsC := rows_mem memC.symm rowsB
    have pcC : c.pc=pcAt (if r=0 then passEnd d else mainPC d) := by
      by_cases hr0 : r=0
      · have mf : more=false := by simp [more,hr0]
        simp [c,MachineState.setPC,gatePC,mf,hr0]
      · have mt : more=true := by simp [more,hr0]
        simp [c,MachineState.setPC,gatePC,mt,if_neg hr0]
    have x20c : c.getReg .x20=BitVec.ofNat 64 r := by simpa [c,MachineState.getReg_setPC] using x20b
    have x10c : c.getReg .x10=BitVec.ofNat 64 (nodeAddress d.val (2*((tiles d-r)*128))) := by
      simpa [c,MachineState.getReg_setPC] using x10b
    have x12c : c.getReg .x12=BitVec.ofNat 64 (nodeAddress (d.val+1) ((tiles d-r)*128)) := by
      simpa [c,MachineState.getReg_setPC] using x12b
    have rowsNext : doneRows o.compression base d.val ((tiles d-r)*128) c := rowsC
    obtain ⟨t,tpc,tcm,trows,ttree,ttail⟩ :=
      ih (by omega) c pcC x20c x10c x12c cmc treeC rowsNext
    refine ⟨t,tpc,tcm,trows,ttree,?_⟩
    have runA' : Runs .commit true o u b 1 1 0 := by simpa [b,instructionCycles] using runA
    have runG' : Runs .commit true o b c 1 1 0 := by simpa [c,gateWords] using runG
    have joined := runs_comp (runs_comp (runs_comp urun runA') runG') ttail
    have hs : ((128*laneWords d+1)+1)+r*(128*laneWords d+2)=(r+1)*(128*laneWords d+2) := by
      have : (128*laneWords d+1)+1=128*laneWords d+2 := by omega
      rw [this];exact (Nat.add_comm _ _).trans (Nat.succ_mul r _).symm
    have hc : ((128*(laneWords d+7)+1)+1)+r*(128*(laneWords d+7)+2)=(r+1)*(128*(laneWords d+7)+2) := by
      have : (128*(laneWords d+7)+1)+1=128*(laneWords d+7)+2 := by omega
      rw [this];exact (Nat.add_comm _ _).trans (Nat.succ_mul r _).symm
    have hq : ((128+0)+0)+r*128=(r+1)*128 := by
      have : (128+0)+0=128 := by omega
      rw [this];exact (Nat.add_comm _ _).trans (Nat.succ_mul r _).symm
    rw [hs,hc,hq] at joined
    exact joined

theorem pointer_pass (d : Height) (simple : ¬chained d) : StageLaw d := by
  intro o s base salt pc cm tree
  obtain ⟨oneCall,endLe,rootShape,loopShape,tailShape⟩ := pointer_shape d simple
  have cycle := phase_counts d
  let a := entered s d
  have entry : s.pc=pcAt (pureEntry d) := by simpa [pureEntry,if_neg simple] using pc
  have head : Runs .commit true o s a (headerOps d).length (headerOps d).length 0 :=
    runs_pure (header_run d s entry)
  obtain ⟨ef,memEq⟩ := entered_frame d s entry cm
  have treeA := tree_mem memEq.symm tree
  by_cases root : d.val=23
  · obtain ⟨w256,noTile,one,cost,atTail,ends⟩ := rootShape root
    have aPC : a.pc=pcAt (tailPC d) := by simpa [atTail] using ef.pc
    have x := ef.ptrSrc simple
    have y := ef.ptrDst simple
    have inside0 : 0<count d := by rw [one];decide
    obtain ⟨rs,asrc,rd,adst⟩ := slot_bounds d 0 inside0
    have word := (pointer_sites d simple).1 root
    have fetched := decoded_site (by omega) word.1 a aPC
    let answer : Output := o.compression (readBuffer a (nodeAddress d.val (2*0)) 96)
    have ident : storeReply d answer=answer := by
      simp only [storeReply,w256,Nat.mod_eq_of_lt answer.isLt,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    let t := writeBits a (BitVec.ofNat 64 (nodeAddress (d.val+1) 0)) answer
    have run := hash_runs o a (nodeAddress d.val (2*0)) (nodeAddress (d.val+1) 0) fetched
      ef.mode ef.len ef.kind x y rs asrc rd adst
    have mem : t.mem=(writeBits a (BitVec.ofNat 64 (nodeAddress (d.val+1) 0))
        (storeReply d (o.compression (readBuffer a (nodeAddress d.val (2*0)) 96)))).mem := by
      simp only [t];rw [←ident]
    have eff := pointer_effect o.compression d 0 a t simple inside0 treeA.pads mem
    have rows := grow_row treeA (fun _ h => by omega) eff inside0
    have closed := close_level (node_frame treeA eff inside0) (by simpa [one] using rows)
    have pcT : t.pc=pcAt (passEnd d) := by
      have hpc : t.pc=a.pc+4 := by
        simpa [t] using congrArg MachineState.pc
          (write_frame a (BitVec.ofNat 64 (nodeAddress (d.val+1) 0)) answer)
      have step : a.pc+4=pcAt (passEnd d) := by rw [aPC,pc_succ,ends]
      exact hpc.trans step
    have cmT : Common t := {
      mode := (writeBits_register a _ answer .x5).trans ef.mode
      len := (writeBits_register a _ answer .x11).trans ef.len
      kind := (writeBits_register a _ answer .x13).trans ef.kind
      base := (writeBits_register a _ answer .x18).trans ef.base
      root := (writeBits_register a _ answer .x9).trans ef.root
      scratch := (writeBits_register a _ answer .x24).trans ef.scratch
      stride₁ := (writeBits_register a _ answer .x25).trans ef.stride₁
      stride₂ := (writeBits_register a _ answer .x26).trans ef.stride₂
      stride₃ := (writeBits_register a _ answer .x27).trans ef.stride₃ }
    refine ⟨t,pcT,cmT,closed,?_⟩
    · have all := runs_comp head run
      have cycles : (headerOps d).length+8=passCycles d := by
        rw [cycle,oneCall,one,Nat.mul_one,←cost]
      have callsEq : count d*calls d=1 := by rw [one,oneCall]
      rw [Nat.zero_add] at all
      rw [←cost,←cycles,callsEq]
      exact all
  · by_cases looped : tileSize d≠0
    · obtain ⟨wide,_rem,parts,many,smallTiles,cost,atMain,gateAt,lw3⟩ := loopShape looped
      have aPC : a.pc=pcAt (mainPC d) := by simpa [atMain] using ef.pc
      have x20a : a.getReg .x20=BitVec.ofNat 64 (tiles d) := ef.counter looped
      have startPC : a.pc=pcAt (if tiles d=0 then passEnd d else mainPC d) := by
        simpa [show tiles d≠0 from by omega] using aPC
      obtain ⟨t,tpc,tcm,trows,ttree,trun⟩ :=
        loop_from d o base salt simple looped wide lw3 parts gateAt endLe smallTiles (tiles d) le_rfl a
          startPC (by simpa [Nat.sub_self] using x20a) (by simpa [Nat.sub_self] using ef.ptrSrc simple)
          (by simpa [Nat.sub_self] using ef.ptrDst simple) ef.toCommon treeA (fun _ h => by omega)
      refine ⟨t,tpc,tcm,close_level ttree (by simpa [parts] using trows),?_⟩
      have cycEq : (headerOps d).length+tiles d*(128*(laneWords d+7)+2)=passCycles d := by
        rw [cycle,oneCall,Nat.mul_one,parts,←cost]
        have expand : 128*(laneWords d+7)+2=128*laneWords d+2+7*128 := by rw [Nat.mul_add]
        rw [expand,Nat.mul_add,Nat.mul_left_comm 7 (tiles d) 128]
        omega
      have all := runs_comp head trun
      rw [cost,cycEq,show tiles d*128=count d*calls d by rw [parts,oneCall,Nat.mul_one]] at all
      rw [Nat.zero_add] at all
      exact all
    · have tailH : tileSize d=0 ∧ d.val≠23 := ⟨by simpa using looped, root⟩
      obtain ⟨w240,cap,_pos,cost,atTail,ends,lw3⟩ := tailShape tailH
      have aPC : a.pc=pcAt (tailPC d) := by simpa [atTail] using ef.pc
      have slots : ∀ i, i<count d → PtrSlot (tailPC d+laneWords d*(0+i)) (wireWidth d)
          (decide ((0+i)%2=1)) := by
        intro i hi;simpa using straight_code d simple tailH.1 root i hi
      have room : tailPC d+laneWords d*(0+count d)≤11529 := by
        rw [Nat.zero_add,Nat.mul_comm,ends];exact endLe
      obtain ⟨t,tpc,_x10,_x12,_keep,tcm,ttree,trows,trun⟩ :=
        run_range d o (tailPC d) 0 0 (count d) a base salt simple (Or.inr w240) lw3 (by omega) room
          slots aPC (ef.ptrSrc simple) (ef.ptrDst simple) ef.toCommon treeA (fun _ h => by omega)
      refine ⟨t, by simpa [Nat.zero_add,Nat.mul_comm,ends] using tpc, tcm,
        close_level ttree (by simpa using trows), ?_⟩
      have cycEq : (headerOps d).length+count d*(laneWords d+7)=passCycles d := by
        rw [cycle,oneCall,Nat.mul_one,←cost,Nat.mul_add,Nat.mul_comm (count d) 7]
        omega
      have all := runs_comp head trun
      rw [cost,cycEq,show count d=count d*calls d by rw [oneCall,Nat.mul_one]] at all
      rw [Nat.zero_add] at all
      exact all

end CommitGolfCandidate.Chained.BinaryMachine
