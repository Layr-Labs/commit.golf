import CommitGolfCandidate.S5TailFold
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem plain_cost : ∀ d : Height,¬chained d →
    calls d=1 ∧ 0<count d ∧ 0<remainder d ∧
    (tileSize d=0 → d.val<23 → (headerOps d).length+tailPrefix d (count d)=passSteps d) ∧
    (d.val=23 → tileSize d=0 ∧ tailPC d+laneWords d=passEnd d ∧ (headerOps d).length+laneWords d=passSteps d) ∧
    (0<tileSize d → 0<tiles d ∧ tiles d*tileSize d<count d ∧ d.val<23 ∧
      (headerOps d).length+tilesPrice d (tiles d)+4+(tailPrefix d (count d)-tailPrefix d (mainCount d))=passSteps d) := by decide +kernel

theorem plain_pass (d : Height) (simple : ¬chained d) : StageLaw d := by
  intro o s base salt pc common tree
  let a:=entered s d
  have entry : s.pc=pcAt (pureEntry d) := by simpa only [pureEntry,if_neg simple,Nat.add_zero] using pc
  have header : Runs .commit true o s a (headerOps d).length (headerOps d).length 0:=runs_pure (header_run d s entry)
  obtain ⟨ef,unchanged_⟩:=entered_frame d s entry common
  have selected (w : wireWidth d=238) : a.getReg .x30=heldMask d := by
    rw [show a.getReg .x30=16383 from entered_plain_mask d s common w,heldMask,w];rfl
  have entrySrc : nodeAddress d.val 0=srcAddr d 0 := by simpa [srcAddr] using row_base d.val 0
  have state:=transfer_tree tree unchanged_
  have empty : doneRows o.compression base d.val 0 a := fun _ hi=>by omega
  obtain ⟨single,size,rempos,smallCost,rootCost,mainCost⟩:=plain_cost d simple
  have cycle:=phase_counts d
  by_cases small : tileSize d=0
  · have b : cursorBias d=0:=by simp [cursorBias,small]
    have startPC : a.pc=pcAt (tailPC d) :=by simpa [bodyEntry,small] using ef.pc
    have src : a.getReg .x21=BitVec.ofNat 64 (srcAddr d 0) :=by simpa [b,entrySrc] using ef.src
    have dst : a.getReg .x22=BitVec.ofNat 64 (dstAddr d 0) :=by simpa [b,dstAddr] using ef.dst
    by_cases root : d.val=23
    · have one : count d=1:=by unfold count levelCount;rw [root];rfl
      have end_:=rootCost root
      have addr : Addr a d 0 0 0 := ⟨by rw [src];exact BitVec.add_zero _,by rw [dst];exact BitVec.add_zero _⟩
      obtain ⟨range,x,y,call,cut,narrow⟩:=tail_table d simple rempos
      have noMask : mask240 d=false := (by decide +kernel : ∀ h : Height,h.val=23 → mask240 h=false) d root
      let t:=plainResult o.compression d 0 a 0 0
      have run := plain_observed o addr ef.toCommon size simple (tailPC d) startPC
        (decoded_site (by omega) x) (decoded_site (by omega) y) (decoded_site range call)
        (fun ok => False.elim (by rw [noMask] at ok;contradiction)) ((by decide +kernel : ∀ h : Height,tailPC h+5<18492) d) narrow
      have eff:=plain_effect o.compression addr state.pads size simple selected
      have all:=runs_comp header run
      have cm : Common t := by
        obtain ⟨q1,q2,q3,q4,q5,q6,q7,q8,q9⟩:=ef.toCommon
        constructor <;> apply (plain_keeps o.compression d 0 a 0 0 _ (by decide) (by decide) (by decide)).trans <;> assumption
      refine ⟨t,?_,cm,close_level (node_frame state eff size) (one ▸ grow_row state empty eff size),?_⟩
      · rw [show t.pc=_ from plain_pc o.compression d 0 a 0 0 simple]
        rw [startPC,←end_.2.1,pcAt,pcAt,←BitVec.ofNat_add];congr 1 <;> omega
      · rw [single,one,Nat.mul_one,show passCycles d=passSteps d+7 by rw [cycle,single,one],←end_.2.2]
        convert all using 1 <;> omega
    · have lower : d.val<23:=by have :=d.isLt;omega
      have ctr : TailFrame d 0 a :=
        ⟨ef.toCommon,selected,startPC.trans (by rw [if_pos size]),src,dst,
          by simpa [small,remainder] using ef.counter lower,by simpa using ef.parity small lower⟩
      obtain ⟨t,last,tree',rows,run⟩:=tail_lanes o d (count d) 0 a base salt ctr simple lower rempos (by omega) state empty
      simp only [Nat.zero_add,tailPrefix,Nat.zero_mul,Nat.zero_div,Nat.add_zero,Nat.sub_zero] at run ⊢
      have final : TailFrame d (count d) t := by simpa using last
      refine ⟨t,final.pc.trans (by rw [if_neg (Nat.lt_irrefl _)]),final.toCommon,close_level tree' (by simpa using rows),?_⟩
      have all:=runs_comp header run
      rw [cycle,single,Nat.mul_one,←smallCost small lower]
      convert all using 1 <;> simp [tailPrefix] <;> omega
  · have used : 0<tileSize d:=by omega
    obtain ⟨many,extra,inner,formula⟩:=mainCost used
    have b : cursorBias d=2048:=by simp [cursorBias,simple,small]
    have frame : Boundary d 0 (tiles d) a :=
      ⟨ef.toCommon,selected,by simpa [bodyEntry,small,many] using ef.pc,
       by simpa [entrySrc,b,BitVec.ofNat_add] using ef.src,by simpa [dstAddr,b,BitVec.ofNat_add] using ef.dst,
       by simpa [small] using ef.counter inner⟩
    obtain ⟨u,last,tree',built,r₁⟩:=many_tiles o d (tiles d) 0 a base salt simple used (by decide) (by omega) frame state empty
    simp only [Nat.zero_add,show tiles d*tileSize d=mainCount d from rfl] at last built r₁
    obtain ⟨ready,mem,r₂⟩:=rebase o simple used last
    obtain ⟨t,tail,fin,all,r₃⟩:=tail_lanes o d (remainder d) (mainCount d) _ base salt ready simple inner rempos (parts d).le
      (transfer_tree tree' mem) (transfer_rows built mem)
    rw [parts] at tail all r₃
    refine ⟨t,tail.pc.trans (by rw [if_neg (Nat.lt_irrefl _)]),tail.toCommon,close_level fin all,?_⟩
    have run:=runs_comp (runs_comp (runs_comp header r₁) r₂) r₃
    rw [cycle,single,Nat.mul_one,←formula];have total:=parts d
    convert run using 1 <;> omega
end CommitGolfCandidate.S5Machine
