import CommitGolfCandidate.PairRecordFrame
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 30000
attribute [local irreducible] readBuffer storedAt prefixNode lowerHash

theorem finishInvariant (o : Oracle) (input : CheckInput) (n : Nat) (hn : n<128)
    (m : MachineState) (h : HashedFrame o input n m) (fresh : Bool) (passed : TailOK o input n m fresh)
    (tab : ∀ v, storedAt m v=prefixNode o.compression input n v)
    (consistent : ∀ r<n, ∀ u : Fin 256, openingIndex input.positions r/65536=u.val →
      prefixNode o.compression input n u=some (lowerHash o.compression input r))
    (high : ∀ w : Word,32768≤w.toNat → w.toNat%8=0 → w.toNat+8≤MEMORY_BYTES → m.getMem w=(Late.submission.initialState .check input).getMem w)
    (gap : ∀ p : Fin 128,readBuffer m (16384+96*p.val+64) 32=0) :
    RecordInvariant o.compression input (n+1) (finishRow fresh m) := by
  let u := rowBucket input n
  have ix : openingIndex input.positions n/65536=u.val := rfl
  have reg := postRegs o input n hn m h fresh (flagDecide fresh _ passed.flag) passed.agrees
  have agree (v : Fin 256) (idx : openingIndex input.positions n/65536=v.val) (d : Digest)
      (old : prefixNode o.compression input n v=some d) : d=lowerHash o.compression input n := by
    have uv : u=v := Fin.ext (ix.symm.trans idx)
    subst v
    have mem := (tab u).trans old
    exact priorAgrees fresh passed.prior mem
  refine recordFrom _ input (n+1) (by omega) (finishRow fresh m) reg ?_
    (extendConsistent _ input n consistent agree) ?_ ?_
  · intro v
    apply rowProperty m fresh (fun t=>storedAt t v=prefixNode o.compression input (n+1) v)
    · intro fst
      have prior : storedAt m u=none := whenFresh passed.prior fst
      rw [copiedMap m h.pc u v h.index h.scratch,h.digest,tab v,prefixFresh _ input n u ix ((tab u).symm.trans prior) v]
    · intro dup
      have prior : storedAt m u=some (lowerHash o.compression input n) := whenSeen passed.prior dup
      exact (mapCongr (compared m) m (comparedMem m h.pc u h.index) v).trans
        ((tab v).trans (prefixSeen _ input n u ix _ ((tab u).symm.trans prior) v).symm)
  · intro w hw al hb
    exact rowProperty m fresh (fun t=>t.getMem w=(Late.submission.initialState .check input).getMem w)
      (fun _=>(copyHigh m h.pc u h.index w hw).trans (high w hw al hb))
      (fun _=>(wordAfter (s:=m) (t:=compared m) (comparedMem m h.pc u h.index) w).trans (high w hw al hb))
  · intro p
    let a:=16384+96*p.val+64
    exact rowProperty m fresh (fun t=>readBuffer t a 32=0)
      (fun _=>(copyGap m h.pc u h.index p).trans (gap p))
      (fun _=>(read_buffer_memory_congr (compared m) m (comparedMem m h.pc u h.index) a 32).trans (gap p))

end CommitGolfCandidate.PairCap.Batch
