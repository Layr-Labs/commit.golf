import CommitGolfCandidate.ReconstructedOpeningLowerAddress
import CommitGolfCandidate.ReconstructedOpeningNodeStream
import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRowEntry
open CommitGolf RiscvZkvm.Rv64 OpeningCursor OpeningHeaderAddress OpeningWordFields
open LeafModel OpeningPut

theorem equalModel (m t : Model) (regs : ∀ r, m.reg r=t.reg r) (mem : m.mem=t.mem) : m=t := by
  cases m;cases t;congr 1;exact funext regs

structure Env where
  index : Index
  cursor : Nat
  count : Word
  room : (cursor+3633)/64<capacity

structure Stack (e : Env) (m : TwoPermutationPrototype.Memory) : Prop where
  stack1856 : m 8589934262=W 281474976710655
  stack1848 : m 8589934261=W 70368744177663
  stack1840 : m 8589934260=W 17592186044415
  stack1832 : m 8589934259=W 8589934591
  stack1872 : m 8589934264=W 4294967295
  stack1864 : m 8589934263=W 2147483647
  stack1816 : m 8589934257=W 1073741823
  stack1808 : m 8589934256=W 536870911
  stack1800 : m 8589934255=W 2051
  stack1928 : m 8589934271=e.count
  stack1912 : m 8589934269=basePtr e.index 10
  stack1904 : m 8589934268=basePtr e.index 11
  stack1896 : m 8589934267=basePtr e.index 12
  stack1888 : m 8589934266=basePtr e.index 13
  stack1880 : m 8589934265=basePtr e.index 14

theorem keepStack (e : Env) (m t : TwoPermutationPrototype.Memory) (h : Stack e m)
    (same : ∀ w, 8589934200<w → t w=m w) : Stack e t := by
  constructor
  · rw [same 8589934262 (by decide)];exact h.stack1856
  · rw [same 8589934261 (by decide)];exact h.stack1848
  · rw [same 8589934260 (by decide)];exact h.stack1840
  · rw [same 8589934259 (by decide)];exact h.stack1832
  · rw [same 8589934264 (by decide)];exact h.stack1872
  · rw [same 8589934263 (by decide)];exact h.stack1864
  · rw [same 8589934257 (by decide)];exact h.stack1816
  · rw [same 8589934256 (by decide)];exact h.stack1808
  · rw [same 8589934255 (by decide)];exact h.stack1800
  · rw [same 8589934271 (by decide)];exact h.stack1928
  · rw [same 8589934269 (by decide)];exact h.stack1912
  · rw [same 8589934268 (by decide)];exact h.stack1904
  · rw [same 8589934267 (by decide)];exact h.stack1896
  · rw [same 8589934266 (by decide)];exact h.stack1888
  · rw [same 8589934265 (by decide)];exact h.stack1880

structure Ready24 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W e.cursor
  r28 : m.reg .x28=basePtr e.index 19
  r26 : m.reg .x26=basePtr e.index 18
  r20 : m.reg .x20=basePtr e.index 17
  r27 : m.reg .x27=basePtr e.index 16
  r15 : m.reg .x15=basePtr e.index 15

structure Ready23 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W e.cursor
  r28 : m.reg .x28=basePtr e.index 19
  r26 : m.reg .x26=basePtr e.index 18
  r20 : m.reg .x20=basePtr e.index 17
  r27 : m.reg .x27=basePtr e.index 16
  r15 : m.reg .x15=basePtr e.index 15

structure Ready22 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W e.cursor
  r28 : m.reg .x28=basePtr e.index 19
  r26 : m.reg .x26=basePtr e.index 18
  r20 : m.reg .x20=basePtr e.index 17
  r27 : m.reg .x27=basePtr e.index 16
  r15 : m.reg .x15=basePtr e.index 15

structure Ready21 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W e.cursor
  r28 : m.reg .x28=basePtr e.index 19
  r26 : m.reg .x26=basePtr e.index 18
  r20 : m.reg .x20=basePtr e.index 17
  r27 : m.reg .x27=basePtr e.index 16
  r15 : m.reg .x15=basePtr e.index 15

structure Ready20 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W e.cursor
  r28 : m.reg .x28=basePtr e.index 19
  r26 : m.reg .x26=basePtr e.index 18
  r20 : m.reg .x20=basePtr e.index 17
  r27 : m.reg .x27=basePtr e.index 16
  r15 : m.reg .x15=basePtr e.index 15

structure Ready19 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W e.cursor
  r28 : m.reg .x28=basePtr e.index 19
  r26 : m.reg .x26=basePtr e.index 18
  r20 : m.reg .x20=basePtr e.index 17
  r27 : m.reg .x27=basePtr e.index 16
  r15 : m.reg .x15=basePtr e.index 15

structure Ready18 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W e.cursor
  r26 : m.reg .x26=basePtr e.index 18
  r20 : m.reg .x20=basePtr e.index 17
  r27 : m.reg .x27=basePtr e.index 16
  r15 : m.reg .x15=basePtr e.index 15
  r31 : m.reg .x31=W 2051

structure Ready17 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W e.cursor
  r20 : m.reg .x20=basePtr e.index 17
  r27 : m.reg .x27=basePtr e.index 16
  r15 : m.reg .x15=basePtr e.index 15
  r31 : m.reg .x31=W 2051

structure Ready16 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r20 : m.reg .x20=W (e.cursor+2051)
  r27 : m.reg .x27=basePtr e.index 16
  r15 : m.reg .x15=basePtr e.index 15
  r31 : m.reg .x31=W 2051
  r30 : m.reg .x30=W 1073741823

structure Ready15 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W 36
  r20 : m.reg .x20=W (e.cursor+2051)
  r15 : m.reg .x15=basePtr e.index 15
  r31 : m.reg .x31=W 2051

structure Ready14 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W 36
  r20 : m.reg .x20=W (e.cursor+2051)
  r31 : m.reg .x31=W 2051
  r6 : m.reg .x6=W 536870911

structure Ready13 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W 36
  r20 : m.reg .x20=W (e.cursor+2051)
  r31 : m.reg .x31=W 2051
  r6 : m.reg .x6=W 536870911

structure Ready12 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W 36
  r20 : m.reg .x20=W (e.cursor+2051)
  r31 : m.reg .x31=W 2051
  r6 : m.reg .x6=W 536870911

structure Ready11 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W 36
  r20 : m.reg .x20=W (e.cursor+2051)
  r31 : m.reg .x31=W 2051
  r6 : m.reg .x6=W 536870911

structure Ready10 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W 36
  r20 : m.reg .x20=W (e.cursor+2051)
  r31 : m.reg .x31=W 2051
  r6 : m.reg .x6=W 536870911

structure Ready9 (e : Env) (m : Model) : Prop where
  r0 : m.reg .x0=W 0
  r2 : m.reg .x2=W 68719474016
  r8 : m.reg .x8=W 68719476336
  r9 : m.reg .x9=W 70368744177663
  r18 : m.reg .x18=W 64
  r22 : m.reg .x22=W 4294971424
  r25 : m.reg .x25=W 10334769248
  r10 : m.reg .x10=W (2^24+e.index.val)
  r7 : m.reg .x7=W 36
  r20 : m.reg .x20=W (e.cursor+2051)
  r31 : m.reg .x31=W 2051
  r6 : m.reg .x6=W 68719474176
  r14 : m.reg .x14=e.count

end CommitGolfCandidate.Reconstruction.OpeningRowEntry
