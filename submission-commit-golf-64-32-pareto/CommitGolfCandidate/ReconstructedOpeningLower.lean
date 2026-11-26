import CommitGolfCandidate.ReconstructedOpeningRowEffect
import CommitGolfCandidate.ReconstructedOpeningRowStart24
import CommitGolfCandidate.ReconstructedOpeningRowStart23
import CommitGolfCandidate.ReconstructedOpeningRowStart22
import CommitGolfCandidate.ReconstructedOpeningRowStart21
import CommitGolfCandidate.ReconstructedOpeningRowStart20
import CommitGolfCandidate.ReconstructedOpeningRowStart19
import CommitGolfCandidate.ReconstructedOpeningRowStart18
import CommitGolfCandidate.ReconstructedOpeningRowStart17
import CommitGolfCandidate.ReconstructedOpeningRowStart16
import CommitGolfCandidate.ReconstructedOpeningRowStart15
import CommitGolfCandidate.ReconstructedOpeningRowStart14
import CommitGolfCandidate.ReconstructedOpeningRowStart13
import CommitGolfCandidate.ReconstructedOpeningRowStart12
import CommitGolfCandidate.ReconstructedOpeningRowStart11
import CommitGolfCandidate.ReconstructedOpeningRowStart10

namespace CommitGolfCandidate.Reconstruction.OpeningLower
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningCursor OpeningRowEntry OpeningRowEffect
open CommitBlocks (addr)
set_option maxRecDepth 24000
set_option maxHeartbeats 2200000

def fields (o : Oracle) (k : Generator.Key) (msg : Message) (e : Env) :=
  (List.range 15).flatMap fun j => OpeningRowEffect.fields o k msg e (24-j)

theorem run (o : Oracle) (k : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor)
    (stored : CommitStorage.Stored o k msg trap) (ps : Positions) (nonempty : 0<ps.card) (e : Env)
    (m24 : Model) (fs : List Wire.Field) (h24 : Ready24 e m24) (good24 : Valid e m24 m24 trap ps fs 222)
    (s24 : MachineState) (pc24 : s24.pc=addr 416) (ok24 : Fits s24 m24) :
    ∃ t out n, n≤1350 ∧ CommitExact.Segment o OpeningStraight.image n s24 t ∧ t.pc=addr 130 ∧ Fits t out ∧
      Ready9 e out ∧ Valid e m24 out trap ps (fs++fields o k msg e) 3633 := by
  let m23 := OpeningRowStart24.result e m24
  obtain ⟨s23,n24,bound24,segment24,pc23,ok23⟩ := OpeningRowStart24.run o e m24 h24 good24.stack s24 pc24 ok24
  have h23 := OpeningRowStart24.ready e m24 good24.stack
  let f23 := fs++OpeningRowEffect.fields o k msg e 24
  have good23 : Valid e m24 m23 trap ps f23 462 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m24 m23 fs (24:Fin 25) (by decide) 222 462 (by decide) (by decide) (by decide) good24 (OpeningRowStart24.memory e m24)
  let m22 := OpeningRowStart23.result e m23
  obtain ⟨s22,n23,bound23,segment23,pc22,ok22⟩ := OpeningRowStart23.run o e m23 h23 good23.stack s23 pc23 ok23
  have h22 := OpeningRowStart23.ready e m23 good23.stack
  let f22 := f23++OpeningRowEffect.fields o k msg e 23
  have good22 : Valid e m24 m22 trap ps f22 700 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m23 m22 f23 (23:Fin 25) (by decide) 462 700 (by decide) (by decide) (by decide) good23 (OpeningRowStart23.memory e m23)
  let m21 := OpeningRowStart22.result e m22
  obtain ⟨s21,n22,bound22,segment22,pc21,ok21⟩ := OpeningRowStart22.run o e m22 h22 good22.stack s22 pc22 ok22
  have h21 := OpeningRowStart22.ready e m22 good22.stack
  let f21 := f22++OpeningRowEffect.fields o k msg e 22
  have good21 : Valid e m24 m21 trap ps f21 938 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m22 m21 f22 (22:Fin 25) (by decide) 700 938 (by decide) (by decide) (by decide) good22 (OpeningRowStart22.memory e m22)
  let m20 := OpeningRowStart21.result e m21
  obtain ⟨s20,n21,bound21,segment21,pc20,ok20⟩ := OpeningRowStart21.run o e m21 h21 good21.stack s21 pc21 ok21
  have h20 := OpeningRowStart21.ready e m21 good21.stack
  let f20 := f21++OpeningRowEffect.fields o k msg e 21
  have good20 : Valid e m24 m20 trap ps f20 1176 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m21 m20 f21 (21:Fin 25) (by decide) 938 1176 (by decide) (by decide) (by decide) good21 (OpeningRowStart21.memory e m21)
  let m19 := OpeningRowStart20.result e m20
  obtain ⟨s19,n20,bound20,segment20,pc19,ok19⟩ := OpeningRowStart20.run o e m20 h20 good20.stack s20 pc20 ok20
  have h19 := OpeningRowStart20.ready e m20 good20.stack
  let f19 := f20++OpeningRowEffect.fields o k msg e 20
  have good19 : Valid e m24 m19 trap ps f19 1412 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m20 m19 f20 (20:Fin 25) (by decide) 1176 1412 (by decide) (by decide) (by decide) good20 (OpeningRowStart20.memory e m20)
  let m18 := OpeningRowStart19.result e m19
  obtain ⟨s18,n19,bound19,segment19,pc18,ok18⟩ := OpeningRowStart19.run o e m19 h19 good19.stack s19 pc19 ok19
  have h18 := OpeningRowStart19.ready e m19 good19.stack
  let f18 := f19++OpeningRowEffect.fields o k msg e 19
  have good18 : Valid e m24 m18 trap ps f18 1636 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m19 m18 f19 (19:Fin 25) (by decide) 1412 1636 (by decide) (by decide) (by decide) good19 (OpeningRowStart19.memory e m19)
  let m17 := OpeningRowStart18.result e m18
  obtain ⟨s17,n18,bound18,segment18,pc17,ok17⟩ := OpeningRowStart18.run o e m18 h18 good18.stack s18 pc18 ok18
  have h17 := OpeningRowStart18.ready e m18 good18.stack
  let f17 := f18++OpeningRowEffect.fields o k msg e 18
  have good17 : Valid e m24 m17 trap ps f17 1859 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m18 m17 f18 (18:Fin 25) (by decide) 1636 1859 (by decide) (by decide) (by decide) good18 (OpeningRowStart18.memory e m18)
  let m16 := OpeningRowStart17.result e m17
  obtain ⟨s16,n17,bound17,segment17,pc16,ok16⟩ := OpeningRowStart17.run o e m17 h17 good17.stack s17 pc17 ok17
  have h16 := OpeningRowStart17.ready e m17 good17.stack
  let f16 := f17++OpeningRowEffect.fields o k msg e 17
  have good16 : Valid e m24 m16 trap ps f16 2081 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m17 m16 f17 (17:Fin 25) (by decide) 1859 2081 (by decide) (by decide) (by decide) good17 (OpeningRowStart17.memory e m17)
  let m15 := OpeningRowStart16.result e m16
  obtain ⟨s15,n16,bound16,segment16,pc15,ok15⟩ := OpeningRowStart16.run o e m16 h16 good16.stack s16 pc16 ok16
  have h15 := OpeningRowStart16.ready e m16 good16.stack
  let f15 := f16++OpeningRowEffect.fields o k msg e 16
  have good15 : Valid e m24 m15 trap ps f15 2303 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m16 m15 f16 (16:Fin 25) (by decide) 2081 2303 (by decide) (by decide) (by decide) good16 (OpeningRowStart16.memory e m16)
  let m14 := OpeningRowStart15.result e m15
  obtain ⟨s14,n15,bound15,segment15,pc14,ok14⟩ := OpeningRowStart15.run o e m15 h15 good15.stack s15 pc15 ok15
  have h14 := OpeningRowStart15.ready e m15 good15.stack
  let f14 := f15++OpeningRowEffect.fields o k msg e 15
  have good14 : Valid e m24 m14 trap ps f14 2528 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m15 m14 f15 (15:Fin 25) (by decide) 2303 2528 (by decide) (by decide) (by decide) good15 (OpeningRowStart15.memory e m15)
  let m13 := OpeningRowStart14.result e m14
  obtain ⟨s13,n14,bound14,segment14,pc13,ok13⟩ := OpeningRowStart14.run o e m14 h14 good14.stack s14 pc14 ok14
  have h13 := OpeningRowStart14.ready e m14 good14.stack
  let f13 := f14++OpeningRowEffect.fields o k msg e 14
  have good13 : Valid e m24 m13 trap ps f13 2749 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m14 m13 f14 (14:Fin 25) (by decide) 2528 2749 (by decide) (by decide) (by decide) good14 (OpeningRowStart14.memory e m14)
  let m12 := OpeningRowStart13.result e m13
  obtain ⟨s12,n13,bound13,segment13,pc12,ok12⟩ := OpeningRowStart13.run o e m13 h13 good13.stack s13 pc13 ok13
  have h12 := OpeningRowStart13.ready e m13 good13.stack
  let f12 := f13++OpeningRowEffect.fields o k msg e 13
  have good12 : Valid e m24 m12 trap ps f12 2970 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m13 m12 f13 (13:Fin 25) (by decide) 2749 2970 (by decide) (by decide) (by decide) good13 (OpeningRowStart13.memory e m13)
  let m11 := OpeningRowStart12.result e m12
  obtain ⟨s11,n12,bound12,segment12,pc11,ok11⟩ := OpeningRowStart12.run o e m12 h12 good12.stack s12 pc12 ok12
  have h11 := OpeningRowStart12.ready e m12 good12.stack
  let f11 := f12++OpeningRowEffect.fields o k msg e 12
  have good11 : Valid e m24 m11 trap ps f11 3191 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m12 m11 f12 (12:Fin 25) (by decide) 2970 3191 (by decide) (by decide) (by decide) good12 (OpeningRowStart12.memory e m12)
  let m10 := OpeningRowStart11.result e m11
  obtain ⟨s10,n11,bound11,segment11,pc10,ok10⟩ := OpeningRowStart11.run o e m11 h11 good11.stack s11 pc11 ok11
  have h10 := OpeningRowStart11.ready e m11 good11.stack
  let f10 := f11++OpeningRowEffect.fields o k msg e 11
  have good10 : Valid e m24 m10 trap ps f10 3412 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m11 m10 f11 (11:Fin 25) (by decide) 3191 3412 (by decide) (by decide) (by decide) good11 (OpeningRowStart11.memory e m11)
  let m9 := OpeningRowStart10.result e m10
  obtain ⟨s9,n10,bound10,segment10,pc9,ok9⟩ := OpeningRowStart10.run o e m10 h10 good10.stack s10 pc10 ok10
  have h9 := OpeningRowStart10.ready e m10 good10.stack
  let f9 := f10++OpeningRowEffect.fields o k msg e 10
  have good9 : Valid e m24 m9 trap ps f9 3633 := OpeningRowEffect.advance o k msg trap stored ps nonempty
    e m24 m10 m9 f10 (10:Fin 25) (by decide) 3412 3633 (by decide) (by decide) (by decide) good10 (OpeningRowStart10.memory e m10)
  refine ⟨s9,m9,n24+n23+n22+n21+n20+n19+n18+n17+n16+n15+n14+n13+n12+n11+n10,by omega,(CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose segment24 segment23) segment22) segment21) segment20) segment19) segment18) segment17) segment16) segment15) segment14) segment13) segment12) segment11) segment10),pc9,ok9,h9,?_⟩
  have order : f9=fs++fields o k msg e := by
    simp only [f9,f10,f11,f12,f13,f14,f15,f16,f17,f18,f19,f20,f21,f22,f23,List.append_assoc]
    rfl
  exact order ▸ good9

end CommitGolfCandidate.Reconstruction.OpeningLower
