/- -- [compile-fix]
# Native marked-panel incidence, independent of profiles

A§1, A-L6.1--A-L6.2, R§8--9; ERRATA E2 and E6. A marker tube meets only
its two incident grid cells. The eight offsets are covariant under every
cubic frame. Consequently any different registered carrier meeting a tube
has a native marker at exactly that site. This is a geometric statement
about the literal unit panels, not an additional atlas enumeration.

Only coordinate metadata (seven cells, six face directions, eight offsets)
is reduced here. The signed profile and the contact census are consumed
through their existing theorems in PairedCollarMaps. No admission.
-/
import R44.Proved.TubeSiteGeometry -- [compile-fix: promoted dependency]

namespace R44.DischargePanels
open Set Generated DischargeGeometry DischargeSites DischargeCells
open DischargePyramid DischargeRegistered DischargeCollision
open scoped R44.DischargeCollision
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem v3_eq_iff (a b : V3) :
    a=b ↔ a.x=b.x ∧ a.y=b.y ∧ a.z=b.z := by
  cases a; cases b; simp

private theorem v3_eq (a b : V3) (hx : a.x=b.x) (hy : a.y=b.y)
    (hz : a.z=b.z) : a=b := by
  cases a; cases b; simp_all -- [compile-fix]

private theorem v3_get_add (a b : V3) (i : Nat) :
    (a.add b).get i=a.get i+b.get i := by
  rcases i with _|i
  · rfl
  · rcases i with _|i
    · rfl
    · rfl -- [compile-fix]

private theorem v3_add_shuffle {A B C D : V3} (h : A.add C=D) :
    (A.add B).add C=D.add B := by
  rcases A with ⟨ax,ay,az⟩
  rcases B with ⟨bx,byv,bz⟩
  rcases C with ⟨cx,cy,cz⟩
  rcases D with ⟨dx,dy,dz⟩
  rw [v3_eq_iff] at h ⊢
  simp [V3.add,v] at h ⊢
  omega -- [compile-fix]

private theorem cellCenter_injective : Function.Injective cellCenter := by
  intro a b h
  rcases a with ⟨ax,ay,az⟩
  rcases b with ⟨bx,byv,bz⟩
  have hx := congrArg (fun z : E3 => z 0) h
  have hy := congrArg (fun z : E3 => z 1) h
  have hz := congrArg (fun z : E3 => z 2) h
  simp [cellCenter,V3.get] at hx hy hz
  simp_all -- [compile-fix]

def nearCell (r : Role) : V3 :=
  (featureFarCell (nativeFeatureData r)).sub (nativeFeatureData r).normal

def farCell (r : Role) : V3 := featureFarCell (nativeFeatureData r)

def faceCenter8 (a b : V3) : V3 := ((a.add b).add (v 1 1 1)).smul 4

/-- An unlabelled eight-port pattern on a directed unit-cell face. The
normal sign does not alter the pattern: the eight offsets are D4-invariant. -/
def MarkedFace (a b c : V3) : Prop :=
  ∃ i : Fin 3, ∃ s : Int, (s=1 ∨ s= -1) ∧
    b=a.add (unitAxis i s) ∧
    ∃ o∈offsets8, c=(faceCenter8 a b).add (tangentOffset i.val o)

private theorem native_panel_metadata (r : Role) :
    nearCell r∈chairCells ∧ farCell r∉chairCells ∧
    MarkedFace (nearCell r) (farCell r) (nativeFeatureData r).center8 := by
  let panelAxis (s : Role) : Fin 3 :=
    ⟨featureAxis s % 3, Nat.mod_lt _ (by norm_num)⟩
  let panelSign (s : Role) : Int :=
    (nativeFeatureData s).normal.get (panelAxis s)
  let panelOffset (s : Role) : V3 :=
    R44.getD offsets8 (s.val % 8) (v 0 0 0)
  have raw : ∀ s : Role,
      nearCell s∈chairCells ∧ farCell s∉chairCells ∧
      (panelSign s=1 ∨ panelSign s= -1) ∧
      farCell s=(nearCell s).add (unitAxis (panelAxis s) (panelSign s)) ∧
      panelOffset s∈offsets8 ∧
      (nativeFeatureData s).center8=
        (faceCenter8 (nearCell s) (farCell s)).add
          (tangentOffset (panelAxis s).val (panelOffset s)) := by
    decide -- [compile-fix: kernel reduction suffices for the explicit finite witness table]
  rcases raw r with ⟨hn,hf,hs,hfar,ho,hc⟩
  exact ⟨hn,hf,panelAxis r,panelSign r,hs,hfar,panelOffset r,ho,hc⟩
  -- [compile-fix: computable witnesses for the identical finite metadata proposition]

 theorem near_mem (r : Role) : nearCell r∈chairCells :=
  (native_panel_metadata r).1
 theorem far_not_mem (r : Role) : farCell r∉chairCells :=
  (native_panel_metadata r).2.1
 theorem native_marked (r : Role) :
    MarkedFace (nearCell r) (farCell r) (nativeFeatureData r).center8 :=
  (native_panel_metadata r).2.2

 theorem marked_reverse {a b c : V3} (h : MarkedFace a b c) :
    MarkedFace b a c := by
  obtain ⟨i,s,hs,hb,o,ho,hc⟩ := h
  refine ⟨i,-s,?_,?_,o,ho,?_⟩
  · rcases hs with rfl|rfl <;> simp
  · subst b
    fin_cases i <;> simp [v3_eq_iff,V3.add,unitAxis,V3.get,v] <;> ring
    -- [compile-fix]
  · rw [hc]
    congr 1
    apply v3_eq <;> simp [faceCenter8,V3.add,V3.smul,v] <;> ring -- [compile-fix]

private theorem frame_act_add (f : Frame) (a b : V3) :
    f.act (a.add b)=(f.act a).add (f.act b) := by
  rcases f with ⟨⟨px,py,pz⟩,⟨sx,sy,sz⟩⟩
  apply v3_eq
  · change sx*(a.add b).get px=sx*a.get px+sx*b.get px
    rw [v3_get_add]; ring
  · change sy*(a.add b).get py=sy*a.get py+sy*b.get py
    rw [v3_get_add]; ring
  · change sz*(a.add b).get pz=sz*a.get pz+sz*b.get pz
    rw [v3_get_add]; ring -- [compile-fix]

private theorem cellLower_add_local (f : Frame) (hf : f∈allFrames)
    (t a b : V3) :
    cellLower f t (a.add b)=(cellLower f t a).add (f.act b) := by
  unfold allFrames at hf
  obtain ⟨perm,hperm,hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨sign,hsign,rfl⟩ := List.mem_map.mp hf -- [compile-fix]
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl|rfl|rfl|rfl|rfl|rfl) <;>
    rcases hsign with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
    rcases t with ⟨tx,ty,tz⟩ <;> rcases a with ⟨ax,ay,az⟩ <;>
    rcases b with ⟨bx,byv,bz⟩ <;>
    apply v3_eq <;>
    simp [cellLower,Frame.act,V3.add,N3.get,V3.get,fr,n3,v] <;> ring

private theorem faceCenter8_image {f : Frame} (hf : f∈allFrames)
    (t a : V3) (i : Fin 3) (s : Int) (hs : s=1∨s= -1) :
    (f.act (faceCenter8 a (a.add (unitAxis i s)))).add (t.smul 8)=
      faceCenter8 (cellLower f t a)
        (cellLower f t (a.add (unitAxis i s))) := by
  unfold allFrames at hf
  obtain ⟨perm,hperm,hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨sign,hsign,rfl⟩ := List.mem_map.mp hf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl|rfl|rfl|rfl|rfl|rfl) <;>
    rcases hsign with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
    fin_cases i <;> rcases hs with rfl|rfl <;>
    rcases a with ⟨ax,ay,az⟩ <;> rcases t with ⟨tx,ty,tz⟩ <;>
    apply v3_eq <;>
    simp [faceCenter8,cellLower,Frame.act,unitAxis,V3.add,V3.smul,
      V3.get,N3.get,fr,n3,v] <;> ring -- [compile-fix]

private def markedTransformCheck : Bool :=
  allFrames.all fun f => (List.finRange 3).all fun i =>
    ([1,-1] : List Int).all fun s => offsets8.all fun o =>
      (List.finRange 3).any fun j => ([1,-1] : List Int).any fun u =>
        offsets8.any fun q =>
          f.act (unitAxis i s)==unitAxis j u &&
            f.act (tangentOffset i.val o)==tangentOffset j.val q

private theorem marked_transform {f : Frame} (hf : f∈allFrames)
    (i : Fin 3) (s : Int) (hs : s=1∨s= -1) (o : V3) (ho : o∈offsets8) :
    ∃ j : Fin 3, ∃ u : Int, (u=1∨u= -1) ∧
      f.act (unitAxis i s)=unitAxis j u ∧
      ∃ q∈offsets8,
        f.act (tangentOffset i.val o)=tangentOffset j.val q := by
  have hc : markedTransformCheck=true := by decide
  have hcf := List.all_eq_true.mp hc f hf
  have hci := List.all_eq_true.mp hcf i (List.mem_finRange i)
  have hslist : s∈([1,-1] : List Int) := by rcases hs with rfl|rfl <;> simp
  have hcs := List.all_eq_true.mp hci s hslist
  have hco := List.all_eq_true.mp hcs o ho
  obtain ⟨j,-,hcj⟩ := List.any_eq_true.mp hco
  obtain ⟨u,hu,hcu⟩ := List.any_eq_true.mp hcj
  obtain ⟨q,hq,hcq⟩ := List.any_eq_true.mp hcu
  simp only [Bool.and_eq_true] at hcq
  have hu' : u=1∨u= -1 := by simpa using hu
  exact ⟨j,u,hu',by simpa using hcq.1,q,hq,by simpa using hcq.2⟩
  -- [compile-fix: kernel-evaluated finite transform table; identical proposition]

/-- Covariance of the unlabelled pattern, including the lower-corner
correction on reflected coordinates. The variable shifts are NOT bounded. -/
theorem marked_image {p : Pose} (hp : p.frame∈allFrames)
    {a b c : V3} (h : MarkedFace a b c) :
    MarkedFace (cellLower p.frame p.shift a) (cellLower p.frame p.shift b)
      ((p.frame.act c).add (p.shift.smul 8)) := by
  obtain ⟨i,s,hs,hb,o,ho,hc⟩ := h
  obtain ⟨j,u,hu,hunit,q,hq,htan⟩ := marked_transform hp i s hs o ho
  refine ⟨j,u,hu,?_,q,hq,?_⟩
  · rw [hb,cellLower_add_local p.frame hp,hunit]
  · rw [hc,frame_act_add,htan]
    have hface := faceCenter8_image hp p.shift a i s hs
    rw [←hb] at hface -- [compile-fix]
    let A := p.frame.act (faceCenter8 a b)
    let B := tangentOffset j.val q
    let C := p.shift.smul 8
    let D := faceCenter8 (cellLower p.frame p.shift a)
      (cellLower p.frame p.shift b)
    change A.add C=D at hface
    change (A.add B).add C=D.add B
    exact v3_add_shuffle hface -- [compile-fix]
  -- [compile-fix: factored finite frame covariance; identical proposition]

private def roleAt (c : V3) : Role :=
  ⟨((nativeFeatures.findIdx? (fun f => f.center8==c)).getD 0)%192,
    Nat.mod_lt _ (by norm_num)⟩

private def exposedMarkLocatorCheck : Bool := -- [compile-fix begin: kernel locator replaces the unavailable delivered lookup proof]
  chairCells.all fun a => (List.finRange 3).all fun i =>
    ([1,-1] : List Int).all fun s => offsets8.all fun o =>
      let b := a.add (unitAxis i s)
      let c := (faceCenter8 a b).add (tangentOffset i.val o)
      if chairCells.contains b then true else
        let r := roleAt c
        nearCell r==a && farCell r==b && (nativeFeatureData r).center8==c &&
          (nativeFeatureData r).normal==b.sub a

/-- Every exposed chair face with an unlabelled marker has the corresponding
native role. The proof reads panel locations, never their coefficients. -/
theorem exposed_mark_locator {a b c : V3} (ha : a∈chairCells)
    (hb : b∉chairCells) (h : MarkedFace a b c) :
    ∃ r : Role, nearCell r=a ∧ farCell r=b ∧
      (nativeFeatureData r).center8=c ∧ (nativeFeatureData r).normal=b.sub a := by
  obtain ⟨i,s,hs,rfl,o,ho,rfl⟩ := h
  have hc : exposedMarkLocatorCheck=true := by decide
  have hca := List.all_eq_true.mp hc a ha
  have hci := List.all_eq_true.mp hca i (List.mem_finRange i)
  have hslist : s∈([1,-1] : List Int) := by rcases hs with rfl|rfl <;> simp
  have hcs := List.all_eq_true.mp hci s hslist
  have hco := List.all_eq_true.mp hcs o ho
  have hcontains : chairCells.contains (a.add (unitAxis i s))=false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact hb (List.contains_iff_mem.mp ht)
  simp [hcontains,Bool.and_eq_true] at hco -- [compile-fix]
  rcases hco with hmem|⟨⟨⟨hn,hf⟩,hc⟩,hnorm⟩
  · exact False.elim (hb hmem)
  refine ⟨roleAt ((faceCenter8 a (a.add (unitAxis i s))).add
    (tangentOffset i.val o)),?_,?_,?_,?_⟩
  · exact hn
  · exact hf
  · exact hc
  · exact hnorm -- [compile-fix end]
  -- [compile-fix: kernel-evaluated exposed-face table; identical proposition]

/-- A point of a closed tube belongs to no closed grid cube except its two
incident cubes. Tangential margins are strict, including on the tube boundary. -/
private abbrev tangentCoordData (r : Role) (i : Nat) : Prop :=
  (nearCell r).get i=(farCell r).get i ∧
    2≤(nativeFeatureData r).center8.get i-8*(nearCell r).get i ∧
    (nativeFeatureData r).center8.get i-8*(nearCell r).get i≤6

private abbrev normalCoordData (r : Role) (i : Nat) : Prop :=
  let k := (nativeFeatureData r).center8.get i/8
  (nativeFeatureData r).center8.get i=8*k ∧
    (((nearCell r).get i=k-1 ∧ (farCell r).get i=k) ∨
      ((nearCell r).get i=k ∧ (farCell r).get i=k-1))

private theorem native_coordinate_data : ∀r : Role,
    (normalCoordData r 0 ∧ tangentCoordData r 1 ∧ tangentCoordData r 2) ∨
    (tangentCoordData r 0 ∧ normalCoordData r 1 ∧ tangentCoordData r 2) ∨
    (tangentCoordData r 0 ∧ tangentCoordData r 1 ∧ normalCoordData r 2) := by
  decide -- [compile-fix: finite native coordinate table]

theorem tube_cell_incidence (r : Role) (a : V3) {x : E3}
    (hx : featureTubeSupport r x) (ha : x∈unitCube a) :
    a=nearCell r ∨ a=farCell r := by
  have hcoord := featureTubeSupport_coordinate_bound hx -- [compile-fix]
  have integer_bound (n k : Int) (z c : ℝ)
      (hz : (n:ℝ)≤z ∧ z≤n+1) (hc : |z-c|≤(1:ℝ)/100)
      (hk : (k:ℝ)+1/5≤c ∧ c≤(k:ℝ)+4/5) : n=k := by
    have hzc := abs_le.mp hc
    have hlow : (k:ℝ)<(n:ℝ)+1 := by linarith
    have hhigh : (n:ℝ)<(k:ℝ)+1 := by linarith
    have hl : k<n+1 := by exact_mod_cast hlow
    have hh : n<k+1 := by exact_mod_cast hhigh
    omega
  have integer_plane (n k : Int) (z : ℝ)
      (hz : (n:ℝ)≤z ∧ z≤n+1) (hc : |z-k|≤(1:ℝ)/100) :
      n=k-1 ∨ n=k := by
    have hzc := abs_le.mp hc
    have hlr : (k:ℝ)<(n:ℝ)+2 := by linarith
    have hhr : (n:ℝ)<(k:ℝ)+1 := by linarith
    have hl : k<n+2 := by exact_mod_cast hlr
    have hh : n<k+1 := by exact_mod_cast hhr
    omega
  have tangent_fix (i : Fin 3) (hd : tangentCoordData r i) :
      a.get i=(nearCell r).get i := by
    apply integer_bound (a.get i) ((nearCell r).get i) (x i)
      (featureCenter r i) (ha i) (hcoord i)
    unfold tangentCoordData at hd
    have hlo : (2:ℝ)≤((nativeFeatureData r).center8.get i:ℝ)-
        8*((nearCell r).get i:ℝ) := by exact_mod_cast hd.2.1
    have hhi : ((nativeFeatureData r).center8.get i:ℝ)-
        8*((nearCell r).get i:ℝ)≤6 := by exact_mod_cast hd.2.2
    change ((nearCell r).get i:ℝ)+1/5≤
        ((nativeFeatureData r).center8.get i:ℝ)/8 ∧
      ((nativeFeatureData r).center8.get i:ℝ)/8≤
        ((nearCell r).get i:ℝ)+4/5
    constructor <;> linarith
  have normal_choice (i : Fin 3) (hd : normalCoordData r i) :
      a.get i=(nearCell r).get i ∨ a.get i=(farCell r).get i := by
    let k := (nativeFeatureData r).center8.get i/8
    unfold normalCoordData at hd
    have hcenter : featureCenter r i=(k:ℝ) := by
      change ((nativeFeatureData r).center8.get i:ℝ)/8=(k:ℝ)
      have he : ((nativeFeatureData r).center8.get i:ℝ)=8*(k:ℝ) := by
        exact_mod_cast hd.1
      linarith
    have hp := integer_plane (a.get i) k (x i) (ha i)
      (by simpa [eta,hcenter] using hcoord i)
    rcases hd.2 with hnf|hnf
    · rcases hp with hp|hp
      · left; omega
      · right; omega
    · rcases hp with hp|hp
      · right; omega
      · left; omega
  rcases native_coordinate_data r with h0|h1|h2
  · have hn := normal_choice 0 h0.1
    have ht1 := tangent_fix 1 h0.2.1
    have ht2 := tangent_fix 2 h0.2.2
    rcases hn with hn|hn
    · left; apply v3_eq
      · simpa [V3.get] using hn
      · simpa [V3.get] using ht1
      · simpa [V3.get] using ht2
    · right; apply v3_eq
      · simpa [V3.get] using hn
      · exact_mod_cast ht1.trans h0.2.1.1
      · exact_mod_cast ht2.trans h0.2.2.1
  · have ht0 := tangent_fix 0 h1.1
    have hn := normal_choice 1 h1.2.1
    have ht2 := tangent_fix 2 h1.2.2
    rcases hn with hn|hn
    · left; apply v3_eq
      · simpa [V3.get] using ht0
      · simpa [V3.get] using hn
      · simpa [V3.get] using ht2
    · right; apply v3_eq
      · exact_mod_cast ht0.trans h1.1.1
      · simpa [V3.get] using hn
      · exact_mod_cast ht2.trans h1.2.2.1
  · have ht0 := tangent_fix 0 h2.1
    have ht1 := tangent_fix 1 h2.2.1
    have hn := normal_choice 2 h2.2.2
    rcases hn with hn|hn
    · left; apply v3_eq
      · simpa [V3.get] using ht0
      · simpa [V3.get] using ht1
      · simpa [V3.get] using hn
    · right; apply v3_eq
      · exact_mod_cast ht0.trans h2.1.1
      · exact_mod_cast ht1.trans h2.2.1.1
      · simpa [V3.get] using hn
  -- [compile-fix: factor the identical coordinate argument through finite role data]

/-- Two different baseline tiles cannot own the same cell. -/
theorem packed_cells_disjoint {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p)
    (hd : Disjoint (interior P) (interior (m '' P))) :
    ∀a∈chairCells,a∉body p := by
  intro a ha hap
  have hroot : cellCenter a∈interior P := by -- [compile-fix]
    apply interior_mono (s := unitCube a)
    · intro x hx
      exact ⟨a,ha,hx⟩
    · exact cellCenter_mem_interior_unitCube a
  have hinc : unitCube a⊆m '' P := by
    intro x hx
    rw [placed_carrier_cells hp hm]
    exact ⟨a,hap,hx⟩
  exact Set.disjoint_left.mp hd hroot
    (interior_mono hinc (cellCenter_mem_interior_unitCube a))

/-- If another packed integral carrier touches the tube, it owns its far cell. -/
theorem tube_meets_far {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p)
    (hd : Disjoint (interior P) (interior (m '' P))) (r : Role)
    {x : E3} (hx : featureTubeSupport r x) (hxP : x∈m '' P) :
    farCell r∈body p := by
  rw [placed_carrier_cells hp hm] at hxP
  obtain ⟨a,ha,hxa⟩ := hxP
  rcases tube_cell_incidence r a hx hxa with he|he
  · exact False.elim ((packed_cells_disjoint hp hm hd _ (near_mem r)) (he ▸ ha))
  · exact he ▸ ha

/-- Geometric (unlabelled) port mate supplied by whole-cell ownership. -/
theorem far_owner_has_role {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p)
    (hd : Disjoint (interior P) (interior (m '' P))) (r : Role)
    (hfar : farCell r∈body p) :
    ∃s : Role, m (featureCenter s)=featureCenter r ∧
      m.linearIsometryEquiv (featureNormal s)= -featureNormal r := by
  have hi := inverse_realizes hp hm
  have hpi := frame_transpose_member p.frame hp
  let a := cellLower p.inverse.frame p.inverse.shift (farCell r)
  let b := cellLower p.inverse.frame p.inverse.shift (nearCell r)
  have hcell (c : V3) :
      cellLower p.inverse.frame p.inverse.shift (cellLower p.frame p.shift c)=c := by
    have he := congrArg m.symm (realized_cellCenter hp hm (d:=c))
    rw [m.symm_apply_apply] at he -- [compile-fix]
    have he2 := realized_cellCenter hpi hi
      (d:=cellLower p.frame p.shift c)
    exact cellCenter_injective (he.trans he2).symm -- [compile-fix]
  have ha : a∈chairCells := by
    obtain ⟨c,hc,he⟩ := by
      simpa only [body,List.mem_eraseDups,List.mem_map] using hfar
    simpa [a,←he,hcell] using hc
  have hb : b∉chairCells := by
    intro hb
    have hback := realized_cellCenter hpi hi (d:=nearCell r)
    have hfw := realized_cellCenter hp hm (d:=b)
    have hsame : cellLower p.frame p.shift b=nearCell r := by -- [compile-fix begin: recover the cell from centre injectivity]
      have he : m (cellCenter b)=cellCenter (nearCell r) := by
        simpa [b] using congrArg m hback.symm
      rw [hfw] at he
      exact cellCenter_injective he -- [compile-fix end]
    exact packed_cells_disjoint hp hm hd _ (near_mem r)
      (by
        simp only [body,List.mem_eraseDups,List.mem_map]
        exact ⟨b,hb,hsame⟩) -- [compile-fix]
  have hmark := marked_image (p:=p.inverse) hpi
    (marked_reverse (native_marked r)) -- [compile-fix]
  obtain ⟨s,hsnear,hsfar,hsc,hsn⟩ := exposed_mark_locator ha hb hmark
  refine ⟨s,?_,?_⟩
  · have hc := placed_center hpi hi r
    have hs : featureCenter s=m.symm (featureCenter r) := by
      rw [featureCenter,hsc]
      exact hc.symm
    simp [hs]
  · have norm_disp (t : Role) : -- [compile-fix begin: express the transported normal through cell-centre displacement]
        featureNormal t=cellCenter (farCell t)-cellCenter (nearCell t) := by
      ext i
      fin_cases i <;>
      simp [featureNormal,nearCell,farCell,cellCenter,scaledV3,V3.sub,V3.get,v]
    rw [norm_disp s,hsnear,hsfar]
    change m.linearIsometryEquiv (cellCenter b -ᵥ cellCenter a)=_
    rw [m.map_vsub]
    simp only [vsub_eq_sub]
    have hn := realized_cellCenter hpi hi (d:=nearCell r)
    have hf := realized_cellCenter hpi hi (d:=farCell r)
    have hn' : m (cellCenter b)=cellCenter (nearCell r) := by
      simpa [b] using (congrArg m hn).symm
    have hf' : m (cellCenter a)=cellCenter (farCell r) := by
      simpa [a] using (congrArg m hf).symm
    rw [hn',hf',norm_disp]
    abel -- [compile-fix end]

end
end R44.DischargePanels
