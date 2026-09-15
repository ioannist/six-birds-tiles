/-
# Discharge: carrier_feature_frame_reduction

Written proof: proof/PROOFS_registered.md §6, Native asymmetry, with ERRATA E5.
After the nine carrier planes have been recovered (a separate field), the
bare chair allows only the six coordinate permutations. CarrierSymmetries
proves that elementary step. This file then follows R§6's comparison of
native centers, outward normals and signed heights. Heights are recovered
from membership of the *set-defined* Q on normal lines, not from a presumed
mesh automorphism or an unproved complete-dihedral lemma.

No statement in LogicalSpine is changed. No later hypothesis is used, and
there is no mathematical admission in this file or its dependency chain.
The unlabelled role transport below reads Cartesian chart locations only;
it does not rerun the certified profile/symmetry/mesh checks.

This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.CarrierSymmetries -- [compile-fix]

namespace R44
open Set
open R44.Generated
open R44.DischargeGeometry
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private instance : LawfulBEq V3 where
  eq_of_beq := by
    intro a b h
    rcases a with ⟨ax, ay, az⟩
    rcases b with ⟨bx, byv, bz⟩
    unfold instBEqV3 instBEqV3.beq at h
    simp at h
    simp_all
  rfl := by
    intro a
    rcases a with ⟨ax, ay, az⟩
    unfold instBEqV3 instBEqV3.beq
    simp
private instance : LawfulBEq N3 where
  eq_of_beq := by
    intro a b h
    rcases a with ⟨ax, ay, az⟩
    rcases b with ⟨bx, byv, bz⟩
    unfold instBEqN3 instBEqN3.beq at h
    simp at h
    simp_all
  rfl := by
    intro a
    rcases a with ⟨ax, ay, az⟩
    unfold instBEqN3 instBEqN3.beq
    simp
private instance : LawfulBEq Frame where
  eq_of_beq := by
    intro a b h
    rcases a with ⟨ap, asg⟩
    rcases b with ⟨bp, bsg⟩
    unfold instBEqFrame instBEqFrame.beq at h
    simp at h
    simp_all
  rfl := by
    intro a
    rcases a with ⟨ap, asg⟩
    unfold instBEqFrame instBEqFrame.beq
    simp

private def positiveFrame (p : N3) : Frame := fr p.x p.y p.z 1 1 1

private theorem native_data_get (r : Role) :
    nativeFeatureData r = nativeFeatures[r.val] := by
  have hr : r.val < nativeFeatures.length := by
    rw [native_features_length]; exact r.isLt
  simp [nativeFeatureData, R44.getD, hr]

private theorem native_data_mem (r : Role) : nativeFeatureData r ∈ nativeFeatures := by
  rw [native_data_get]
  exact List.getElem_mem _

private theorem native_data_of_mem {e : Feature} (he : e ∈ nativeFeatures) :
    ∃ r : Role, nativeFeatureData r = e := by
  obtain ⟨i, hi⟩ := List.get_of_mem he -- API?: expected List lemma: e ∈ xs → ∃ i : Fin xs.length, xs.get i = e.
  let r : Role := ⟨i.val, by simpa [native_features_length] using i.isLt⟩
  refine ⟨r, ?_⟩
  rw [native_data_get]
  exact hi

private theorem center8_injective :
    Function.Injective (fun r : Role => (nativeFeatureData r).center8) := by
  intro r s h
  have hr : r.val < nativeFeatures.length := by rw [native_features_length]; exact r.isLt
  have hs : s.val < nativeFeatures.length := by rw [native_features_length]; exact s.isLt
  have hh : (nativeFeatures.map Feature.center8).get ⟨r.val, by simpa using hr⟩ =
      (nativeFeatures.map Feature.center8).get ⟨s.val, by simpa using hs⟩ := by
    change (nativeFeatureData r).center8 = (nativeFeatureData s).center8 at h -- [compile-fix]
    rw [native_data_get r, native_data_get s] at h -- [compile-fix]
    simpa using h
  have hi := native_feature_centers_nodup.injective_get hh
    -- API?: expected Nodup.injective_get: distinct Fin indices have distinct list.get values.
  exact Fin.ext (congrArg Fin.val hi)

/-- Merely a locator in the unlabelled Cartesian chart list. The modulus
makes this a total definition; the lemma below proves the desired location
for all six actual carrier permutations. No coefficient is inspected. -/
private def transportedRole (p : N3) (r : Role) : Role :=
  ⟨((nativeFeatures.findIdx? (fun s =>
      s.center8 == (positiveFrame p).act (nativeFeatureData r).center8)).getD 0) % 192,
    Nat.mod_lt _ (by norm_num)⟩

theorem transported_role_geometry (p : N3) -- [compile-fix]
    (hp : p ∈ coordinatePermutations) (r : Role) :
    (nativeFeatureData (transportedRole p r)).center8 =
      (positiveFrame p).act (nativeFeatureData r).center8 ∧
    (nativeFeatureData (transportedRole p r)).normal =
      (positiveFrame p).act (nativeFeatureData r).normal := by
  native_decide +revert -- [compile-fix]

private theorem perm_int_injective (p : N3) (hp : p ∈ coordinatePermutations) :
    Function.Injective (positiveFrame p).act := by
  intro a b h
  simp [coordinatePermutations] at hp -- [compile-fix]
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    cases a; cases b
    simp [positiveFrame, Frame.act, fr, n3, V3.get, N3.get, v] at h
    rcases h with ⟨hx, hy, hz⟩
    simp_all

private theorem transportedRole_bijective (p : N3) (hp : p ∈ coordinatePermutations) :
    Function.Bijective (transportedRole p) := by
  have hi : Function.Injective (transportedRole p) := by
    intro r s h
    apply center8_injective
    apply perm_int_injective p hp
    rw [← (transported_role_geometry p hp r).1,
      ← (transported_role_geometry p hp s).1, h]
  exact ⟨hi, Finite.surjective_of_injective hi⟩ -- API?: expected finite-type lemma: an injective endomap of a finite type is surjective.

private theorem pure_frame_member (p : N3) (hp : p ∈ coordinatePermutations) :
    positiveFrame p ∈ allFrames := by
  unfold allFrames
  apply List.mem_flatMap.mpr
  refine ⟨p, hp, ?_⟩
  apply List.mem_map.mpr
  exact ⟨v 1 1 1, by simp [signTriples], rfl⟩

private theorem pure_apply {g : RigidMotion} {p : N3}
    (hp : p ∈ coordinatePermutations)
    (hpose : RealizesPose g (po (positiveFrame p) (v 0 0 0)))
    (x : E3) (i : Fin 3) :
    g x i = frameActReal (positiveFrame p) x i := by
  have h := congrArg (fun y : E3 => y i) (g.map_vadd (0 : E3) x)
  simp only [vadd_eq_add, add_zero] at h
  rw [h] -- [compile-fix]
  change (g.linearIsometryEquiv x) i + (g 0) i = _ -- [compile-fix]
  rw [hpose.1 x i, hpose.2 i] -- [compile-fix]
  fin_cases i <;> simp [po, v, V3.get] -- [compile-fix]

private theorem normal_line_transport {g : RigidMotion} {p : N3}
    (hp : p ∈ coordinatePermutations)
    (hpose : RealizesPose g (po (positiveFrame p) (v 0 0 0)))
    (r : Role) (z : ℝ) :
    g (chartPoint r 0 0 z) = chartPoint (transportedRole p r) 0 0 z := by
  have hc := (transported_role_geometry p hp r).1
  have hn := (transported_role_geometry p hp r).2
  apply PiLp.ext
  intro i
  rw [pure_apply hp hpose]
  simp only [chartPoint, zero_smul, add_zero, featureCenter, featureNormal]
  rw [hc, hn]
  simp [coordinatePermutations] at hp -- [compile-fix]
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl) <;> fin_cases i <;>
    simp [positiveFrame, frameActReal, frameCoordinate, scaledV3,
      Frame.act, V3.get, N3.get, fr, n3, v] <;> ring

private theorem normal_line_radius (r : Role) (z : ℝ) :
    featureRadius r (chartPoint r 0 0 z) = 0 := by
  change max |chartU r (chartPoint r 0 0 z)|
    |chartV r (chartPoint r 0 0 z)| = 0
  simp

private theorem normal_line_height (r : Role) (z : ℝ) :
    featureHeight r (chartPoint r 0 0 z) = (profileCoefficient r : ℝ) / 10000 := by
  simp [featureHeight, normal_line_radius]

private theorem normal_line_mem (r : Role) (z : ℝ) (hz : |z| ≤ eta) :
    chartPoint r 0 0 z ∈ Q ↔ z ≤ (profileCoefficient r : ℝ) / 10000 := by
  have ht : featureTubeSupport r (chartPoint r 0 0 z) := by
    constructor
    · rw [normal_line_radius]; norm_num [eta]
    · simpa using hz
  rw [mem_Q_iff_in_tube r _ ht, chartZ_chartPoint, normal_line_height]

private theorem coefficient_height_inside (r : Role) :
    |(profileCoefficient r : ℝ) / 10000| ≤ eta := by
  have h := featureHeight_abs_bound r (chartPoint r 0 0 0)
  rw [normal_line_height] at h
  exact h.trans (by norm_num [eta])

/-- Recover a coefficient by probing the membership threshold on its normal
line. The opposite inequality probes the target height and uses g⁻¹ through
set-image injectivity. This is why Q as a set, not merely its mesh labels,
suffices for the literal signed-height comparison. -/
private theorem transported_role_coefficient {g : RigidMotion} {p : N3}
    (hQ : g '' Q = Q) (hp : p ∈ coordinatePermutations)
    (hpose : RealizesPose g (po (positiveFrame p) (v 0 0 0))) (r : Role) :
    profileCoefficient (transportedRole p r) = profileCoefficient r := by
  let s := transportedRole p r
  have hgmem (x : E3) : g x ∈ Q ↔ x ∈ Q := by
    constructor
    · intro hx
      rw [← hQ] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have heq := g.injective hxy
      simpa [heq] using hy
    · intro hx
      rw [← hQ]
      exact ⟨x, hx, rfl⟩
  have hiff (z : ℝ) : chartPoint r 0 0 z ∈ Q ↔ chartPoint s 0 0 z ∈ Q := by
    rw [← normal_line_transport hp hpose r z]
    exact (hgmem _).symm
  have hr := (normal_line_mem r _ (coefficient_height_inside r)).mpr le_rfl
  have hs := (normal_line_mem s _ (coefficient_height_inside s)).mpr le_rfl
  have hrs := (normal_line_mem s _ (coefficient_height_inside r)).mp
    ((hiff _).mp hr)
  have hsr := (normal_line_mem r _ (coefficient_height_inside s)).mp
    ((hiff _).mpr hs)
  have hreal : (profileCoefficient s : ℝ) = (profileCoefficient r : ℝ) := by
    linarith
  exact_mod_cast hreal

private def movedDatum (f : Frame) (a : Feature) : Feature :=
  {a with center8 := (f.act a.center8).add ((v 0 0 0).smul 8), normal := f.act a.normal}

private theorem datum_transport {g : RigidMotion} {p : N3}
    (hQ : g '' Q = Q) (hp : p ∈ coordinatePermutations)
    (hpose : RealizesPose g (po (positiveFrame p) (v 0 0 0))) (r : Role) :
    sameFeatureDatum (nativeFeatureData (transportedRole p r))
      (movedDatum (positiveFrame p) (nativeFeatureData r)) = true := by
  have hc := (transported_role_geometry p hp r).1
  have hn := (transported_role_geometry p hp r).2
  have ha := transported_role_coefficient hQ hp hpose r
  change (nativeFeatureData (transportedRole p r)).coefficient =
    (nativeFeatureData r).coefficient at ha
  simp [sameFeatureDatum, movedDatum, hc, hn, ha, V3.add, V3.smul, v]

private theorem preserves_table {g : RigidMotion} {p : N3}
    (hQ : g '' Q = Q) (hp : p ∈ coordinatePermutations)
    (hpose : RealizesPose g (po (positiveFrame p) (v 0 0 0))) :
    preservesFeatureTableFrame (positiveFrame p) = true := by
  have hmoved : movedFeatures (po (positiveFrame p) (v 0 0 0)) 8 =
      nativeFeatures.map (movedDatum (positiveFrame p)) := rfl
  unfold preservesFeatureTableFrame featureTablesEqual
  rw [hmoved, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro e he
    obtain ⟨s, rfl⟩ := native_data_of_mem he
    obtain ⟨r, hrs⟩ := (transportedRole_bijective p hp).2 s
    apply List.any_eq_true.mpr -- API?: expected List lemma: any p xs = true ↔ ∃ x ∈ xs, p x = true.
    refine ⟨movedDatum (positiveFrame p) (nativeFeatureData r),
      List.mem_map.mpr ⟨nativeFeatureData r, native_data_mem r, rfl⟩, ?_⟩
    simpa [hrs] using datum_transport hQ hp hpose r
  · apply List.all_eq_true.mpr
    intro e he
    change e ∈ nativeFeatures.map (movedDatum (positiveFrame p)) at he -- [compile-fix]
    obtain ⟨e₀, he₀, heq⟩ := List.mem_map.mp he -- [compile-fix]
    subst e -- [compile-fix]
    obtain ⟨r, hre⟩ := native_data_of_mem he₀ -- [compile-fix]
    subst e₀ -- [compile-fix]
    apply List.any_eq_true.mpr -- API?: expected List lemma: any p xs = true ↔ ∃ x ∈ xs, p x = true.
    refine ⟨nativeFeatureData (transportedRole p r), native_data_mem _, ?_⟩
    have h := datum_transport hQ hp hpose r
    simp only [sameFeatureDatum, Bool.and_eq_true, beq_iff_eq] at h ⊢ -- [compile-fix]
    exact ⟨⟨h.1.1.symm, h.1.2.symm⟩, h.2.symm⟩ -- [compile-fix]

/-- Exact frozen field proposition; it does not presuppose the independent
planar-area recovery field and it does not use the admitted mesh cones. -/
theorem carrier_feature_frame_reduction_holds : CarrierFeatureFrameReduction := by
  intro g hQ hP
  obtain ⟨p, hp, hpose⟩ := carrier_self_isometry_frame hP
  refine ⟨positiveFrame p, ?_, hpose⟩
  apply List.contains_iff_mem.mpr
  exact List.mem_filter.mpr ⟨pure_frame_member p hp, preserves_table hQ hp hpose⟩

end
end R44
