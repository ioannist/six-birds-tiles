/- -- [compile-fix]
# Discharge: companion_pose_discrete

Written source: proof/ALIGNMENT_PROOF.md A-C4.4 (after A-L4.3, ERRATA E1)
and its exact correspondence with the complete-feature census, A-FS5.2.
The frozen proposition is copied verbatim. The whole-feature geometric
implication is proved, including centers, normals, cubic frames and eighth
shifts. MateCensusSemantics interprets the already certified pair-set
equality and projects it to poses, with the literal record-nonemptiness
side condition stated explicitly. No mesh or generic-stratification admission
is imported. There are no mathematical admissions in this dependency chain.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.MateCensusSemantics -- [compile-fix]

namespace R44
noncomputable section

theorem companion_pose_discrete_holds :
    profileCanonicalCheck = true → matesCensusCheck = true →
      FeatureContainmentRigidity Q → CompanionPoseDiscrete Q := by
  intro hprofile hcensus _hrigid
  refine ⟨DischargeMateCensus.formula_set_eq_census hprofile hcensus,?_⟩
  intro T g h hg hh hne r s hm
  exact DischargePyramid.tiling_complete_mate_formula T g h hg hh hne r s hm

end
end R44
