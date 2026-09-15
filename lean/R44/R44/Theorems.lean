import R44.FiniteModel

namespace R44

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The eight literal child poses are proper and their 56 integer cells are a
    disjoint, exact partition of the doubled seven-cube chair. -/
theorem children_partition_2P : childrenPartitionCheck = true := by
  decide

/-- Refining the 21 internal face contacts once gives 30 states, and one more
    refinement adds no state.  The result is the literal 30-state certificate. -/
theorem contact_closure_30 : contactClosureCheck = true := by
  native_decide

/-- The 30 states induce 372 distinct sign equations.  Their listed twelve
    connected components are balanced, rooted positively at their least roles,
    and ordered by those roots; canonical signs and component magnitudes give
    both independent 192-entry profile literals. -/
theorem profile_canonical : profileCanonicalCheck = true := by
  native_decide

/-- Among all 2,388 disjoint touching shell poses in all 48 signed frames,
    profile compatibility admits exactly the literal 44-pose atlas. -/
theorem atlas_44 : atlasCheck = true := by
  native_decide

/-- Exhaustive exact-cover recursion gives precisely the 33 literal covers of
    the 22-cell shell, and every cover has one candidate parent signature. -/
theorem first_shells_33 : firstShellsCheck = true := by
  native_decide

/-- Of the 32 outer-root shells, exactly 14 have a compatible completion and
    18 have none; every viable completing shell types the centre as central. -/
theorem central_completion : centralCompletionCheck = true := by
  native_decide

/-- Every one of the 28 unordered pairs among the eight parents through a root
    contains an incompatible pair of child poses. -/
theorem parent_conflicts_28 : parentConflictsCheck = true := by
  native_decide

/-- The induced parent census is 697 candidates, 116 disjoint macro-bodies and
    44 admitted contacts; all admitted shifts are even and halving gives the
    fine 44-contact atlas extensionally. -/
theorem parent_atlas_eq_fine : parentAtlasCheck = true := by
  native_decide

/-- The literal complete-feature census has 6,862 poses, of which 5,317 avoid
    the root baseline.  The 5,273 rejection records quantify over every isolated
    companion option (299,975 in all); every selected overlap retains side at
    least 42/400 = 21/200.  The 44 survivors are exactly the registered atlas. -/
theorem mates_census : matesCensusCheck = true := by
  native_decide

/-- For 1 <= i,j <= 12 the base/ridge deviation equation has no solution.  For
    L=3/25, both requested rational inequalities hold after clearing 25^2. -/
theorem deviations_distinct :
    deviationsDistinctCheck = true ∧ lipschitzBoundsCheck = true := by
  decide

/-- Among all 48 signed coordinate permutations, only the identity preserves
    the centres, outward normals and coefficients of the 192-feature table. -/
theorem no_native_symmetry : noNativeSymmetryCheck = true := by
  decide

set_option maxRecDepth 100000 in
/-- The literal table has exactly the 192 roles used by the geometric model. -/
theorem native_features_length : nativeFeatures.length = 192 := by
  decide

set_option maxRecDepth 100000 in
/-- Distinct literal roles have distinct eighth-grid feature centres. -/
theorem native_feature_centers_nodup :
    (nativeFeatures.map Feature.center8).Nodup := by
  set_option maxHeartbeats 1000000 in
  decide

set_option maxRecDepth 100000 in
/-- Every literal panel normal has unit coefficient on its selected axis. -/
theorem native_feature_normal_axis :
    ∀ i : Fin nativeFeatures.length,
      (nativeFeatures.get i).normal.get (featureAxisOf (nativeFeatures.get i)) = 1 ∨
      (nativeFeatures.get i).normal.get (featureAxisOf (nativeFeatures.get i)) = -1 := by
  set_option maxHeartbeats 1000000 in
  decide

/-- The 2,138 literal vertices and 4,272 indexed triangles are a connected,
    closed oriented 6,408-edge surface; it is exactly the panel/feature
    construction triangle-by-triangle and has signed volume seven. -/
theorem solid_mesh_exact : solidMeshCheck = true := by
  native_decide

/-- Every indexed boundary edge has exactly two incident triangles, the
    edge-sharing triangle graph is connected, every vertex link is one cycle,
    and the computed counts satisfy V - E + F = 2138 - 6408 + 4272 = 2.

    The classification theorem for connected closed surfaces therefore makes
    this PL surface a 2-sphere; the PL Schoenflies (Alexander) theorem then
    makes the bounded solid a closed 3-ball.  These classical bridge theorems
    are imported at T3; see E. E. Moise, *Geometric Topology in Dimensions 2
    and 3*, and C. P. Rourke--B. J. Sanderson, *Introduction to Piecewise-Linear
    Topology*. -/
theorem boundary_sphere :
    boundaryEdgeIncidenceCheck = true ∧
    triangleAdjacencyConnectedCheck = true ∧
    vertexLinksSingleCyclesCheck = true ∧
    (List.length Generated.solidVertices10000 = 2138 ∧
      List.length meshUndirectedEdges = 6408 ∧
      List.length Generated.solidTriangles = 4272 ∧
      List.length Generated.solidVertices10000 + List.length Generated.solidTriangles =
        List.length meshUndirectedEdges + 2) := by
  native_decide

/-- The same-frame grandchild occurs at (2,2,2), and the first two nested
    substitution controls have 64/4,096 poses and 448/28,672 disjoint cells. -/
theorem nested_substitution_controls : nestedPatchControlsCheck = true := by
  native_decide

/-- The root double refinement contains all 448 cells `4a+b` of the seven
    four-by-four-by-four blocks, and every signed-permutation lower-corner
    action permutes the 64 offsets in the form required by equivariance. -/
theorem hierarchy_cell_controls : hierarchyCellControlsCheck = true := by
  native_decide

/-- The 192 panel features map onto the 22 shell cells; every legal-contact
    frame is one of the 48 signed permutations; and an exact opposite
    center/normal/coefficient mate owns the cell beyond the root panel. -/
theorem registered_shell_cell_controls : registeredShellCellControlsCheck = true := by
  native_decide

/-- The 19 contact frames generate exactly the literal 24-element proper cubic
    rotation group. -/
theorem orientation_group_24 : orientationGroupCheck = true := by
  native_decide

/-- The cell-labelled R44 chair substitution is a total constant-length
substitution on 168 labels.  Its 168×168 matrix has column sum eight and least
positive power three; its least modular-coincidence depth is three.  The first
lexicographic witness is address `(0,0,2)` and label 78, namely generated frame
11 and local chair cell 1.

Lee--Moody, *Lattice substitution systems and model sets*, Theorem 3,
supplies the external implication from primitive modular coincidence to model
sets; that classification is a cited T3 import, not part of this theorem. -/
theorem substitution_modular_coincidence :
    substitutionTotalWellDefinedCheck = true ∧
    substitutionMatrixDimensionsCheck = true ∧
    substitutionConstantColumnSumCheck = true ∧
    leastPrimitiveExponent = some 3 ∧
    leastModularCoincidenceDepth = some 3 ∧
    substitutionLabels.idxOf (substitutionLabelAt 11 1) = 78 ∧
    modularCoincidenceWitness 3 =
      some (v 0 0 2, substitutionLabelAt 11 1) := by
  native_decide

/-- Closing the legal `2×2×2` block language under all 27 windows of a
substituted block has successive sizes 168, 600, 1,278, 1,398 and 1,410, after
which the language is stable.  Exactly 27 blocks on `{-1,0}³` are fixed by
their eight residue maps.  They form two proper-frame orbits of sizes 24 and
3; 24 seeds have trivial origin stabilizer and three have stabilizer order 8.
Every seed reproduces itself in place, and the cell substitution commutes with
all 24 generated proper frames. -/
theorem seed_language_closure :
    let summary := substitutionSeedLanguageSummary
    summary.closureSizes = [168, 600, 1278, 1398, 1410] ∧
    summary.stable = true ∧
    summary.fixedSeedCount = 27 ∧
    summary.orbitCount = 2 ∧
    hashSetEq summary.orbitSizes [24, 3] = true ∧
    summary.stabilizerHistogram = [(1, 24), (8, 3)] ∧
    summary.inPlaceReproduction = true ∧
    summary.frameCommutation = true := by
  native_decide

/-- Every actual mesh edge has one of the declared flat/carrier/feature
    dihedrals.  The 1,536 feature edges contain 32 copies of each
    (base/ridge, magnitude 1..12, positive/negative side) class with the exact squared-angle
    and edge-length formula. -/
theorem mesh_angle_audit : meshAngleAuditCheck = true := by
  native_decide

end R44
