/- -- [compile-fix: promoted to Proved after exchange 7]
# Discharge attempt: generic_feature_partner — exchange 5

Written sources: A-L2.2 and A-L3.2, proof/ALIGNMENT_PROOF.md.
The frozen proposition is unchanged. -- [compile-fix: exchange 7 proves the
actual nonexceptional boundary classification.] The REAL sector sum is derived in
PolyhedralConeMeasure by volume additivity for the frozen radial cones.
This is an explicit measure-theoretic rendering of the written section
argument, not a redefinition of angle. Cone boundary directions are not lost.

This file does not import MeshSemantics. Its CompleteDihedralList premise
is used verbatim, so the native wedge-volume bridge is not re-admitted here.
The field is discharged by the proved generic-boundary-label bridge. -- [compile-fix]
-/
import R44.Proved.GenericBoundaryLabels -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeSectors
open Set R44.DischargeFeatureGraphs R44.DischargePolyhedral
noncomputable section

/-- Once the actual sector packet is supplied, partner uniqueness follows
from arithmetic and disjoint native role supports. No extra incidence premise. -/
theorem packet_unique_partner (hlist : CompleteDihedralList Q)
    {T : Tiling Q} {g : RigidMotion} {r : Role} {kind : FeatureEdgeKind} {x : E3}
    (p : SectorPacket T g r kind x) :
    HasUniqueGenericPartner Q T g r kind x := by
  classical
  obtain ⟨h,hh,hne,htype,hI⟩ := packet_two_features hlist p
  have hlabel : ∃k s,p.label h=.feature k s := by
    cases he : p.label h with
    | ordinary k => simp [he,SectorLabel.isFeature] at htype
    | feature k s => exact ⟨k,s,rfl⟩ -- [compile-fix]
  obtain ⟨k,s,hlabel⟩ := hlabel
  have hsum := p.angle_sum
  rw [hI,Finset.sum_pair (Ne.symm hne),p.root_label,hlabel] at hsum
    -- API?: Finset.sum_pair requires g ≠ h; it is the sum over {g,h}.
  change featureInteriorAngle r kind+featureInteriorAngle s k=2*Real.pi at hsum
  obtain ⟨hkind,hcoeff⟩ := complementary_feature_angles hlist r s kind k hsum
  subst k
  have hpos := (p.incident_iff h).mp hh
  have hpoint := p.feature_location h hh kind s hlabel
  refine ⟨(h,s),⟨hpos.1,hne,hpoint,hcoeff,?_⟩,?_⟩
  · intro q hq hxq
    have hqi := (p.incident_iff q).mpr ⟨hq,hxq⟩
    simpa [hI] using hqi
  · rintro ⟨q,t⟩ ⟨hq,hqg,hqt,hct,hall⟩
    have hqi := (p.incident_iff q).mpr
      ⟨hq,graph_in_tile q t (generic_subset_graph q t kind hqt)⟩
    have hqh : q=h := (show q=g ∨ q=h by simpa [hI] using hqi).resolve_left hqg
    subst q
    have ht : t=s := by
      by_contra hts
      exact Set.disjoint_left.mp (graph_roles_disjoint h hts)
        (generic_subset_graph h t kind hqt)
        (generic_subset_graph h s kind hpoint)
    exact Prod.ext rfl ht


end
end R44.DischargeSectors

namespace R44
noncomputable section

/-- Exact frozen endpoint; the native boundary labelling chain is
    admission-free. -- [compile-fix] -/
theorem generic_feature_partner_holds :
    ConeSectorBudgets Q → CompleteDihedralList Q → GenericFeaturePartners Q := by
  intro hbudget hdihedral T g hg r
  obtain ⟨D,hD,hcl,hlabels⟩ :=
    DischargeSectors.generic_boundary_labels hbudget hdihedral T g hg r
  refine ⟨D,hD,hcl,?_⟩
  intro kind x hx
  obtain ⟨b⟩ := hlabels kind x hx
  exact DischargeSectors.packet_unique_partner hdihedral
    (b.toSectorPacket hbudget hdihedral)

end
end R44
