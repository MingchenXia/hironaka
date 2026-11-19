import Hironaka.Resolution.HironakaG11HistoryDenseEscape

set_option autoImplicit false

/-! Density away from a closed obstacle survives literal strict transforms
through an arbitrary blowup history; no avoidance of the centres is needed. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11UnrestrictedDenseEscape
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal BoundaryCount DivisorExponentAlong
  GermIdealOrder HironakaG11InvBMLower HironakaG8SuccExponents MemberInterTowerAlong

noncomputable section

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- A centre-relative strict transform preserves density off a closed obstacle. -/
theorem geoStrictTransform_dense_off {C A H : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hH : IsClosed H)
    (hDense : A ⊆ closure (A \ H)) :
    geoStrictTransform π C A ⊆
      closure (geoStrictTransform π C A \ geoStrictTransform π C H) := by
  refine closure_minimal ?_ isClosed_closure
  rintro y ⟨hyA, hyC⟩
  rw [mem_closure_iff_nhds]
  intro V hV
  have hyE : y ∉ exceptionalLocus n π := fun he =>
    hyC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ he)
  have himg : π '' V ∈ 𝓝 (π y) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hπ.contMDiff hyE]
    exact image_mem_map hV
  have hnear : π '' V ∩ Cᶜ ∈ 𝓝 (π y) :=
    inter_mem himg (hπ.1.1.isOpen_compl.mem_nhds hyC)
  obtain ⟨x, ⟨⟨w, hwV, rfl⟩, hwC⟩, hwA, hwH⟩ :=
    mem_closure_iff_nhds.mp (hDense hyA) _ hnear
  exact ⟨w, hwV, subset_closure ⟨hwA, hwC⟩,
    fun hw => hwH (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hH hw)⟩

/-- Density survives any finite literal strict-transform history. -/
theorem strictAlong_dense_off (A H : Set X) (hH : IsClosed H)
    (hDense : A ⊆ closure (A \ H)) (T : BlowupTower X Y) :
    strictAlong T A ⊆ closure (strictAlong T A \ strictAlong T H) := by
  induction T with
  | refl => simpa [strictAlong] using hDense
  | @step Z W T C π hπ ih =>
      change geoStrictTransform π C (strictAlong T A) ⊆
        closure (geoStrictTransform π C (strictAlong T A) \ geoStrictTransform π C (strictAlong T H))
      exact geoStrictTransform_dense_off hπ (isClosed_strictAlong T hH) ih

/-- A dense escaping born trace rules out exceptional-term divisibility on
any later test history, with no avoidance hypothesis. -/
theorem not_isDivNearAlong_exceptionalTerm_of_history
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (i : Fin M.E.length)
    (H : Set X) (hH : IsClosed H)
    (hDense : M.N ∩ M.E.get i ⊆ closure ((M.N ∩ M.E.get i) \ H))
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {S : List (Set Y)} (hS : ∀ K ∈ S, IsClosed K)
    (hmem : strictAlong T H ∈ S) (e : ℕ) {y : Y}
    (hy : y ∈ (geoTransformAlong M T).N ∩ strictAlong T (M.E.get i)) :
    ¬ IsDivNearAlong n (geoTransformAlong M T).N (exceptionalTermBM (n := n) S e)
      (strictAlong T (M.E.get i)) 1 y := by
  classical
  have htrace : strictAlong T (M.N ∩ M.E.get i) =
      (geoTransformAlong M T).N ∩ strictAlong T (M.E.get i) := by
    simpa [BoundaryCount.memberInter] using
      (strictAlong_inter_memberInter M hM ({i} : Finset (Fin M.E.length)) T hT)
  have hdense := strictAlong_dense_off (M.N ∩ M.E.get i) H hH hDense T
  rw [htrace] at hdense
  have hcl := hdense hy
  intro hdiv
  obtain ⟨q, hqdiv, ⟨⟨hqN, hqD⟩, hqH⟩⟩ := (mem_closure_iff_nhds.mp hcl) _ hdiv
  have hqCos := hqdiv hqN hqD
  exact hqH (mem_of_mem_cosupport_one_exceptionalTermBM (Y := Y) (S := S) (e := e) hS hqCos _ hmem)

end
end Hironaka.HironakaG11UnrestrictedDenseEscape
