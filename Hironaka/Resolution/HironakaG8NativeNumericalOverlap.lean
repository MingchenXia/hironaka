import Hironaka.Resolution.HironakaG8NativeBoundaryComparison
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Resolution.HironakaG11InvCommonMark

/-!
# Numerical agreement on actual full-boundary native overlaps

Use one class-functorial invariant and a common mark on two genuine
ambient windows. The two restricted native records have equal numerical
values at the same actual point of their common cut.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeNumericalOverlap

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport MarkedIdealRestrictOpen
  ResolutionInvariantSpec HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG8NativeBoundaryComparison MaxLocusLocal
  HironakaActualPowerBoundaryExponents HironakaG11InvCommonMark HironakaG8LocalPower
  ResolutionInvariantSegments

variable {n k : ℕ} {X : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]

/-- The comparison of two powered native windows continues along one
literal ambient tower, using both of its actual restricted canonical histories. -/
theorem native_window_values_agree_along (hn : 0 < n)
    (R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k Λ)
    (U V : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U))
    (Q : MarkedIdeal n (CMfd.of (n := n) V)) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (W : Set X) (H : ℕ → ℕ)
    (hSP : NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H)
    (hSQ : NativeHSState Q ((Subtype.val : V → X) ⁻¹' W) H)
    (E : List (Set X)) (hEP : P.E = E.map ((Subtype.val : U → X) ⁻¹' ·))
    (hEQ : Q.E = E.map ((Subtype.val : V → X) ⁻¹' ·))
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) (hd : (powerMarked P e).d = (powerMarked Q f).d)
    (hNot : ∀ D ∈ E, ∀ y : U, y ∈ P.cosupp → y.val ∈ D →
       ¬ ∀ᶠ z in 𝓝 y.val, z ∈ D → z ∈ W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hCanP : IsCanonical (powerMarked P e) (R.toResolutionInvariant.inv (powerMarked P e)) (restrict U T))
    (hCanQ : IsCanonical (powerMarked Q f) (R.toResolutionInvariant.inv (powerMarked Q f)) (restrict V T))
    {z : Y} (hzU : z ∈ openPreimage T U) (hzV : z ∈ openPreimage T V)
    (hzP : (⟨z, hzU⟩ : openPreimage T U) ∈ (geoTransformAlong (powerMarked P e) (restrict U T)).cosupp) :
    (⟨z, hzV⟩ : openPreimage T V) ∈ (geoTransformAlong (powerMarked Q f) (restrict V T)).cosupp ∧
    R.toResolutionInvariant.inv (powerMarked P e) (restrict U T) ⟨z, hzU⟩ =
      R.toResolutionInvariant.inv (powerMarked Q f) (restrict V T) ⟨z, hzV⟩ := by
  let O := U ⊓ V
  let UP := nestedOpens U O
  let VQ := nestedOpens V O
  let p : CMfd.of (n := n) O ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) UP :=
    (nestedOpensDiffeo (n := n) (show O ≤ U from inf_le_left)).symm
  let q : CMfd.of (n := n) O ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) VQ :=
    (nestedOpensDiffeo (n := n) (show O ≤ V from inf_le_right)).symm
  let PU := MarkedIdeal.pullback (Subtype.val : UP → U) P
  let QV := MarkedIdeal.pullback (Subtype.val : VQ → V) Q
  let A := MarkedIdeal.pullback p PU
  let B := MarkedIdeal.pullback q QV
  have hPU : IsInvDomain k PU := InvDomainTowerAlong.isInvDomain_pullback_val UP hP
  have hQV : IsInvDomain k QV := InvDomainTowerAlong.isInvDomain_pullback_val VQ hQ
  have hA : IsInvDomain k A := InvDomainTowerAlong.isInvDomain_pullback p hPU
  have hB : IsInvDomain k B := InvDomainTowerAlong.isInvDomain_pullback q hQV
  have hsPU := hSP.restrict UP
  have hsQV := hSQ.restrict VQ
  have hSA := hsPU.pullback p
  have hSB := hsQV.pullback q
  have hAE : A.E = E.map ((Subtype.val : O → X) ⁻¹' ·) := by
    change (P.E.map ((Subtype.val : UP → U) ⁻¹' ·)).map (p ⁻¹' ·) = _
    simp only [hEP, List.map_map, Function.comp_def]
    rfl
  have hBE : B.E = E.map ((Subtype.val : O → X) ⁻¹' ·) := by
    change (Q.E.map ((Subtype.val : VQ → V) ⁻¹' ·)).map (q ⁻¹' ·) = _
    simp only [hEQ, List.map_map, Function.comp_def]
    rfl
  have hBound : A.E = B.E := hAE.trans hBE.symm
  have hW : p ⁻¹' ((Subtype.val : UP → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' W)) =
      q ⁻¹' ((Subtype.val : VQ → V) ⁻¹' ((Subtype.val : V → X) ⁻¹' W)) := rfl
  have hPCos : PU.cosupp = (Subtype.val : UP → U) ⁻¹' P.cosupp :=
    cosupp_pullback_val P (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg) UP
  have hQCos : QV.cosupp = (Subtype.val : VQ → V) ⁻¹' Q.cosupp :=
    cosupp_pullback_val Q (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hg) VQ
  have hACos : A.cosupp = p ⁻¹' ((Subtype.val : UP → U) ⁻¹' P.cosupp) := by
    rw [show A.cosupp = p ⁻¹' PU.cosupp from cosupp_pullback_eq hPU.isWellFormed.isCoherent, hPCos]
  have hBCos : B.cosupp = q ⁻¹' ((Subtype.val : VQ → V) ⁻¹' Q.cosupp) := by
    rw [show B.cosupp = q ⁻¹' QV.cosupp from cosupp_pullback_eq hQV.isWellFormed.isCoherent, hQCos]
  have hNotO : ∀ D ∈ A.E, ∀ a ∈ A.cosupp, a ∈ D →
      ¬ ∀ᶠ z in 𝓝 a, z ∈ D → z ∈ p ⁻¹' ((Subtype.val : UP → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' W)) := by
    intro D hD a ha haD hNear
    obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.mp (hAE ▸ hD)
    rw [hACos] at ha
    apply hNot D₀ hD₀ (p a).val ha haD
    rw [show (p a).val.val = a.val from rfl, ← O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq a]
    exact Filter.eventually_map.mpr hNear
  obtain ⟨hEq, _, _, hCos, hZero, _⟩ := native_boundary_comparison hn p q PU QV hPU hQV
    hsPU hsQV hW hBound hNotO
  let Pe := powerMarked (X := CMfd.of (n := n) U) P e
  let Qf := powerMarked (X := CMfd.of (n := n) V) Q f
  let PUe := powerMarked (X := CMfd.of (n := n) UP) PU e
  let QVf := powerMarked (X := CMfd.of (n := n) VQ) QV f
  let Ae := powerMarked (X := CMfd.of (n := n) O) A e
  let Bf := powerMarked (X := CMfd.of (n := n) O) B f
  have hPe := powerMarked_isInvDomain P hP he
  have hQf := powerMarked_isInvDomain Q hQ hf
  have hPUe := powerMarked_isInvDomain (X := CMfd.of (n := n) UP) PU hPU he
  have hQVf := powerMarked_isInvDomain (X := CMfd.of (n := n) VQ) QV hQV hf
  have hAe := powerMarked_isInvDomain (X := CMfd.of (n := n) O) A hA he
  have hBf := powerMarked_isInvDomain (X := CMfd.of (n := n) O) B hB hf
  have hPRestr : MarkedIdeal.pullback (Subtype.val : UP → U) Pe = PUe :=
    pullback_powerMarked (X := CMfd.of (n := n) U) (X' := CMfd.of (n := n) UP) contMDiff_subtype_val P hP.isWellFormed.isCoherent e
  have hQRestr : MarkedIdeal.pullback (Subtype.val : VQ → V) Qf = QVf :=
    pullback_powerMarked (X := CMfd.of (n := n) V) (X' := CMfd.of (n := n) VQ) contMDiff_subtype_val Q hQ.isWellFormed.isCoherent f
  have hAPull : MarkedIdeal.pullback p PUe = Ae :=
    pullback_powerMarked p.contMDiff PU hPU.isWellFormed.isCoherent e
  have hBPull : MarkedIdeal.pullback q QVf = Bf :=
    pullback_powerMarked q.contMDiff QV hQV.isWellFormed.isCoherent f
  have hEx : ExpAgree Ae Bf := by
    intro D hD y hy hyD
    rw [show Ae.cosupp = A.cosupp from powerMarked_cosupp (X := CMfd.of (n := n) O) A hA he] at hy
    obtain ⟨hZA, hZB⟩ := hZero D hD y hy hyD
    change DivisorExponentAlong.divExpAlong n A.N (IdealWeightPowers.idealPow A.ideal e) D y =
      DivisorExponentAlong.divExpAlong n B.N (IdealWeightPowers.idealPow B.ideal f) D y
    rw [divExpAlong_idealPow hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent he y,
      divExpAlong_idealPow hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent hf y,
      hZA, hZB, Nat.mul_zero, Nat.mul_zero]
  have hDims : SameCarrierDim Ae Bf :=
    SameCarrierDim.of_N_eq (hSA.2.2.1.trans hSB.2.2.1.symm)
  have hClass : LocWPEquiv Ae Bf := locEquiv_pow rfl hEq hA hB he hf
  let R₀ := R.toResolutionInvariant
  let S := restrict O T
  let TU := restrict U T
  let TV := restrict V T
  let TPS := restrict UP TU
  let TQS := restrict VQ TV
  let χP := (nestedDiffeo (n := n) (openPreimage T U) (openPreimage TU UP) (openPreimage T O)
    (mem_openPreimage_restrict_nestedOpens U O T) (openPreimage_mono T (show O ≤ U from inf_le_left))).symm
  let χQ := (nestedDiffeo (n := n) (openPreimage T V) (openPreimage TV VQ) (openPreimage T O)
    (mem_openPreimage_restrict_nestedOpens V O T) (openPreimage_mono T (show O ≤ V from inf_le_right))).symm
  have hIsoP : IsTowerIso p S TPS χP :=
    (isTowerIso_restrict_nestedOpens (show O ≤ U from inf_le_left) T).symm
  have hIsoQ : IsTowerIso q S TQS χQ :=
    (isTowerIso_restrict_nestedOpens (show O ≤ V from inf_le_right) T).symm
  have hCanPU := Seq.ResolutionInvariantExt.isCanonical_restrict R₀ hPe UP TU hCanP
  have hCanQV := Seq.ResolutionInvariantExt.isCanonical_restrict R₀ hQf VQ TV hCanQ
  rw [hPRestr] at hCanPU
  rw [hQRestr] at hCanQV
  have hCanA := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R₀ hPUe p hIsoP hCanPU
  rw [hAPull] at hCanA
  have hTestP := R₀.isInvValue.isGeoTestTower_of_isCanonical hPe TU hCanP
  have hTestQ := R₀.isInvValue.isGeoTestTower_of_isCanonical hQf TV hCanQ
  have hTestPU := R₀.isInvValue.isGeoTestTower_of_isCanonical hPUe TPS hCanPU
  have hTestQV := R₀.isInvValue.isGeoTestTower_of_isCanonical hQVf TQS hCanQV
  have hTestA := R₀.isInvValue.isGeoTestTower_of_isCanonical hAe S hCanA
  have hCosPU := cosupp_geoTransformAlong_restrict
    hPe.isWellFormed.isClosedSubmanifold_N hPe.isWellFormed.isCoherent UP TU hTestP
  have hCosQV := cosupp_geoTransformAlong_restrict
    hQf.isWellFormed.isClosedSubmanifold_N hQf.isWellFormed.isCoherent VQ TV hTestQ
  rw [hPRestr] at hCosPU
  rw [hQRestr] at hCosQV
  have hCosA := IsTowerIso.cosupp_geoTransformAlong p hPUe.isWellFormed.isClosedSubmanifold_N
    hPUe.isWellFormed.isCoherent hIsoP hTestPU
  have hCosB := IsTowerIso.cosupp_geoTransformAlong q hQVf.isWellFormed.isClosedSubmanifold_N
    hQVf.isWellFormed.isCoherent hIsoQ hTestQV
  rw [hAPull] at hCosA
  rw [hBPull] at hCosB
  let a : openPreimage T O := ⟨z, hzU, hzV⟩
  have hPA : χP a ∈ (geoTransformAlong PUe TPS).cosupp := by
    rw [hCosPU]
    exact hzP
  have ha : a ∈ (geoTransformAlong Ae S).cosupp := by
    rw [hCosA]
    exact hPA
  have hCosAB := ((hClass.wEquiv).2 S).2 hTestA
  have hQB : χQ a ∈ (geoTransformAlong QVf TQS).cosupp := by
    rw [← mem_preimage, ← hCosB, ← hCosAB]
    exact ha
  have hzQ : (⟨z, hzV⟩ : openPreimage T V) ∈ (geoTransformAlong Qf TV).cosupp := by
    rw [hCosQV] at hQB
    exact hQB
  have hVal := R.classFunctorial.inv_eq Ae Bf hAe hBf hClass hd hBound hDims hEx S hCanA a ha
  have hValA := R₀.isInvValue.towerIso p PUe hPUe S TPS χP hIsoP hCanPU a hPA
  have hValB := R₀.isInvValue.towerIso q QVf hQVf S TQS χQ hIsoQ hCanQV a hQB
  have hPVal := R₀.isInvValue.restrictOpen Pe hPe UP TU hCanP (χP a) hzP
  have hQVal := R₀.isInvValue.restrictOpen Qf hQf VQ TV hCanQ (χQ a) hzQ
  rw [hAPull] at hValA
  rw [hBPull] at hValB
  rw [hPRestr] at hPVal
  rw [hQRestr] at hQVal
  exact ⟨hzQ, hPVal.symm.trans (hValA.symm.trans (hVal.trans (hValB.trans hQVal)))⟩

/-- Actual ambient overlap records with a common mark and a full common
boundary have the same initial numerical invariant at their cut points.
The native weighted records are compared through their positive whole powers. -/
theorem native_window_initial_values_agree (hn : 0 < n)
    (R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k Λ)
    (U V : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U))
    (Q : MarkedIdeal n (CMfd.of (n := n) V)) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (W : Set X) (H : ℕ → ℕ)
    (hSP : NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H)
    (hSQ : NativeHSState Q ((Subtype.val : V → X) ⁻¹' W) H)
    (E : List (Set X)) (hEP : P.E = E.map ((Subtype.val : U → X) ⁻¹' ·))
    (hEQ : Q.E = E.map ((Subtype.val : V → X) ⁻¹' ·))
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) (hd : (powerMarked P e).d = (powerMarked Q f).d)
    (hNot : ∀ D ∈ E, ∀ y : U, y ∈ P.cosupp → y.val ∈ D →
       ¬ ∀ᶠ z in 𝓝 y.val, z ∈ D → z ∈ W)
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) (hxP : (⟨x, hxU⟩ : U) ∈ P.cosupp) :
    (⟨x, hxV⟩ : V) ∈ Q.cosupp ∧
    R.toResolutionInvariant.inv (powerMarked P e) .refl ⟨x, hxU⟩ =
      R.toResolutionInvariant.inv (powerMarked Q f) .refl ⟨x, hxV⟩ := by
  have hxPow : (⟨x, hxU⟩ : U) ∈ (powerMarked P e).cosupp :=
    (powerMarked_cosupp P hP he).symm ▸ hxP
  obtain ⟨hxQ, hVal⟩ := native_window_values_agree_along hn R U V P Q hP hQ W H hSP hSQ
    E hEP hEQ e f he hf hd hNot (.refl : BlowupTower X X) trivial trivial hxU hxV hxPow
  exact ⟨powerMarked_cosupp Q hQ hf ▸ hxQ, hVal⟩

end
end Hironaka.HironakaG8NativeNumericalOverlap
