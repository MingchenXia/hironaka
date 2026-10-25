import DeJongAlterations.Geometry.ProperSteinProjectiveCechShiftedPresentation
import DeJongAlterations.Geometry.ProperSteinProjectiveCechModuleLocalization
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubsetLocalization

/-! # Actual localization of finite shifted free modules

The comparison uses the actual localized coordinate projections and actual
localized coefficient insertions. Both inverse identities retain the native
localization quotient and allow localization torsion.
-/

/-!
Adapted from the same workspace `BingWangEntropy/FiniteShiftedModuleLocalization.lean`,
SHA256 5f6f98b6c0da909cb2906b94c2845711751c61691b21624ba2fdaeaab19b3f6b.
Only native Mathlib and owned DeJongAlterations modules are imported.
-/

universe u

open DirectSum

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section FiniteFreeLocalization

variable {R I : Type u} [CommRing R] [Fintype I] [DecidableEq I]
  (S : Submonoid R)

/-- The actual coefficient projections of the actual localized finite free module. -/
def actualLocalizedFiniteFreeCoefficients :
    LocalizedModule S (I → R) →ₗ[R] (I → LocalizedModule S R) :=
  LinearMap.pi fun i => actualLocalizedModuleMap S (LinearMap.proj i)

/-- The actual assembly of a finite family of actual localized coefficients. -/
def actualLocalizedFiniteFreeAssemble :
    (I → LocalizedModule S R) →ₗ[R] LocalizedModule S (I → R) :=
  ∑ i : I, (actualLocalizedModuleMap S (LinearMap.single R (fun _ : I => R) i)).comp
    (LinearMap.proj i)

/-- Reassembling the true localized coefficients restores the true localized vector. -/
theorem actualLocalizedFiniteFreeAssemble_coefficients
    (z : LocalizedModule S (I → R)) :
    actualLocalizedFiniteFreeAssemble S (actualLocalizedFiniteFreeCoefficients S z) = z := by
  induction z using LocalizedModule.induction_on with
  | h a s =>
    simp only [actualLocalizedFiniteFreeAssemble, actualLocalizedFiniteFreeCoefficients,
      LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.pi_apply, actualLocalizedModuleMap_mk, LinearMap.single_apply]
    let q : (I → R) →ₗ[R] LocalizedModule S (I → R) :=
      (LocalizedModule.divBy s).comp (LocalizedModule.mkLinearMap S (I → R))
    have hq (a : I → R) : q a = LocalizedModule.mk a s := by
      simp [q, LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk]
    simp_rw [← hq]
    rw [← map_sum, Finset.univ_sum_single]

/-- Projecting a true assembled localized vector restores every true localized coefficient. -/
theorem actualLocalizedFiniteFreeCoefficients_assemble
    (a : I → LocalizedModule S R) :
    actualLocalizedFiniteFreeCoefficients S (actualLocalizedFiniteFreeAssemble S a) = a := by
  funext i
  simp only [actualLocalizedFiniteFreeCoefficients, actualLocalizedFiniteFreeAssemble,
    LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  change actualLocalizedModuleMap S (LinearMap.proj i)
    (∑ j : I, actualLocalizedModuleMap S (LinearMap.single R (fun _ : I => R) j) (a j)) = a i
  rw [map_sum]
  have h (j : I) : actualLocalizedModuleMap S (LinearMap.proj i)
      (actualLocalizedModuleMap S (LinearMap.single R (fun _ : I => R) j) (a j)) =
        if i = j then a j else 0 := by
    induction a j using LocalizedModule.induction_on with
    | h r s =>
      rw [actualLocalizedModuleMap_mk, actualLocalizedModuleMap_mk]
      by_cases hij : i = j
      · subst j
        simp [LinearMap.single_apply]
      · simp [LinearMap.single_apply, hij]
  simp_rw [h]
  simp

/-- The actual localization of a finite free module is the true finite product of actual ring localizations. -/
def actualLocalizedFiniteFreeEquiv :
    LocalizedModule S (I → R) ≃ₗ[R] (I → LocalizedModule S R) :=
  { actualLocalizedFiniteFreeCoefficients S with
    invFun := actualLocalizedFiniteFreeAssemble S
    left_inv := actualLocalizedFiniteFreeAssemble_coefficients S
    right_inv := actualLocalizedFiniteFreeCoefficients_assemble S }

end FiniteFreeLocalization

section ShiftedDegreeLocalization

variable {K R I : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype I] [DecidableEq I]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜] (δ : I → ℤ)
  (x : R) (d : ℤ) (hx : x ∈ 𝒜 d) (k : ℤ)

/-- Project a true localized shifted homogeneous vector to its true shifted ring coefficient. -/
def finiteShiftedLocalizedCoefficient (i : I) :
    localizedHomogeneousModulePiece 𝒜 (finiteShiftedFreePiece 𝒜 δ) x d hx k →ₗ[K]
      localizedHomogeneousModulePiece 𝒜 𝒜 x d hx (k - δ i) :=
  (((actualLocalizedModuleMap (Submonoid.powers x) (LinearMap.proj i)).restrictScalars K).comp
    (localizedHomogeneousModulePiece 𝒜 (finiteShiftedFreePiece 𝒜 δ) x d hx k).subtype).codRestrict _
      (by
        intro z
        obtain ⟨n, a, ha, he⟩ := z.property
        refine ⟨n, a i, ?_, ?_⟩
        · convert ha i using 1
          congr 1
          ring
        · change LocalizedModule.mk (a i) (homogeneousPowerDenominator x n) =
            actualLocalizedModuleMap (Submonoid.powers x) (LinearMap.proj i) z.val
          rw [← he, actualLocalizedModuleMap_mk]
          rfl)

/-- Insert a true localized shifted ring coefficient into its true finite shifted homogeneous vector. -/
def finiteShiftedLocalizedInsert (i : I) :
    localizedHomogeneousModulePiece 𝒜 𝒜 x d hx (k - δ i) →ₗ[K]
      localizedHomogeneousModulePiece 𝒜 (finiteShiftedFreePiece 𝒜 δ) x d hx k :=
  (((actualLocalizedModuleMap (Submonoid.powers x)
    (LinearMap.single R (fun _ : I => R) i)).restrictScalars K).comp
      (localizedHomogeneousModulePiece 𝒜 𝒜 x d hx (k - δ i)).subtype).codRestrict _
        (by
          intro z
          obtain ⟨n, a, ha, he⟩ := z.property
          refine ⟨n, Pi.single i a, ?_, ?_⟩
          · intro j
            by_cases hji : j = i
            · subst j
              simp only [Pi.single_eq_same]
              convert ha using 1
              congr 1
              ring
            · simpa only [Pi.single_eq_of_ne hji] using (𝒜 (k + (n : ℤ) * d - δ j)).zero_mem
          · change LocalizedModule.mk (Pi.single i a) (homogeneousPowerDenominator x n) =
              actualLocalizedModuleMap (Submonoid.powers x)
                (LinearMap.single R (fun _ : I => R) i) z.val
            rw [← he, actualLocalizedModuleMap_mk]
            rfl)

/-- All actual shifted homogeneous localized coefficients, as a true finite product. -/
def finiteShiftedLocalizedCoefficients :
    localizedHomogeneousModulePiece 𝒜 (finiteShiftedFreePiece 𝒜 δ) x d hx k →ₗ[K]
      (∀ i, localizedHomogeneousModulePiece 𝒜 𝒜 x d hx (k - δ i)) :=
  LinearMap.pi fun i => finiteShiftedLocalizedCoefficient 𝒜 δ x d hx k i

/-- Assemble all actual shifted homogeneous localized coefficients. -/
def finiteShiftedLocalizedAssemble :
    (∀ i, localizedHomogeneousModulePiece 𝒜 𝒜 x d hx (k - δ i)) →ₗ[K]
      localizedHomogeneousModulePiece 𝒜 (finiteShiftedFreePiece 𝒜 δ) x d hx k :=
  ∑ i : I, (finiteShiftedLocalizedInsert 𝒜 δ x d hx k i).comp (LinearMap.proj i)

/-- True homogeneous assembly is the restriction of true unrestricted localized assembly. -/
theorem finiteShiftedLocalizedAssemble_val
    (a : ∀ i, localizedHomogeneousModulePiece 𝒜 𝒜 x d hx (k - δ i)) :
    (finiteShiftedLocalizedAssemble 𝒜 δ x d hx k a).val =
      actualLocalizedFiniteFreeAssemble (Submonoid.powers x) (fun i => (a i).val) := by
  simp only [finiteShiftedLocalizedAssemble, actualLocalizedFiniteFreeAssemble,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_sum]
  rfl

/-- Homogeneous assembly restores the true localized shifted homogeneous vector. -/
theorem finiteShiftedLocalizedAssemble_coefficients
    (z : localizedHomogeneousModulePiece 𝒜 (finiteShiftedFreePiece 𝒜 δ) x d hx k) :
    finiteShiftedLocalizedAssemble 𝒜 δ x d hx k
      (finiteShiftedLocalizedCoefficients 𝒜 δ x d hx k z) = z := by
  apply Subtype.ext
  rw [finiteShiftedLocalizedAssemble_val]
  change actualLocalizedFiniteFreeAssemble (Submonoid.powers x)
    (actualLocalizedFiniteFreeCoefficients (Submonoid.powers x) z.val) = z.val
  exact actualLocalizedFiniteFreeAssemble_coefficients _ _

/-- True coefficient projection restores each assembled shifted homogeneous localized coefficient. -/
theorem finiteShiftedLocalizedCoefficients_assemble
    (a : ∀ i, localizedHomogeneousModulePiece 𝒜 𝒜 x d hx (k - δ i)) :
    finiteShiftedLocalizedCoefficients 𝒜 δ x d hx k
      (finiteShiftedLocalizedAssemble 𝒜 δ x d hx k a) = a := by
  funext i
  apply Subtype.ext
  change actualLocalizedModuleMap (Submonoid.powers x) (LinearMap.proj i)
    (finiteShiftedLocalizedAssemble 𝒜 δ x d hx k a).val = (a i).val
  rw [finiteShiftedLocalizedAssemble_val]
  exact congrFun (actualLocalizedFiniteFreeCoefficients_assemble (Submonoid.powers x)
    (fun i => (a i).val)) i

/-- The actual localized degree of a true finite shifted free module is the true finite product
of actual localized ring degrees shifted by the actual generator degrees. -/
def finiteShiftedLocalizedEquiv :
    localizedHomogeneousModulePiece 𝒜 (finiteShiftedFreePiece 𝒜 δ) x d hx k ≃ₗ[K]
      (∀ i, localizedHomogeneousModulePiece 𝒜 𝒜 x d hx (k - δ i)) :=
  { finiteShiftedLocalizedCoefficients 𝒜 δ x d hx k with
    invFun := finiteShiftedLocalizedAssemble 𝒜 δ x d hx k
    left_inv := finiteShiftedLocalizedAssemble_coefficients 𝒜 δ x d hx k
    right_inv := finiteShiftedLocalizedCoefficients_assemble 𝒜 δ x d hx k }

end ShiftedDegreeLocalization

section CoordinateNaturality

open CategoryTheory

variable {K R I J : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype I] [DecidableEq I] [LinearOrder J]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜] (δ : I → ℤ)
  (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

omit [Fintype I] [DecidableEq I] in
/-- Actual localized coefficient projections commute with every actual coordinate-subset restriction. -/
theorem finiteShiftedLocalizedCoefficient_subsetRestriction
    {S T : Finset J} (hST : S ⊆ T) (k : ℤ) (i : I)
    (z : localizedHomogeneousModulePiece 𝒜 (finiteShiftedFreePiece 𝒜 δ)
      (homogeneousCoordinateSubsetProduct x S) (S.card : ℤ)
      (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k) :
    finiteShiftedLocalizedCoefficient 𝒜 δ (homogeneousCoordinateSubsetProduct x T)
      (T.card : ℤ) (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx T) k i
      (homogeneousCoordinateSubsetRestriction 𝒜 (finiteShiftedFreePiece 𝒜 δ) x hx hST k z) =
    homogeneousCoordinateSubsetRestriction 𝒜 𝒜 x hx hST (k - δ i)
      (finiteShiftedLocalizedCoefficient 𝒜 δ (homogeneousCoordinateSubsetProduct x S)
        (S.card : ℤ) (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k i z) := by
  apply Subtype.ext
  change actualLocalizedModuleMap (Submonoid.powers (homogeneousCoordinateSubsetProduct x T))
    (LinearMap.proj i)
    (actualLocalizedModuleDivisorRestriction (M := I → R)
      (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x T)
      (homogeneousCoordinateSubsetProduct_dvd x hST) z.val) =
    actualLocalizedModuleDivisorRestriction (M := R)
      (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x T)
      (homogeneousCoordinateSubsetProduct_dvd x hST)
      (actualLocalizedModuleMap (Submonoid.powers (homogeneousCoordinateSubsetProduct x S))
        (LinearMap.proj i) z.val)
  exact (LinearMap.congr_fun (actualLocalizedModuleDivisorRestriction_map
    (LinearMap.proj i) _ _ (homogeneousCoordinateSubsetProduct_dvd x hST)) z.val).symm

end CoordinateNaturality

section DiagramProducts

open CategoryTheory

variable {K I J : Type u} [CommRing K]

/-- The actual pointwise module product of actual coordinate-subset diagrams. -/
def actualModuleSubsetDiagramPi (F : I → Finset J ⥤ ModuleCat.{u} K) :
    Finset J ⥤ ModuleCat.{u} K where
  obj S := ModuleCat.of K (∀ i, F i |>.obj S)
  map f := ModuleCat.ofHom (LinearMap.pi fun i => ((F i |>.map f).hom).comp (LinearMap.proj i))
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext i
    change (F i).map (𝟙 S) (a i) = a i
    rw [(F i).map_id S]
    rfl
  map_comp {S T U} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext i
    change (F i).map (f ≫ g) (a i) = (F i).map g ((F i).map f (a i))
    rw [(F i).map_comp f g]
    rfl

end DiagramProducts

section ShiftedDiagramComparison

open CategoryTheory

variable {K R I J : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype I] [DecidableEq I] [LinearOrder J]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜] (δ : I → ℤ)
  (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

/-- The native coordinate diagram of a finite shifted free module is naturally isomorphic
to the true finite product of its shifted ring coordinate diagrams. -/
def finiteShiftedCoordinateSubsetDiagramIso (k : ℤ) :
    homogeneousCoordinateSubsetDiagram 𝒜 (finiteShiftedFreePiece 𝒜 δ) x hx k ≅
      actualModuleSubsetDiagramPi
        (fun i : I => homogeneousCoordinateSubsetDiagram 𝒜 𝒜 x hx (k - δ i)) :=
  NatIso.ofComponents
    (fun S => (finiteShiftedLocalizedEquiv 𝒜 δ
      (homogeneousCoordinateSubsetProduct x S) (S.card : ℤ)
      (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k).toModuleIso) (by
        intro S T f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        funext i
        exact finiteShiftedLocalizedCoefficient_subsetRestriction 𝒜 δ x hx (leOfHom f) k i z)

end ShiftedDiagramComparison

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
