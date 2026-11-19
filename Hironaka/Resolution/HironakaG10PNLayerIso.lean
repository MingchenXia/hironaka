import Hironaka.Resolution.HironakaG10PNBottomRestrict

/-! The restricted quotient layers of the downward chain are the prime targets of the SAME
preselected models on the final open (lane G10P, run 0080; ingredient of
`G10.PN.8.layer_iso`).  Blueprint: `hironaka-g10-pn-layer-iso.tex`.

* `restrictedPrimeTargetIso`: for original opens `Ω ⊆ W ⊆ U(B)`, restricting the prime target of
  `B` on `W` to `Ω` gives the prime target of the SAME `B` on `Ω` (both are casts of cokernels of
  restricted cyclic relations; the comparison goes through the accepted cokernel restriction,
  local/direct and nested restriction isomorphisms).
* `RestrictedChainOn`: the restricted chain whose quotient at every level is the prime target of
  `B_i` on `Ω` itself; `exists_original_restricted_chain_on` upgrades PN.5 to it. -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaG10PNLayerIso

open HironakaChowNativeFreePartContinuation
  HironakaChowNativePrimeSupportContinuation HironakaSingularModuleSheafStalk
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeLocalOverStalkTransport
  HironakaChowNativeLocalOverFiniteDataTransport HironakaNativeCanonicalSupportRestriction
  HironakaNativeCyclicCokernelRestriction HironakaChowNativeModuleStalkExact
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading
  HironakaSingularLocallyFreeStalk HironakaNativeOriginalRestrictionComparison
  HironakaG10PNLayerStep HironakaG10PNDownwardLayers HironakaG10PNRestrictionExact
  HironakaG10PNBottomRestrict

noncomputable section

variable {n : ℕ}

theorem castOriginalModule_eq_transport {W Z : Opens (ComplexModel n)} (h : W = Z)
    (C : OriginalModules W) :
    castOriginalModule h C = (originalModuleCategoryTransport h).obj C := by
  subst h
  rfl

/-- Transport along an equality of opens followed by restriction is restriction. -/
def transportRestrictIso {Z W : Opens (ComplexModel n)} (e : Z = W)
    (Ω : Opens (ComplexModel n)) (h : Ω ≤ W) (h' : Ω ≤ Z) :
    originalModuleCategoryTransport e ⋙ restrictTo W Ω h ≅ restrictTo Z Ω h' := by
  subst e
  exact Functor.leftUnitor _

theorem le_image_of_le (U W Ω : Opens (ComplexModel n)) (h : Ω ≤ W) (hWU : W ≤ U) :
    Ω ≤ originalImageOpen U (inverseImageOpen U W) := by
  rw [original_image_inverseImage U W hWU]
  exact h

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the prime target of `B` from `W` to `Ω` gives the prime target of the SAME `B`
on `Ω`. -/
def restrictedPrimeTargetIso {q : ComplexModel n}
    {P : Ideal (HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) q)}
    (B : NativePrimeAllOpenCokernelData q P) (W Ω : Opens (ComplexModel n)) (h : Ω ≤ W)
    (hWB : W ≤ B.old.U) :
    (restrictTo W Ω h).obj (primeTargetOnDomain B W hWB) ≅
      primeTargetOnDomain B Ω (h.trans hWB) :=
  let U₀ := B.old.U
  let IW := inverseImageOpen U₀ W
  let IΩ := inverseImageOpen U₀ Ω
  let eW := original_image_inverseImage U₀ W hWB
  let eΩ := original_image_inverseImage U₀ Ω (h.trans hWB)
  let h₁ : Ω ≤ originalImageOpen U₀ IW := le_image_of_le U₀ W Ω h hWB
  eqToIso (congrArg (restrictTo W Ω h).obj
      (castOriginalModule_eq_transport eW (cokernel (originalRestrictedCyclicRelation U₀ IW B.old.δ)))) ≪≫
    (transportRestrictIso eW Ω h h₁).app (cokernel (originalRestrictedCyclicRelation U₀ IW B.old.δ)) ≪≫
    (restrictTo (originalImageOpen U₀ IW) Ω h₁).mapIso
      (originalCyclicCokernelRestrictionIso U₀ IW B.old.δ ≪≫
        ((localOriginalRestrictionIso U₀ IW).app (cokernel B.old.δ)).symm) ≪≫
    (restrictToNestedIso U₀ Ω IW h₁).app (cokernel B.old.δ) ≪≫
    (originalModuleCategoryTransport eΩ).mapIso
      ((localOriginalRestrictionIso U₀ IΩ).app (cokernel B.old.δ) ≪≫
        (originalCyclicCokernelRestrictionIso U₀ IΩ B.old.δ).symm) ≪≫
    eqToIso (castOriginalModule_eq_transport eΩ
      (cokernel (originalRestrictedCyclicRelation U₀ IΩ B.old.δ))).symm

/-- ONE exact step on `Ω` whose quotient is the prime target of `B` on `Ω` itself. -/
def RestrictedStepOn {q : ComplexModel n}
    {P : Ideal (HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) q)}
    (B : NativePrimeAllOpenCokernelData q P) (Ω : Opens (ComplexModel n)) (hΩB : Ω ≤ B.old.U)
    (G : OriginalModules Ω) (next : OriginalModules Ω → Prop) : Prop :=
  ∃ (G' : OriginalModules Ω) (ι : G' ⟶ G) (π : G ⟶ primeTargetOnDomain B Ω hΩB)
    (w : ι ≫ π = 0),
    Nonempty (IsLimit (KernelFork.ofι ι w)) ∧ Nonempty (IsColimit (CokernelCofork.ofπ π w)) ∧
    next G'

/-- A restricted step on an open inside the old domain is a step onto the target on `Ω`. -/
theorem restrictedStepOn_of_restrictedStep {q : ComplexModel n}
    {P : Ideal (HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureStalk
      (n := n) q)}
    {B : NativePrimeAllOpenCokernelData q P} {Ω : Opens (ComplexModel n)} (hΩB : Ω ≤ B.old.U)
    {G : OriginalModules Ω} {next next' : OriginalModules Ω → Prop}
    (hn : ∀ G', next G' → next' G') (h : RestrictedStep B Ω G next) :
    RestrictedStepOn B Ω hΩB G next' := by
  obtain ⟨G', Q, ι, π, w, ⟨hl⟩, ⟨hc⟩, ⟨W, hΩW, hWB, ⟨eQ⟩⟩, hG'⟩ := h
  let e : Q ≅ primeTargetOnDomain B Ω hΩB := eQ ≪≫ restrictedPrimeTargetIso B W Ω hΩW hWB
  refine ⟨G', ι, π ≫ e.hom, by rw [← Category.assoc, w, zero_comp], ⟨?_⟩, ⟨?_⟩, hn _ hG'⟩
  · refine KernelFork.isLimitOfIsLimitOfIff' hl (π ≫ e.hom) (fun _ φ => ⟨fun h => ?_, fun h => ?_⟩)
    · rw [← Category.assoc, h, zero_comp]
    · have h' := congrArg (· ≫ e.inv) h
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp] using h'
  · exact IsColimit.ofIsoColimit hc (Cofork.ext e rfl)

/-- The restricted chain with every quotient the prime target of `B_i` on `Ω` itself. -/
def RestrictedChainOn {U : Opens (ComplexModel n)} {p : U}
    {M : ModuleCat.{0} (OriginalRingStalk U p)}
    (d : SelectedPrimeSeries (OriginalRingStalk U p) M)
    (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
    (Ω : Opens (ComplexModel n)) (hΩB : ∀ j : Fin d.s.length, Ω ≤ (B j).old.U) :
    (k : ℕ) → k ≤ d.s.length → OriginalModules Ω → Prop
  | 0, _, G => IsZero G
  | k + 1, hk, G => RestrictedStepOn (B ⟨k, Nat.lt_of_succ_le hk⟩) Ω
      (hΩB ⟨k, Nat.lt_of_succ_le hk⟩) G (RestrictedChainOn d B Ω hΩB k (Nat.le_of_succ_le hk))

theorem restrictedChainOn_of_restrictedChain {U : Opens (ComplexModel n)} {p : U}
    {M : ModuleCat.{0} (OriginalRingStalk U p)}
    (d : SelectedPrimeSeries (OriginalRingStalk U p) M)
    (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
    (Ω : Opens (ComplexModel n)) (hΩB : ∀ j : Fin d.s.length, Ω ≤ (B j).old.U) :
    ∀ (k : ℕ) (hk : k ≤ d.s.length) (G : OriginalModules Ω),
      RestrictedChain d B Ω k hk G → RestrictedChainOn d B Ω hΩB k hk G
  | 0, _, _, h => h
  | k + 1, hk, _, h => restrictedStepOn_of_restrictedStep (hΩB ⟨k, Nat.lt_of_succ_le hk⟩)
      (restrictedChainOn_of_restrictedChain d B Ω hΩB k (Nat.le_of_succ_le hk)) h

/-- **Restricted layers on the final open (ingredient of G10.PN.8.layer_iso).**  PN.5 with every
restricted quotient identified with the prime target of the SAME preselected `B_i` on `Ω` itself:
on EVERY original open `Ω ⊆ Ω₀` the literal restriction `F|Ω` carries `RestrictedChainOn`. -/
theorem exists_original_restricted_chain_on
    (n : ℕ) (U : Opens (ComplexModel n)) (F : OriginalModules U)
    [hF : F.IsFinitePresentation] (p : U) :
    ∃ (d : SelectedPrimeSeries (OriginalRingStalk U p)
        ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj F))
      (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
        (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
      (D : Opens (ComplexModel n)) (_hpD : p.val ∈ D) (hDU : D ≤ U)
      (hDB : ∀ j : Fin d.s.length, D ≤ (B j).old.U)
      (Ω₀ : Opens (ComplexModel n)) (_hpΩ₀ : p.val ∈ Ω₀) (hΩ₀D : Ω₀ ≤ D),
      ∀ (Ω : Opens (ComplexModel n)) (hΩ : Ω ≤ Ω₀),
        RestrictedChainOn d B Ω (fun j => hΩ.trans (hΩ₀D.trans (hDB j))) d.s.length le_rfl
          ((restrictTo U Ω (hΩ.trans (hΩ₀D.trans hDU))).obj F) := by
  obtain ⟨d, B, D, hpD, hDU, hDB, Ω₀, hpΩ₀, hΩ₀D, hall⟩ :=
    exists_original_bottom_exact_restrict n U F p
  exact ⟨d, B, D, hpD, hDU, hDB, Ω₀, hpΩ₀, hΩ₀D, fun Ω hΩ =>
    restrictedChainOn_of_restrictedChain d B Ω (fun j => hΩ.trans (hΩ₀D.trans (hDB j)))
      d.s.length le_rfl _ (hall Ω hΩ)⟩

end

end Hironaka.HironakaG10PNLayerIso
