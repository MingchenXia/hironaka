/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CechComplex
import DeJongAlterations.StableModification.Cohomology.CechAcyclic
import DeJongAlterations.StableModification.Cohomology.CechRefinement
import DeJongAlterations.StableModification.Cohomology.CechLongExact
import DeJongAlterations.StableModification.Cohomology.CechCover
import DeJongAlterations.StableModification.Cohomology.CechPushforward

/-!
# Čech cohomology of quasi-coherent modules (umbrella module)

The curves-only Čech cohomology library of the Claude team's route to Temkin's stable modification
theorem (plan `PLAN-SM-GEOM.md`, chapter F, decision D4; blueprint `sm-cohomology-cech.tex`).
Namespace `DeJongAlterations.StableModification.Cohomology`.

## Files

* `CechComplex`: sections as `R`-modules (`sectionsModuleCat`), the Čech diagram, complex and
  cohomology (`cechDiagram`, `cechComplex`, `cechCohomology`), functoriality (`cechComplexMap`),
  restriction to subfamilies along order embeddings (`cechRestrict`), `Ȟ⁰ = Γ`
  (`cechCohomologyZeroIso`), vanishing above the number of opens
  (`isZero_cechCohomology_of_card_le`), and homology criteria for subset complexes.
* `CechAcyclic`: the cone lemma, locality of exactness, sections of quasi-coherent modules over
  basic opens (`isLocalizedModule_sectionsRestrict`), exactness of the augmented Čech complex on an
  affine (`linkDiagram_exact`) and vanishing on affine schemes (`isZero_cechCohomology_of_isAffine`).
* `CechRefinement`: restriction to a covering subfamily is a quasi-isomorphism
  (`isIso_homologyMap_cechRestrict`); independence of the cover (`cechCohomologyIsoOfCovers`,
  `cechCohomologyIsoOfAffineCovers`), natural in the module.
* `CechLongExact`: short exact sequences of quasi-coherent modules give short exact sequences of
  Čech complexes (`cechShortComplex_shortExact`) and long exact sequences (`cechδ`,
  `cechCohomology_exact₁/₂/₃`).
* `CechCover`: bundled finite affine covers (`FiniteAffineCover`), the cover-free cohomology
  `cohomology F c p = H^p(X, F)` of a quasi-compact scheme with affine diagonal, its comparison with
  any finite affine cover (`cohomologyIsoCech`), `H⁰`, vanishing, and the long exact sequence
  (`cohomologyδ`, `cohomology_exact₁/₂/₃`).
* `CechPushforward`: Čech complexes of pushforwards (`cechComplexPushforwardIso`) and
  `H^p(Y, π_* G) ≅ H^p(X, G)` for affine `π` (`cohomologyPushforwardIso`).

## For the later lanes

* Finiteness (COH2): for `X → Spec A` projective, compute `H^p` with the standard affine cover of
  `ℙⁿ_A`. Codex's projective Čech files compute the corresponding complexes for graded modules
  (`ProperSteinProjectiveCech.homogeneousCoordinateCechComplex`); both are `subsetCechComplex`es,
  so an isomorphism of subset diagrams gives an isomorphism of complexes (`subsetCechComplexIso`).
  Use `cohomologyPushforwardIso` for finite maps to `ℙ¹`.
* Base change and the Mumford complex (COH2/COH3): not in this library yet. The comparison
  `Γ(U_T, F) ⊗_A B → Γ(p⁻¹U_T, p^*F)` comes from the unit of
  `Scheme.Modules.pullbackPushforwardAdjunction`; its bijectivity on affine opens is Codex's
  `QuotGrassmann.originalSpecPullbackSectionsIso` after restricting to the affine open
  (`Scheme.Modules.pullbackComp`, `restrictFunctorIsoPullback`, `pullbackSpecIso`), with the unit
  tracked through the mates (`unit_conjugateEquiv`). Blueprint `prop:sm-cech-base-change`.
-/
