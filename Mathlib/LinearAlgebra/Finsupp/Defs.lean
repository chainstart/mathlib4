/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Finsupp.SMul

/-!
# Properties of the module `α →₀ M`

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`Mathlib/Data/Finsupp/SMul.lean`.

In this file we define `LinearMap` versions of various maps:

* `Finsupp.lsingle a : M →ₗ[R] ι →₀ M`: `Finsupp.single a` as a linear map;
* `Finsupp.lapply a : (ι →₀ M) →ₗ[R] M`: the map `fun f ↦ f a` as a linear map;
* `Finsupp.lsubtypeDomain (s : Set α) : (α →₀ M) →ₗ[R] (s →₀ M)`: restriction to a subtype as a
  linear map;
* `Finsupp.restrictDom`: `Finsupp.filter` as a linear map to `Finsupp.supported s`;
* `Finsupp.lmapDomain`: a linear map version of `Finsupp.mapDomain`;

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

assert_not_exists Submodule

noncomputable section

open Set LinearMap

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R R₂ R₃ : Type*} {S : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R₂ N]
variable [AddCommMonoid P] [Module R₃ P]
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂}
variable {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

section LinearEquivFunOnFinite

variable (R : Type*) {S : Type*} (M : Type*) (α : Type*)
variable [Finite α] [AddCommMonoid M] [Semiring R] [Module R M]

/-- Given `Finite α`, `linearEquivFunOnFinite R` is the natural `R`-linear equivalence between
`α →₀ β` and `α → β`. -/
@[simps apply]
noncomputable def linearEquivFunOnFinite : (α →₀ M) ≃ₗ[R] α → M :=
  { equivFunOnFinite with
    toFun := (⇑)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
theorem linearEquivFunOnFinite_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α) (single x m) = Pi.single x m :=
  equivFunOnFinite_single x m

@[simp]
theorem linearEquivFunOnFinite_symm_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α).symm (Pi.single x m) = single x m :=
  equivFunOnFinite_symm_single x m

@[simp]
theorem linearEquivFunOnFinite_symm_coe (f : α →₀ M) : (linearEquivFunOnFinite R M α).symm f = f :=
  (linearEquivFunOnFinite R M α).symm_apply_apply f

@[simp]
theorem linearEquivFunOnFinite_symm_apply (f : α → M) (x) :
    (linearEquivFunOnFinite R M α).symm f x = f x :=
  rfl

end LinearEquivFunOnFinite

/-- Interpret `Finsupp.single a` as a linear map. -/
def lsingle (a : α) : M →ₗ[R] α →₀ M :=
  { Finsupp.singleAddHom a with map_smul' := fun _ _ => (smul_single _ _ _).symm }

/-- Two `R`-linear maps from `Finsupp X M` which agree on each `single x y` agree everywhere. -/
theorem lhom_ext ⦃φ ψ : (α →₀ M) →ₛₗ[σ₁₂] N⦄ (h : ∀ a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h

/-- Two `R`-linear maps from `Finsupp X M` which agree on each `single x y` agree everywhere.

We formulate this fact using equality of linear maps `φ.comp (lsingle a)` and `ψ.comp (lsingle a)`
so that the `ext` tactic can apply a type-specific extensionality lemma to prove equality of these
maps. E.g., if `M = R`, then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
-- The priority should be higher than `LinearMap.ext`.
@[ext high]
theorem lhom_ext' ⦃φ ψ : (α →₀ M) →ₛₗ[σ₁₂] N⦄ (h : ∀ a, φ.comp (lsingle a) = ψ.comp (lsingle a)) :
    φ = ψ :=
  lhom_ext fun a => LinearMap.congr_fun (h a)

/-- Interpret `fun f : α →₀ M ↦ f a` as a linear map. -/
def lapply (a : α) : (α →₀ M) →ₗ[R] M :=
  { Finsupp.applyAddHom a with map_smul' := fun _ _ => rfl }

instance [Nonempty α] [FaithfulSMul R M] : FaithfulSMul R (α →₀ M) :=
  .of_injective (Finsupp.lsingle <| Classical.arbitrary _) (Finsupp.single_injective _)

section LSubtypeDomain

variable (s : Set α)

/-- Interpret `Finsupp.subtypeDomain s` as a linear map. -/
def lsubtypeDomain : (α →₀ M) →ₗ[R] s →₀ M where
  toFun := subtypeDomain fun x => x ∈ s
  map_add' _ _ := subtypeDomain_add
  map_smul' _ _ := ext fun _ => rfl

theorem lsubtypeDomain_apply (f : α →₀ M) :
    (lsubtypeDomain s : (α →₀ M) →ₗ[R] s →₀ M) f = subtypeDomain (fun x => x ∈ s) f :=
  rfl

end LSubtypeDomain

@[simp]
theorem lsingle_apply (a : α) (b : M) : (lsingle a : M →ₗ[R] α →₀ M) b = single a b :=
  rfl

@[simp]
theorem lapply_apply (a : α) (f : α →₀ M) : (lapply a : (α →₀ M) →ₗ[R] M) f = f a :=
  rfl

@[simp]
theorem lapply_comp_lsingle_same (a : α) : lapply a ∘ₗ lsingle a = (.id : M →ₗ[R] M) := by ext; simp

@[simp]
theorem lapply_comp_lsingle_of_ne (a a' : α) (h : a ≠ a') :
    lapply a ∘ₗ lsingle a' = (0 : M →ₗ[R] M) := by ext; simp [h.symm]

section LMapDomain

variable {α' : Type*} {α'' : Type*} (M R)

/-- Interpret `Finsupp.mapDomain` as a linear map. -/
def lmapDomain (f : α → α') : (α →₀ M) →ₗ[R] α' →₀ M where
  toFun := mapDomain f
  map_add' _ _ := mapDomain_add
  map_smul' := mapDomain_smul

@[simp]
theorem lmapDomain_apply (f : α → α') (l : α →₀ M) :
    (lmapDomain M R f : (α →₀ M) →ₗ[R] α' →₀ M) l = mapDomain f l :=
  rfl

lemma coe_lmapDomain (f : α → α') : ⇑(lmapDomain M R f) = Finsupp.mapDomain f :=
  rfl

@[simp]
theorem lmapDomain_id : (lmapDomain M R _root_.id : (α →₀ M) →ₗ[R] α →₀ M) = LinearMap.id :=
  LinearMap.ext fun _ => mapDomain_id

theorem lmapDomain_comp (f : α → α') (g : α' → α'') :
    lmapDomain M R (g ∘ f) = (lmapDomain M R g).comp (lmapDomain M R f) :=
  LinearMap.ext fun _ => mapDomain_comp

/-- `Finsupp.mapDomain` as a `LinearEquiv`. -/
def mapDomain.linearEquiv (f : α ≃ α') : (α →₀ M) ≃ₗ[R] (α' →₀ M) where
  __ := lmapDomain M R f.toFun
  invFun := mapDomain f.symm
  left_inv _ := by
    simp [← mapDomain_comp]
  right_inv _ := by
    simp [← mapDomain_comp]

@[simp] theorem mapDomain.coe_linearEquiv (f : α ≃ α') :
    ⇑(linearEquiv M R f) = mapDomain f := rfl

@[simp] theorem mapDomain.toLinearMap_linearEquiv (f : α ≃ α') :
    (linearEquiv M R f : _ →ₗ[R] _) = lmapDomain M R f := rfl

@[simp] theorem mapDomain.linearEquiv_symm (f : α ≃ α') :
    (linearEquiv M R f).symm = linearEquiv M R f.symm := rfl

end LMapDomain

section LComapDomain

variable {β : Type*}

/-- Given `f : α → β` and a proof `hf` that `f` is injective, `lcomapDomain f hf` is the linear map
sending `l : β →₀ M` to the finitely supported function from `α` to `M` given by composing
`l` with `f`.

This is the linear version of `Finsupp.comapDomain`. -/
@[simps]
def lcomapDomain (f : α → β) (hf : Function.Injective f) : (β →₀ M) →ₗ[R] α →₀ M where
  toFun l := Finsupp.comapDomain f l hf.injOn
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

theorem leftInverse_lcomapDomain_mapDomain (f : α → β) (hf : Function.Injective f) :
    Function.LeftInverse (lcomapDomain (R := R) (M := M) f hf) (mapDomain f) :=
  comapDomain_mapDomain f hf

end LComapDomain

/-- `Finsupp.mapRange` as a `LinearMap`. -/
@[simps apply]
def mapRange.linearMap (f : M →ₛₗ[σ₁₂] N) : (α →₀ M) →ₛₗ[σ₁₂] α →₀ N :=
  { mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
    map_smul' := fun c v => mapRange_smul' c (σ₁₂ c) v (f.map_smulₛₗ c) }

@[simp]
theorem mapRange.linearMap_id :
    mapRange.linearMap LinearMap.id = (LinearMap.id : (α →₀ M) →ₗ[R] _) :=
  LinearMap.ext mapRange_id

theorem mapRange.linearMap_comp (f : N →ₛₗ[σ₂₃] P) (f₂ : M →ₛₗ[σ₁₂] N) :
    (mapRange.linearMap (f.comp f₂) : (α →₀ _) →ₛₗ[σ₁₃] _) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  LinearMap.ext <| mapRange_comp f f.map_zero f₂ f₂.map_zero (comp f f₂).map_zero

@[simp]
theorem mapRange.linearMap_toAddMonoidHom (f : M →ₛₗ[σ₁₂] N) :
    (mapRange.linearMap f).toAddMonoidHom =
      (mapRange.addMonoidHom f.toAddMonoidHom : (α →₀ M) →+ _) :=
  AddMonoidHom.ext fun _ => rfl

section Equiv

variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
variable [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]

/-- `Finsupp.mapRange` as a `LinearEquiv`. -/
@[simps apply]
def mapRange.linearEquiv (e : M ≃ₛₗ[σ₁₂] N) : (α →₀ M) ≃ₛₗ[σ₁₂] α →₀ N :=
  { mapRange.linearMap e.toLinearMap,
    mapRange.addEquiv e.toAddEquiv with
    toFun := mapRange e e.map_zero
    invFun := mapRange e.symm e.symm.map_zero }

@[simp]
theorem mapRange.linearEquiv_refl :
    mapRange.linearEquiv (LinearEquiv.refl R M) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext mapRange_id

theorem mapRange.linearEquiv_trans (f : M ≃ₛₗ[σ₁₂] N) (f₂ : N ≃ₛₗ[σ₂₃] P) :
    (mapRange.linearEquiv (f.trans f₂) : (α →₀ _) ≃ₛₗ[σ₁₃] _) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  LinearEquiv.ext <| mapRange_comp f₂ f₂.map_zero f f.map_zero (f.trans f₂).map_zero

@[simp]
theorem mapRange.linearEquiv_symm (f : M ≃ₛₗ[σ₁₂] N) :
    ((mapRange.linearEquiv f).symm : (α →₀ _) ≃ₛₗ[σ₂₁] _) = mapRange.linearEquiv f.symm :=
  LinearEquiv.ext fun _x => rfl

@[simp]
theorem mapRange.linearEquiv_toAddEquiv (f : M ≃ₛₗ[σ₁₂] N) :
    (mapRange.linearEquiv f).toAddEquiv = (mapRange.addEquiv f.toAddEquiv : (α →₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => rfl

@[simp]
theorem mapRange.linearEquiv_toLinearMap (f : M ≃ₛₗ[σ₁₂] N) :
    (mapRange.linearEquiv f).toLinearMap =
    (mapRange.linearMap f.toLinearMap : (α →₀ M) →ₛₗ[σ₁₂] _) :=
  LinearMap.ext fun _ => rfl

end Equiv

section Prod

variable {α β R M : Type*} [DecidableEq α] [Semiring R] [AddCommMonoid M] [Module R M]

variable (R) in
/-- The linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M`.

This is the `LinearEquiv` version of `Finsupp.curryEquiv`. -/
@[simps +simpRhs]
noncomputable def curryLinearEquiv : (α × β →₀ M) ≃ₗ[R] α →₀ β →₀ M where
  toAddEquiv := curryAddEquiv
  map_smul' c f := by ext; simp

@[deprecated (since := "2026-01-03")] alias finsuppProdLEquiv := curryLinearEquiv

theorem curryLinearEquiv_symm_apply_apply (f : α →₀ β →₀ M) (xy) :
    (curryLinearEquiv R).symm f xy = f xy.1 xy.2 :=
  rfl

@[deprecated (since := "2026-01-03")]
alias finsuppProdLEquiv_symm_apply_apply := curryLinearEquiv_symm_apply_apply

end Prod

end Finsupp

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

section

variable (R)

/-- If `Subsingleton R`, then `M ≃ₗ[R] ι →₀ R` for any type `ι`. -/
@[simps]
def Module.subsingletonEquiv (R M ι : Type*) [Semiring R] [Subsingleton R] [AddCommMonoid M]
    [Module R M] : M ≃ₗ[R] ι →₀ R where
  toFun _ := 0
  invFun _ := 0
  left_inv m :=
    have := Module.subsingleton R M
    Subsingleton.elim _ _
  right_inv f := by simp only [eq_iff_true_of_subsingleton]
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm

end

namespace Module.End

variable (ι : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `M` is an `R`-module and `ι` is a type, then an additive endomorphism of `M` that
commutes with all `R`-endomorphisms of `M` gives rise to an additive endomorphism of `ι →₀ M`
that commutes with all `R`-endomorphisms of `ι →₀ M`. -/
@[simps] noncomputable def ringHomEndFinsupp :
    End (End R M) M →+* End (End R (ι →₀ M)) (ι →₀ M) where
  toFun f :=
  { toFun := Finsupp.mapRange.addMonoidHom f
    map_add' := map_add _
    map_smul' g x := x.induction_linear (by simp)
      (fun _ _ h h' ↦ by rw [smul_add, map_add, h, h', map_add, smul_add]) fun i m ↦ by
        ext j
        change f (Finsupp.lapply j ∘ₗ g ∘ₗ Finsupp.lsingle i • m) = _
        rw [map_smul]
        simp }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

variable {ι}

/-- If `M` is an `R`-module and `ι` is a nonempty type, then every additive endomorphism
of `ι →₀ M` that commutes with all `R`-endomorphisms of `ι →₀ M` comes from an additive
endomorphism of `M` that commutes with all `R`-endomorphisms of `M`.
See (15) in F4 of §28 on p.131 of [Lorenz2008]. -/
@[simps!] noncomputable def ringEquivEndFinsupp (i : ι) :
    End (End R M) M ≃+* End (End R (ι →₀ M)) (ι →₀ M) where
  __ := ringHomEndFinsupp ι
  invFun f :=
  { toFun m := f (Finsupp.single i m) i
    map_add' _ _ := by simp
    map_smul' g m := let g := Finsupp.mapRange.linearMap g
      show _ = g _ i by rw [← End.smul_def g, ← map_smul]; simp [g] }
  left_inv _ := by ext; simp
  right_inv f := by
    ext x j
    change f (Finsupp.lsingle (R := R) (M := M) i ∘ₗ Finsupp.lapply j • x) i = _
    rw [map_smul]
    simp

end Module.End
