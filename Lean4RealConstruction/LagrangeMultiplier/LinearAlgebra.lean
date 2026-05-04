import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Lean4RealConstruction.LagrangeMultiplier.PairComponent
import Lean4RealConstruction.LagrangeMultiplier.PrefixSplit

variable {m n : ℕ}

open scoped Topology Set Filter
open EuclideanSplit EuclideanPrefixSplit Submodule
open RealInnerProductSpace Gradient LinearMap ContinuousLinearMap InnerProduct

def IsInvertibleCLM {n : ℕ} (A : Euc n →L[ℝ] Euc n) : Prop :=
  ∃ e : Euc n ≃L[ℝ] Euc n,
    (e : Euc n →L[ℝ] Euc n) = A

theorem IsInvertibleCLM_of_det_ne_zero
    {A : Euc m →L[ℝ] Euc m}
    (hdet : LinearMap.det (A : Euc m →ₗ[ℝ] Euc m) ≠ 0) :
    IsInvertibleCLM A := by
  have hker : (A : Euc m →ₗ[ℝ] Euc m).ker = ⊥ := by
    by_contra hker
    exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker)
  have hsurj : (A : Euc m →ₗ[ℝ] Euc m).range = ⊤ := by
    rwa [← LinearMap.ker_eq_bot_iff_range_eq_top]
  refine ⟨ContinuousLinearEquiv.ofBijective A hker hsurj, rfl⟩

/--
Normal space of `g` at `a`, defined as the range of the adjoint
of the derivative.
-/
noncomputable def normalSpaceOfMap
    (g : Euc n → Euc m) (a : Euc n) :
    Submodule ℝ (Euc n) :=
  LinearMap.range
    ((fderiv ℝ g a : Euc n →ₗ[ℝ] Euc m).adjoint)

theorem ker_fderiv_eq_normalSpace_orthogonal
    (g : Euc n → Euc m) (a : Euc n) :
    (fderiv ℝ g a).ker =
      (normalSpaceOfMap g a)ᗮ := by
  unfold normalSpaceOfMap
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    (ContinuousLinearMap.orthogonal_range ((fderiv ℝ g a)†)).symm

/-- The gradient of the `i`-th component of `g`. -/
noncomputable def componentGradient
    (g : Euc n → Euc m) (a : Euc n) (i : Fin m) : Euc n :=
  ∇ (fun x : Euc n => g x i) a

/-- Span of the gradients of the component functions of `g`. -/
noncomputable def gradientSpan
    (g : Euc n → Euc m) (a : Euc n) :
    Submodule ℝ (Euc n) :=
  Submodule.span ℝ
    (Set.range fun i : Fin m => componentGradient g a i)

theorem normalSpace_eq_gradientSpan
    {g : Euc n → Euc m} {a : Euc n}
    (hg : DifferentiableAt ℝ g a) :
    normalSpaceOfMap g a = gradientSpan g a := by
  let b : Module.Basis (Fin m) ℝ (Euc m) :=
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  let proj : Fin m → Euc m →L[ℝ] ℝ := fun i =>
    EuclideanSpace.proj i
  have hcomponent :
      ∀ i : Fin m,
        componentGradient g a i =
          ((fderiv ℝ g a : Euc n →ₗ[ℝ] Euc m).adjoint) (b i) := by
    intro i
    have hgi : DifferentiableAt ℝ (fun x : Euc n => (g x).ofLp i) a := by
      simpa [Function.comp] using
        (((proj i).differentiableAt).comp a hg)
    have hfderiv_i :
        fderiv ℝ (fun x : Euc n => (g x).ofLp i) a =
          (proj i).comp (fderiv ℝ g a) := by
      simpa [Function.comp] using
        (fderiv_comp a ((proj i).differentiableAt) hg)
    apply ext_inner_right ℝ
    intro x
    calc
      ⟪componentGradient g a i, x⟫ = fderiv ℝ (fun y : Euc n => g y i) a x := by
        rw [componentGradient, inner_gradient_left hgi]
      _ = ⟪(fderiv ℝ g a) x, b i⟫ := by
        rw [hfderiv_i, ContinuousLinearMap.comp_apply]
        simpa [proj, b] using
          (EuclideanSpace.inner_basisFun_real (ι := Fin m) ((fderiv ℝ g a) x) i).symm
      _ = ⟪b i, (fderiv ℝ g a) x⟫ := by
        rw [real_inner_comm]
      _ = ⟪((fderiv ℝ g a : Euc n →ₗ[ℝ] Euc m).adjoint) (b i), x⟫ := by
        simpa using
          (LinearMap.adjoint_inner_left
            (A := (fderiv ℝ g a : Euc n →ₗ[ℝ] Euc m)) x (b i)).symm
  have hadj :
      ((fderiv ℝ g a : Euc n →ₗ[ℝ] Euc m).adjoint) =
        b.constr ℝ (fun i : Fin m => componentGradient g a i) := by
    apply b.ext
    intro i
    simpa using (hcomponent i).symm
  unfold normalSpaceOfMap gradientSpan
  rw [hadj]
  simpa using (b.constr_range ℝ (f := fun i : Fin m => componentGradient g a i))

theorem fderiv_range_eq_top_of_gradient_independent
    {g : Euc n → Euc m} {a : Euc n}
    (hg : DifferentiableAt ℝ g a)
    (hli : LinearIndependent ℝ
      (fun i : Fin m => componentGradient g a i)) :
    (fderiv ℝ g a).range = ⊤ := by
  let A : Euc m →ₗ[ℝ] Euc n :=
    (fderiv ℝ g a : Euc n →ₗ[ℝ] Euc m).adjoint
  have hnormal :
      Module.finrank ℝ (normalSpaceOfMap g a) = m := by
    rw [normalSpace_eq_gradientSpan hg]
    unfold gradientSpan
    simpa using (finrank_span_eq_card hli)
  have hrange :
      Module.finrank ℝ (LinearMap.range A) = m := by
    simpa [A, normalSpaceOfMap] using hnormal
  have hsum :
      Module.finrank ℝ (LinearMap.range A) +
        Module.finrank ℝ (LinearMap.ker A) = m := by
    simpa [A] using LinearMap.finrank_range_add_finrank_ker A
  have hker_fin : Module.finrank ℝ (LinearMap.ker A) = 0 := by
    omega
  have hker : LinearMap.ker A = ⊥ := by
    exact Submodule.finrank_eq_zero.mp hker_fin
  have hor : (fderiv ℝ g a).rangeᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range]
    simpa [A] using hker
  exact Submodule.orthogonal_eq_bot_iff.mp hor

noncomputable def DxBlockCLM
    (hmn : m ≤ n)
    (A : Euc n →L[ℝ] Euc m) :
    Euc m →L[ℝ] Euc m :=
  A.comp (xInclCLM hmn)

theorem surjective_of_DxBlockCLM_invertible
    (hmn : m ≤ n)
    (A : Euc n →L[ℝ] Euc m)
    (hA : IsInvertibleCLM (DxBlockCLM hmn A)) :
    A.range = ⊤
:= by
  rcases hA with ⟨e, eq⟩;
  simp [DxBlockCLM] at eq;
  rw [range_eq_top_of_surjective]
  intro y;
  rcases e.surjective y with ⟨x, rfl⟩
  use xInclCLM hmn x
  rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply, ← eq];
  rfl

theorem exists_perm_DxBlockCLM_invertible_of_surjective
    {A : Euc n →L[ℝ] Euc m}
    (hA : A.range = ⊤) :
    ∃ P : Euc n ≃L[ℝ] Euc n,
    ∃ hmn : m ≤ n,
      IsInvertibleCLM
        (DxBlockCLM hmn (A.comp (P : Euc n →L[ℝ] Euc n))) := by
  have hrange_fin :
      Module.finrank ℝ (LinearMap.range (A : Euc n →ₗ[ℝ] Euc m)) = m := by
    have hfin :=
      congrArg (fun S : Submodule ℝ (Euc m) => Module.finrank ℝ S) hA
    simpa using hfin
  have hfin_n : Module.finrank ℝ (Euc n) = n := by
    simp [EuclideanSplit.Euc]
  have hmn : m ≤ n := by
    have hle := LinearMap.finrank_range_le (A : Euc n →ₗ[ℝ] Euc m)
    rw [hrange_fin, hfin_n] at hle
    exact hle
  obtain ⟨B, hB⟩ := ContinuousLinearMap.exists_right_inverse_of_surjective A hA
  have hright : Function.RightInverse B A := by
    intro x
    have hx := congrArg (fun f : Euc m →L[ℝ] Euc m => f x) hB
    simpa using hx
  have hsum : m + Module.finrank ℝ (LinearMap.ker (A : Euc n →ₗ[ℝ] Euc m)) = n := by
    have hsum' := LinearMap.finrank_range_add_finrank_ker (A : Euc n →ₗ[ℝ] Euc m)
    rw [hrange_fin, hfin_n] at hsum'
    exact hsum'
  have hker_fin :
      Module.finrank ℝ (LinearMap.ker (A : Euc n →ₗ[ℝ] Euc m)) = n - m := by
    omega
  let eKer : Euc (n - m) ≃L[ℝ] A.ker :=
    ContinuousLinearEquiv.ofFinrankEq (by
      simpa using hker_fin.symm)
  let e : Euc n ≃L[ℝ] (Euc m × A.ker) :=
    ContinuousLinearEquiv.equivOfRightInverse A B hright
  let Pprod : (Euc m × Euc (n - m)) ≃L[ℝ] Euc n :=
    ((ContinuousLinearEquiv.refl ℝ (Euc m)).prodCongr eKer).trans e.symm
  let P : Euc n ≃L[ℝ] Euc n :=
    (splitPrefixEquiv n m hmn).trans Pprod
  have hDx :
      DxBlockCLM hmn (A.comp (P : Euc n →L[ℝ] Euc n)) =
        ContinuousLinearMap.id ℝ (Euc m) := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      DxBlockCLM hmn (A.comp (P : Euc n →L[ℝ] Euc n)) x
          = A (P (xInclCLM hmn x)) := by
              rfl
      _ = A (Pprod (x, 0)) := by
            simp [P, Pprod, xInclCLM]
      _ = A (e.symm (x, 0)) := by
            simp [Pprod]
      _ = A (B x) := by
            simp [e]
      _ = x := hright x
  refine ⟨P, hmn, ?_⟩
  refine ⟨ContinuousLinearEquiv.refl ℝ (Euc m), ?_⟩
  simpa using hDx.symm

theorem DxBlock_eq_DxBlockCLM
    (hmn : m ≤ n)
    (g : Euc n → Euc m)
    (a : Euc n) :
    DxBlock hmn g a =
      DxBlockCLM hmn (fderiv ℝ g a) := by
  rfl

theorem fderiv_comp_linearEquiv
    {g : Euc n → Euc m}
    {a : Euc n}
    (hg : DifferentiableAt ℝ g a)
    (P : Euc n ≃L[ℝ] Euc n) :
    fderiv ℝ (g ∘ P) (P.symm a)
      =
    (fderiv ℝ g a).comp (P : Euc n →L[ℝ] Euc n) := by
  have hP : P (P.symm a) = a := by simp
  have hg_at : DifferentiableAt ℝ g (P (P.symm a)) := by
    simpa [hP] using hg
  have hcomp :=
    fderiv_comp (P.symm a) hg_at P.differentiableAt
  change fderiv ℝ (g ∘ P) _ = _
  rw [hcomp, hP, ContinuousLinearEquiv.fderiv P]
