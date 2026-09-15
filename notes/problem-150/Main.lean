/-
Nikliborc Problem 150: a formalization relative to classical Newtonian balayage.

Scope of formalization
----------------------
Everything after the theorem `classical_balayage_on_sphere` is proved in Lean.
That theorem is intentionally declared as the one external mathematical interface:
it packages the classical balayage/Green-function/Hopf-lemma input for a sphere.
There are no `sorry`s in this file.

The printed Scottish Book problem assumes only a continuous density.  The
interface below gives a continuous *strictly positive* density, hence the
counterexample proved here is stronger than necessary on the density side.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

open Set Metric MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace Nikliborc150

/-- Euclidean three-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The usual two-dimensional surface measure restricted to a set. -/
noncomputable def surfaceMeasure (S : Set E) : Measure E :=
  (Measure.euclideanHausdorffMeasure 2).restrict S

/-- Newtonian single-layer potential with kernel `1 / ‖x-y‖`. -/
noncomputable def singleLayer (S : Set E) (f : E → ℝ) (x : E) : ℝ :=
  ∫ y, f y * (‖x - y‖)⁻¹ ∂surfaceMeasure S

/--
The one external mathematical interface used by this file.

It is the classical balayage theorem specialized to a Euclidean sphere:
if the origin lies strictly inside the ball `B(c,r)`, then the unit point
mass at the origin can be swept to the boundary sphere.  With respect to
standard surface measure, the swept measure has a continuous strictly
positive density, and its Newtonian single-layer potential agrees with
`1 / ‖x‖` at every point exterior to the closed ball.

Analytically, for a smooth boundary this is obtained from the Dirichlet
Green function and the Hopf boundary point lemma.
-/
axiom classical_balayage_on_sphere
    (c : E) (r : ℝ) (hr : 0 < r) (h0 : dist (0 : E) c < r) :
    ∃ f : E → ℝ,
      ContinuousOn f (Metric.sphere c r) ∧
      (∀ y ∈ Metric.sphere c r, 0 < f y) ∧
      (∀ x : E, x ∉ Metric.closedBall c r →
        singleLayer (Metric.sphere c r) f x = (‖x‖)⁻¹)

/-- Unit vector normal to the plane `x₁ = 0`. -/
def e₁ : E := EuclideanSpace.single (0 : Fin 3) 1

/-- The plane through the origin orthogonal to `e₁`. -/
def π : Submodule ℝ E := (ℝ ∙ e₁)ᗮ

/-- Reflection in the plane `π`. -/
noncomputable def R : E ≃ₗᵢ[ℝ] E := π.reflection

/-- Center of our deliberately nonsymmetric sphere. -/
def a : E := (1 / 2 : ℝ) • e₁

/-- Supporting surface.  It is the unit sphere centered at `a`. -/
def S : Set E := Metric.sphere a 1

/-- A point on `S` whose reflection is not on `S`. -/
def p : E := (3 / 2 : ℝ) • e₁

lemma norm_e₁ : ‖e₁‖ = 1 := by
  simp [e₁]

lemma e₁_ne_zero : e₁ ≠ 0 := by
  intro h
  have hnorm := norm_e₁
  rw [h] at hnorm
  norm_num at hnorm

/-- `π` really is a two-dimensional plane in three-space. -/
lemma finrank_π : Module.finrank ℝ π = 2 := by
  change Module.finrank ℝ ↥((ℝ ∙ e₁)ᗮ) = 2
  have hsum :=
    Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ e₁)
  have hspan : Module.finrank ℝ ↥(ℝ ∙ e₁) = 1 :=
    finrank_span_singleton e₁_ne_zero
  have hE : Module.finrank ℝ E = 3 := by
    simp [E]
  rw [hspan, hE] at hsum
  omega

lemma norm_a : ‖a‖ = (1 / 2 : ℝ) := by
  rw [a, norm_smul, norm_e₁, mul_one]
  norm_num

lemma origin_inside : dist (0 : E) a < 1 := by
  rw [dist_zero_left, norm_a]
  norm_num

lemma R_e₁ : R e₁ = -e₁ := by
  simpa [R, π] using
    (Submodule.reflection_orthogonalComplement_singleton_eq_neg (𝕜 := ℝ) e₁)

lemma R_norm (x : E) : ‖R x‖ = ‖x‖ := by
  exact R.norm_map x

lemma R_p : R p = (-3 / 2 : ℝ) • e₁ := by
  calc
    R p = (3 / 2 : ℝ) • R e₁ := by simp [p]
    _ = (3 / 2 : ℝ) • (-e₁) := by rw [R_e₁]
    _ = (-3 / 2 : ℝ) • e₁ := by module

lemma p_mem_S : p ∈ S := by
  rw [S, Metric.mem_sphere, dist_eq_norm]
  have h : p - a = e₁ := by
    simp [p, a]
    module
  rw [h, norm_e₁]

lemma R_p_not_mem_S : R p ∉ S := by
  rw [S, Metric.mem_sphere]
  rw [R_p, a, dist_eq_norm]
  have h : ((-3 / 2 : ℝ) • e₁) - ((1 / 2 : ℝ) • e₁) = (-2 : ℝ) • e₁ := by
    module
  rw [h, norm_smul, norm_e₁]
  norm_num

/-- The supporting sphere is not invariant under reflection in `π`. -/
lemma surface_not_symmetric : R '' S ≠ S := by
  intro hEq
  have hpImage : R p ∈ R '' S := ⟨p, p_mem_S, rfl⟩
  have : R p ∈ S := by simpa [hEq] using hpImage
  exact R_p_not_mem_S this

/-- A crude radius `2` is enough to guarantee that a point is outside the
closed unit ball centered at `a`. -/
lemma outside_closedBall_of_two_lt_norm {x : E} (hx : 2 < ‖x‖) :
    x ∉ Metric.closedBall a 1 := by
  intro hxball
  have hdist : dist x a ≤ 1 := by
    simpa [Metric.mem_closedBall] using hxball
  have hsub : ‖x - a‖ ≤ 1 := by
    simpa [dist_eq_norm] using hdist
  have htri : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by
    calc
      ‖x‖ = ‖(x - a) + a‖ := by simp
      _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
  rw [norm_a] at htri
  linarith

lemma outside_closedBall_R_of_two_lt_norm {x : E} (hx : 2 < ‖x‖) :
    R x ∉ Metric.closedBall a 1 := by
  apply outside_closedBall_of_two_lt_norm
  simpa [R_norm] using hx

/--
Concrete counterexample to the printed implication.

The density is continuous on the supporting surface (indeed the external
balayage interface gives strict positivity as well), the single-layer
potential is reflection-invariant outside the sphere of radius `2`, but the
supporting surface is not reflection-invariant.
-/
theorem counterexample :
    ∃ f : E → ℝ,
      ContinuousOn f S ∧
      (∀ y ∈ S, 0 < f y) ∧
      (∀ x : E, 2 < ‖x‖ → singleLayer S f (R x) = singleLayer S f x) ∧
      R '' S ≠ S := by
  obtain ⟨f, hfcont, hfpos, hpot⟩ :=
    classical_balayage_on_sphere a 1 (by norm_num) origin_inside
  refine ⟨f, ?_, ?_, ?_, surface_not_symmetric⟩
  · simpa [S] using hfcont
  · simpa [S] using hfpos
  · intro x hx
    have hxout : x ∉ Metric.closedBall a 1 := outside_closedBall_of_two_lt_norm hx
    have hRxout : R x ∉ Metric.closedBall a 1 := outside_closedBall_R_of_two_lt_norm hx
    have hxpot : singleLayer S f x = (‖x‖)⁻¹ := by
      simpa [S] using hpot x hxout
    have hRxpot : singleLayer S f (R x) = (‖R x‖)⁻¹ := by
      simpa [S] using hpot (R x) hRxout
    rw [hRxpot, hxpot, R_norm]

/--
A proposition matching the logical content needed to refute the printed
Problem 150: there is a continuous density whose potential has the required
far-field reflection symmetry while the surface itself is not symmetric.
-/
def PrintedCounterexampleExists : Prop :=
  ∃ (S₀ : Set E) (f : E → ℝ) (T : E → E),
    ContinuousOn f S₀ ∧
    (∃ ρ : ℝ, 0 < ρ ∧
      ∀ x : E, ρ < ‖x‖ → singleLayer S₀ f (T x) = singleLayer S₀ f x) ∧
    T '' S₀ ≠ S₀

/-- The printed symmetry implication is false, relative only to the classical
balayage interface above. -/
theorem printed_problem_150_is_false : PrintedCounterexampleExists := by
  obtain ⟨f, hfcont, _hfpos, hsymm, hnonsymm⟩ := counterexample
  refine ⟨S, f, R, hfcont, ?_, hnonsymm⟩
  exact ⟨2, by norm_num, hsymm⟩

end Nikliborc150

#print axioms Nikliborc150.counterexample
#print axioms Nikliborc150.printed_problem_150_is_false
