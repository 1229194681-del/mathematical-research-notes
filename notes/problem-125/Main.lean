import Mathlib

set_option autoImplicit false

/-!
# Scottish Book Problem 125: a fully explicit Lean formalization

This file formalizes a counterexample to the global single-valued factorization
asked for in Scottish Book Problem 125.

All mathematical claims below are proved internally from Mathlib lemmas; no proof placeholders or custom mathematical axioms are introduced.

The counterexample is the elementary real-analytic one

  s(x)   = (x - 2)^2 + 1,
  φ(x)   = -x s(x)^2,
  g(x)   = -x^3/6 + 5x/2,
  f(x,y) = g(x) + y/(2 s(x)).

For each x, the two partial derivatives of f at (x, φ(x)) are formalized
using `HasDerivAt` on the one-variable slices.  They satisfy

  x f_x + φ(x) f_y = 0,
  4 f_x f_y = 1.

The global factorization statement is formalized with the factorizing function
defined exactly on the image of x ↦ x / φ(x), for x ≠ 0.  The points x = 1
and x = 3 have the same parameter value but different f-values, so no
single-valued factorization exists.

The core theorem is `scottishBook125_negative`; the theorem
`scottishBook125_paper_package` bundles every mathematical assertion retained
in the accompanying revised paper.
-/

namespace Scottish125


/-- The positive auxiliary function `s(x) = (x - 2)^2 + 1`. -/
noncomputable def s (x : ℝ) : ℝ := (x - 2) * (x - 2) + 1

/-- The witnessing curve. -/
noncomputable def φ (x : ℝ) : ℝ := -x * (s x) ^ 2

/-- The x-dependent part of the counterexample. -/
noncomputable def g (x : ℝ) : ℝ := -(x * x * x) / 6 + 5 * x / 2

/-- The explicit counterexample. -/
noncomputable def f (x y : ℝ) : ℝ := g x + y / (2 * s x)

/-- The explicit x-partial derivative of `f`. -/
noncomputable def fx (x y : ℝ) : ℝ :=
  -x ^ 2 / 2 + 5 / 2 - y * (x - 2) / (s x) ^ 2

/-- The explicit y-partial derivative of `f`. -/
noncomputable def fy (x _y : ℝ) : ℝ := 1 / (2 * s x)

/-- `s` is everywhere strictly positive. -/
lemma s_pos (x : ℝ) : 0 < s x := by
  rw [s]
  nlinarith [sq_nonneg (x - 2)]

/-- In particular, `s` never vanishes. -/
lemma s_ne_zero (x : ℝ) : s x ≠ 0 :=
  ne_of_gt (s_pos x)

/-- The curve denominator is nonzero away from x = 0. -/
lemma φ_ne_zero {x : ℝ} (hx : x ≠ 0) : φ x ≠ 0 := by
  rw [φ]
  exact mul_ne_zero (neg_ne_zero.mpr hx) (pow_ne_zero 2 (s_ne_zero x))

/-- ASCII alias for the nonvanishing lemma, convenient in external documentation. -/
lemma phi_ne_zero {x : ℝ} (hx : x ≠ 0) : φ x ≠ 0 :=
  φ_ne_zero hx

/-! ## Derivative calculations -/

/-- Derivative of the auxiliary function `s`. -/
lemma hasDerivAt_s (x : ℝ) :
    HasDerivAt s (2 * (x - 2)) x := by
  have hlin : HasDerivAt (fun t : ℝ => t - 2) 1 x :=
    (hasDerivAt_id x).sub_const 2
  have h := hlin.mul hlin
  have hval :
      (1 * (x - 2) + (x - 2) * 1 : ℝ) = 2 * (x - 2) := by
    ring
  rw [hval] at h
  change HasDerivAt
    ((fun t : ℝ => t - 2) * (fun t : ℝ => t - 2))
    (2 * (x - 2)) x at h
  change HasDerivAt
    (fun t : ℝ => (t - 2) * (t - 2) + 1)
    (2 * (x - 2)) x
  exact h.add_const 1

/-- Derivative of `g`. -/
lemma hasDerivAt_g (x : ℝ) :
    HasDerivAt g (-x ^ 2 / 2 + 5 / 2) x := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := by
    exact hasDerivAt_id x
  have hsq := hid.mul hid
  have hsqVal :
      (1 * x + x * 1 : ℝ) = 2 * x := by
    ring
  rw [hsqVal] at hsq
  have hcube := hsq.mul hid
  -- Normalize the remaining pointwise application coming from multiplication
  -- in the Pi type before rewriting the derivative value.
  simp only [Pi.mul_apply] at hcube
  have hcubeVal :
      ((2 * x) * x + (x * x) * 1 : ℝ) = 3 * x ^ 2 := by
    ring
  rw [hcubeVal] at hcube
  have hfirst := hcube.neg.div_const 6
  have hsecond :=
    (HasDerivAt.const_mul (5 : ℝ) hid).div_const 2
  have h := hfirst.add hsecond
  -- Normalize the trivial scalar derivative `5 * 1 / 2` first.
  norm_num at h
  have hval :
      (-(3 * x ^ 2) / 6 + 5 / 2 : ℝ) =
        -x ^ 2 / 2 + 5 / 2 := by
    ring
  rw [hval] at h
  change HasDerivAt
    ((fun t : ℝ => -(t * t * t) / 6) + (fun t : ℝ => 5 * t / 2))
    (-x ^ 2 / 2 + 5 / 2) x
  exact h

/-- The x-partial derivative of `f`, with y held fixed. -/
lemma hasDerivAt_f_x (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f t y) (fx x y) x := by
  have hden :
      HasDerivAt (fun t : ℝ => 2 * s t) (2 * (2 * (x - 2))) x :=
    HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_s x)
  have hnum :
      HasDerivAt (fun _t : ℝ => y) 0 x :=
    hasDerivAt_const x y
  have hden_ne : (2 : ℝ) * s x ≠ 0 :=
    mul_ne_zero (by norm_num) (s_ne_zero x)
  have hquot := hnum.div hden hden_ne
  have h := (hasDerivAt_g x).add hquot
  have hval :
      (-x ^ 2 / 2 + 5 / 2 +
          (0 * (2 * s x) - y * (2 * (2 * (x - 2)))) / (2 * s x) ^ 2 : ℝ) =
        fx x y := by
    rw [fx]
    field_simp [s_ne_zero x]
    ring
  rw [hval] at h
  change HasDerivAt
    (g + (fun _t : ℝ => y) / (fun t : ℝ => 2 * s t))
    (fx x y) x
  exact h

/-- The y-partial derivative of `f`, with x held fixed. -/
lemma hasDerivAt_f_y (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f x t) (fy x y) y := by
  have h :=
    HasDerivAt.const_add (g x)
      ((hasDerivAt_id y).div_const (2 * s x))
  change HasDerivAt
    (fun t : ℝ => g x + t / (2 * s x))
    (1 / (2 * s x)) y
  exact h

/-- On the witnessing curve, the x-partial simplifies to `s(x)/2`. -/
lemma fx_on_curve_value (x : ℝ) :
    fx x (φ x) = s x / 2 := by
  have hs := s_ne_zero x
  simp only [fx, φ]
  field_simp [hs]
  simp [s]
  ring

/-- On the witnessing curve, the y-partial is `1/(2s(x))`. -/
lemma fy_on_curve_value (x : ℝ) :
    fy x (φ x) = 1 / (2 * s x) := by
  rfl

/-- The x-partial derivative at a point on the witnessing curve. -/
lemma hasDerivAt_f_x_on_curve (x : ℝ) :
    HasDerivAt (fun t : ℝ => f t (φ x)) (s x / 2) x := by
  have h := hasDerivAt_f_x x (φ x)
  rw [fx_on_curve_value] at h
  exact h

/-- The y-partial derivative at a point on the witnessing curve. -/
lemma hasDerivAt_f_y_on_curve (x : ℝ) :
    HasDerivAt (fun t : ℝ => f x t) (1 / (2 * s x)) (φ x) := by
  simpa only [fy] using hasDerivAt_f_y x (φ x)

/-! ## A precise formalization of condition A -/

/--
`ConditionAAt F φ x` says that the two one-variable slices defining the
partial derivatives of `F` at `(x, φ x)` have derivatives `px, py`, and these
derivatives satisfy Infeld's two equations.
-/
def ConditionAAt (F : ℝ → ℝ → ℝ) (curve : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ px py : ℝ,
    HasDerivAt (fun t : ℝ => F t (curve x)) px x ∧
    HasDerivAt (fun t : ℝ => F x t) py (curve x) ∧
    x * px + curve x * py = 0 ∧
    4 * px * py = 1

/-- Condition A holds at every real point of the witnessing curve. -/
def SatisfiesConditionA (F : ℝ → ℝ → ℝ) (curve : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ConditionAAt F curve x

lemma first_Infeld_equation (x : ℝ) :
    x * (s x / 2) + φ x * (1 / (2 * s x)) = 0 := by
  have hs := s_ne_zero x
  simp only [φ]
  field_simp [hs]
  ring

lemma second_Infeld_equation (x : ℝ) :
    4 * (s x / 2) * (1 / (2 * s x)) = 1 := by
  have hs := s_ne_zero x
  field_simp [hs]
  norm_num

/-- The explicit pair `(f, φ)` satisfies condition A everywhere. -/
theorem satisfiesConditionA : SatisfiesConditionA f φ := by
  intro x
  refine ⟨s x / 2, 1 / (2 * s x), ?_, ?_, ?_, ?_⟩
  · exact hasDerivAt_f_x_on_curve x
  · exact hasDerivAt_f_y_on_curve x
  · exact first_Infeld_equation x
  · exact second_Infeld_equation x

/-! ## The excluded linear case -/

/--
The linear case excluded in the printed problem:
`F(x,y) = a*x + b*y` with `a*b = 1/4`.
-/
def IsExcludedLinearCase (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, a * b = 1 / 4 ∧ ∀ x y : ℝ, F x y = a * x + b * y

/-- The explicit counterexample is not of the excluded linear form. -/
theorem f_not_excluded_linear : ¬ IsExcludedLinearCase f := by
  rintro ⟨a, b, _hab, hlin⟩
  have h01 := hlin 0 1
  have h00 := hlin 0 0
  have h21 := hlin 2 1
  have h20 := hlin 2 0
  norm_num [f, g, s] at h01 h00 h21 h20
  linarith

/-! ## The global factorization statement on the exact parameter image -/

/-- The parameter `x / φ(x)`. -/
noncomputable def ratioOf (curve : ℝ → ℝ) (x : ℝ) : ℝ :=
  x / curve x

/-- Nonzero real numbers, the natural source of the parameter map. -/
abbrev NonzeroReal := {x : ℝ // x ≠ 0}

/-- The exact image of the parameter map on nonzero real points. -/
noncomputable def ParamImage (curve : ℝ → ℝ) : Set ℝ :=
  Set.range (fun x : NonzeroReal => ratioOf curve x.1)

/-- The point of the parameter image represented by a nonzero real x. -/
noncomputable def imagePoint (curve : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    ParamImage curve :=
  ⟨ratioOf curve x, ⟨⟨x, hx⟩, rfl⟩⟩

/--
The exact global single-valued factorization asked for in the problem:
one function on the entire parameter image must work for all nonzero real x.
-/
def GloballyFactorsThroughRatio
    (F : ℝ → ℝ → ℝ) (curve : ℝ → ℝ) : Prop :=
  ∃ G : ParamImage curve → ℝ,
    ∀ (x : ℝ) (hx : x ≠ 0),
      G (imagePoint curve x hx) = F x (curve x)

/-! The two colliding parameter values. -/

lemma ratio_one :
    ratioOf φ 1 = -(1 : ℝ) / 4 := by
  norm_num [ratioOf, φ, s]

lemma ratio_three :
    ratioOf φ 3 = -(1 : ℝ) / 4 := by
  norm_num [ratioOf, φ, s]

lemma ratio_collision :
    ratioOf φ 1 = ratioOf φ 3 := by
  rw [ratio_one, ratio_three]

/-! The function values at the two colliding points. -/

lemma curve_value_one :
    f 1 (φ 1) = (4 : ℝ) / 3 := by
  norm_num [f, g, φ, s]

lemma curve_value_three :
    f 3 (φ 3) = 0 := by
  norm_num [f, g, φ, s]

/--
There is no set-theoretic single-valued function on the exact parameter image
which factors the restriction of `f` to the witnessing curve.
-/
theorem no_global_factorization :
    ¬ GloballyFactorsThroughRatio f φ := by
  rintro ⟨G, hG⟩
  have h1ne : (1 : ℝ) ≠ 0 := by norm_num
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have hp :
      imagePoint φ 1 h1ne = imagePoint φ 3 h3ne := by
    apply Subtype.ext
    exact ratio_collision
  have h1 := hG 1 h1ne
  have h3 := hG 3 h3ne
  rw [hp] at h1
  rw [curve_value_one] at h1
  rw [curve_value_three] at h3
  linarith

/-! ## Exact common zero set of the two equations -/

/-- The graph residual: it vanishes exactly on `y = φ x`. -/
noncomputable def D (x y : ℝ) : ℝ := y + x * (s x) ^ 2

lemma D_eq_zero_iff_curve (x y : ℝ) :
    D x y = 0 ↔ y = φ x := by
  simp only [D, φ]
  constructor <;> intro h <;> linarith

/-- A denominator-free form of the first equation. -/
lemma first_equation_scaled (x y : ℝ) :
    (x * fx x y + y * fy x y) * (2 * (s x) ^ 2) =
      -(x ^ 2 - 5) * D x y := by
  have hs := s_ne_zero x
  simp only [fx, fy, D]
  field_simp [hs]
  simp [s]
  ring

/-- A denominator-free form of the second equation. -/
lemma second_equation_scaled (x y : ℝ) :
    (4 * fx x y * fy x y - 1) * (s x) ^ 3 =
      -2 * (x - 2) * D x y := by
  have hs := s_ne_zero x
  simp only [fx, fy, D]
  field_simp [hs]
  simp [s]
  ring

/--
The simultaneous equations cut out exactly the graph of `φ`.
-/
theorem common_zero_set_exact (x y : ℝ) :
    (x * fx x y + y * fy x y = 0 ∧ 4 * fx x y * fy x y = 1) ↔
      y = φ x := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    have hfirst' : -(x ^ 2 - 5) * D x y = 0 := by
      rw [← first_equation_scaled]
      rw [hfirst]
      ring
    have hsecond' : -2 * (x - 2) * D x y = 0 := by
      rw [← second_equation_scaled]
      rw [hsecond]
      ring
    have hprod : (x - 2) * D x y = 0 := by
      nlinarith
    have hD : D x y = 0 := by
      rcases mul_eq_zero.mp hprod with hx | hD
      · have hx2 : x = 2 := by linarith
        subst x
        norm_num at hfirst'
        exact hfirst'
      · exact hD
    exact (D_eq_zero_iff_curve x y).mp hD
  · intro hy
    subst y
    constructor
    · rw [fx_on_curve_value, fy_on_curve_value]
      exact first_Infeld_equation x
    · rw [fx_on_curve_value, fy_on_curve_value]
      exact second_Infeld_equation x

/-! ## A symmetric family of collisions near the fold -/

lemma s_symmetric (t : ℝ) :
    s (2 - t) = s (2 + t) := by
  simp [s]

lemma ratio_formula (x : ℝ) (hx : x ≠ 0) :
    ratioOf φ x = -1 / (s x) ^ 2 := by
  have hs := s_ne_zero x
  simp only [ratioOf, φ]
  field_simp [hx, hs]

lemma ratio_symmetric (t : ℝ)
    (hleft : 2 - t ≠ 0) (hright : 2 + t ≠ 0) :
    ratioOf φ (2 - t) = ratioOf φ (2 + t) := by
  rw [ratio_formula (2 - t) hleft, ratio_formula (2 + t) hright,
    s_symmetric]

lemma curve_value_formula (x : ℝ) :
    f x (φ x) = 2 * x ^ 2 * (3 - x) / 3 := by
  have hs := s_ne_zero x
  simp only [f, g, φ]
  field_simp [hs]
  simp [s]
  ring

lemma symmetric_curve_value_difference (t : ℝ) :
    f (2 + t) (φ (2 + t)) - f (2 - t) (φ (2 - t)) =
      -4 * t ^ 3 / 3 := by
  rw [curve_value_formula, curve_value_formula]
  ring

lemma symmetric_curve_values_ne {t : ℝ} (ht : t ≠ 0) :
    f (2 - t) (φ (2 - t)) ≠ f (2 + t) (φ (2 + t)) := by
  intro hEq
  have hzero :
      f (2 + t) (φ (2 + t)) - f (2 - t) (φ (2 - t)) = 0 := by
    rw [hEq]
    ring
  have hdiff := symmetric_curve_value_difference t
  have ht3 : t ^ 3 = 0 := by
    nlinarith
  exact (pow_ne_zero 3 ht) ht3

/--
Every nonzero symmetric displacement which avoids the origin gives the same
ratio parameter at `2-t` and `2+t`, but two different curve values.
-/
theorem symmetric_fold_obstruction (t : ℝ)
    (ht : t ≠ 0) (hleft : 2 - t ≠ 0) (hright : 2 + t ≠ 0) :
    ratioOf φ (2 - t) = ratioOf φ (2 + t) ∧
      f (2 - t) (φ (2 - t)) ≠ f (2 + t) (φ (2 + t)) := by
  exact ⟨ratio_symmetric t hleft hright, symmetric_curve_values_ne ht⟩

/-! ## Optional strengthening: explicit partial derivatives everywhere -/

theorem partial_derivatives_everywhere (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f t y) (fx x y) x ∧
    HasDerivAt (fun t : ℝ => f x t) (fy x y) y :=
  ⟨hasDerivAt_f_x x y, hasDerivAt_f_y x y⟩

/-! ## Final bundled theorem -/

/--
A strict formal negative answer to Scottish Book Problem 125 under the global
single-valued interpretation.

It exhibits explicit `F` and `curve` such that:
* the two required partial derivatives exist and satisfy condition A at every x;
* the quotient parameter is well-defined for every nonzero x;
* the function is not in the excluded linear class;
* no single-valued function on the exact parameter image can factor the
  restriction to the curve.
-/
theorem scottishBook125_negative :
    ∃ (F : ℝ → ℝ → ℝ) (curve : ℝ → ℝ),
      SatisfiesConditionA F curve ∧
      (∀ x : ℝ, x ≠ 0 → curve x ≠ 0) ∧
      ¬ IsExcludedLinearCase F ∧
      ¬ GloballyFactorsThroughRatio F curve := by
  refine ⟨f, φ, satisfiesConditionA, ?_, f_not_excluded_linear,
    no_global_factorization⟩
  intro x hx
  exact φ_ne_zero hx

/--
A bundled version of all mathematical assertions retained in the revised
paper.
-/
theorem scottishBook125_paper_package :
    SatisfiesConditionA f φ ∧
    (∀ x : ℝ, x ≠ 0 → φ x ≠ 0) ∧
    ¬ IsExcludedLinearCase f ∧
    ¬ GloballyFactorsThroughRatio f φ ∧
    (∀ x y : ℝ,
      (x * fx x y + y * fy x y = 0 ∧ 4 * fx x y * fy x y = 1) ↔
        y = φ x) ∧
    (∀ t : ℝ, t ≠ 0 → 2 - t ≠ 0 → 2 + t ≠ 0 →
      ratioOf φ (2 - t) = ratioOf φ (2 + t) ∧
        f (2 - t) (φ (2 - t)) ≠ f (2 + t) (φ (2 + t))) := by
  refine ⟨satisfiesConditionA, ?_, f_not_excluded_linear,
    no_global_factorization, ?_, ?_⟩
  · intro x hx
    exact φ_ne_zero hx
  · intro x y
    exact common_zero_set_exact x y
  · intro t ht hleft hright
    exact symmetric_fold_obstruction t ht hleft hright

end Scottish125

#print axioms Scottish125.scottishBook125_negative
#print axioms Scottish125.scottishBook125_paper_package
