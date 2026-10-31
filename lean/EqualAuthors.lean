/-
Formalisation of `paper/main.tex`,
"Truly Every Author is First Author: Equal-Width Superimposition by Minimising
Visual Distortion".

Every theorem is named after the label it carries in the paper: `prop_split`,
`eq_cstar`, `eq_ratio`, `prop_width`, `eq_clamp`, `eq_measure_w` / `eq_measure_g`,
`eq_problem`.  The definitions keep the paper's symbols: `ω` (eq:width), `C`
(eq:cost), `K` (eq:stiffness), `sOpt` / `tOpt` (eq:split), `Wstar` (eq:wstar),
the variables `w`, `g`, `c`, `e`, `s`, `t`, `W`, and `lam` for the Lagrange
multiplier the paper writes as a bare lambda.
-/
import Mathlib

namespace EqualAuthors

noncomputable section

open Finset

/-- Definition (Name data), Section 2. -/
structure Name where
  /-- `w > 0`, the natural set width, as the font sets it. -/
  w : ℝ
  /-- `g`, the number of inter-character gaps. -/
  g : ℕ
  hw : 0 < w

namespace Name

variable (N : Name)

/-- `c = g + 1`, the number of characters. -/
def c : ℝ := (N.g : ℝ) + 1

/-- `e = w / c`, the mean character width, the natural length scale of the name. -/
def e : ℝ := N.w / N.c

lemma c_pos : 0 < N.c := by
  have h : (0 : ℝ) ≤ (N.g : ℝ) := Nat.cast_nonneg _
  unfold c; linarith

lemma e_pos : 0 < N.e := div_pos N.hw N.c_pos

lemma e_ne_zero : N.e ≠ 0 := N.e_pos.ne'

/-- "`g e ≈ w`, exact up to one character": precisely, `g e = w - e`. -/
lemma g_mul_e : (N.g : ℝ) * N.e = N.w - N.e := by
  have hc := N.c_pos.ne'
  have hg : (N.g : ℝ) = N.c - 1 := by unfold c; ring
  rw [hg, e]; field_simp

/-- Equation (eq:width), the realised width: `ω(s,t) = s w + g t`. -/
def ω (s t : ℝ) : ℝ := s * N.w + (N.g : ℝ) * t

/-- Equation (eq:cost), the ugliness of a name:
`C(s,t) = α/2 (s-1)² + β/2 (t/e)²`. -/
def C (α β s t : ℝ) : ℝ := α / 2 * (s - 1) ^ 2 + β / 2 * (t / N.e) ^ 2

/-- "Both terms vanish at the undistorted setting `(s,t) = (1,0)`." -/
@[simp] lemma C_undistorted (α β : ℝ) : N.C α β 1 0 = 0 := by simp [C]

lemma C_nonneg (α β s t : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) : 0 ≤ N.C α β s t := by
  have h₁ : 0 ≤ α / 2 * (s - 1) ^ 2 := by positivity
  have h₂ : 0 ≤ β / 2 * (t / N.e) ^ 2 := by positivity
  simp only [C]; linarith

/-- Equation (eq:stiffness): `K = w²/α + g² e²/β`. -/
def K (α β : ℝ) : ℝ := N.w ^ 2 / α + (N.g : ℝ) ^ 2 * N.e ^ 2 / β

/-- "`K > 0`". -/
lemma K_pos (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : 0 < N.K α β := by
  have h₁ : 0 < N.w ^ 2 / α := div_pos (pow_pos N.hw 2) hα
  have h₂ : 0 ≤ (N.g : ℝ) ^ 2 * N.e ^ 2 / β := by positivity
  simp only [K]; linarith

lemma K_ne_zero (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : N.K α β ≠ 0 :=
  (N.K_pos α β hα hβ).ne'

/-! ### Section 3.1, the optimal split for a fixed width -/

/-- The Lagrange multiplier of Proposition 1, `λ = (W - w)/K`. -/
def lam (α β W : ℝ) : ℝ := (W - N.w) / N.K α β

/-- Equation (eq:split), the scale: `s = 1 + λ w / α`. -/
def sOpt (α β W : ℝ) : ℝ := 1 + N.lam α β W * N.w / α

/-- Equation (eq:split), the tracking: `t = λ g e² / β`. -/
def tOpt (α β W : ℝ) : ℝ := N.lam α β W * (N.g : ℝ) * N.e ^ 2 / β

lemma lam_mul_K (α β W : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    N.lam α β W * N.K α β = W - N.w :=
  div_mul_cancel₀ _ (N.K_ne_zero α β hα hβ)

/-- Stationarity in the scale, `α (s - 1) = λ w`. -/
lemma stationarity_s (α β W : ℝ) (hα : 0 < α) :
    α * (N.sOpt α β W - 1) = N.lam α β W * N.w := by
  simp only [sOpt, add_sub_cancel_left]
  field_simp

/-- Stationarity in the tracking, `β t / e² = λ g`. -/
lemma stationarity_t (α β W : ℝ) (hβ : 0 < β) :
    β * N.tOpt α β W / N.e ^ 2 = N.lam α β W * (N.g : ℝ) := by
  have he := N.e_ne_zero
  simp only [tOpt]
  field_simp

/-- Equation (eq:split) is feasible: it realises the target width `W`. -/
lemma omega_split (α β W : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    N.ω (N.sOpt α β W) (N.tOpt α β W) = W := by
  have hK := N.lam_mul_K α β W hα hβ
  have he := N.e_ne_zero
  have h : N.ω (N.sOpt α β W) (N.tOpt α β W) = N.w + N.lam α β W * N.K α β := by
    simp only [ω, sOpt, tOpt, K]
    field_simp
    ring
  rw [h, hK]; ring

/-- The heart of Proposition 1 (prop:split): along the feasible line `ω = W`
the cost is its value at (eq:split) plus an exact positive definite quadratic in
the displacement.  Minimality, uniqueness and the KKT argument of the paper all
follow from this single identity. -/
theorem C_sub_C_split (α β W : ℝ) (hα : 0 < α) (hβ : 0 < β) (s' t' : ℝ)
    (h : N.ω s' t' = W) :
    N.C α β s' t' - N.C α β (N.sOpt α β W) (N.tOpt α β W)
      = α / 2 * (s' - N.sOpt α β W) ^ 2
        + β / 2 * ((t' - N.tOpt α β W) / N.e) ^ 2 := by
  have hs := N.stationarity_s α β W hα
  have ht := N.stationarity_t α β W hβ
  have hcon : N.w * (s' - N.sOpt α β W) + (N.g : ℝ) * (t' - N.tOpt α β W) = 0 := by
    have hfeas := N.omega_split α β W hα hβ
    simp only [ω] at h hfeas
    linarith
  simp only [C]
  linear_combination (s' - N.sOpt α β W) * hs + (t' - N.tOpt α β W) * ht
    + N.lam α β W * hcon

/-- Proposition 1 (prop:split): for a fixed common width `W`, the pair
(eq:split) minimises the cost (eq:cost) subject to the width constraint. -/
theorem prop_split (α β W : ℝ) (hα : 0 < α) (hβ : 0 < β) (s' t' : ℝ)
    (h : N.ω s' t' = W) :
    N.C α β (N.sOpt α β W) (N.tOpt α β W) ≤ N.C α β s' t' := by
  have hid := N.C_sub_C_split α β W hα hβ s' t' h
  have h₁ : 0 ≤ α / 2 * (s' - N.sOpt α β W) ^ 2 := by positivity
  have h₂ : 0 ≤ β / 2 * ((t' - N.tOpt α β W) / N.e) ^ 2 := by positivity
  linarith

/-- Proposition 1 (prop:split): "the *unique* minimiser". -/
theorem prop_split_unique (α β W : ℝ) (hα : 0 < α) (hβ : 0 < β) (s' t' : ℝ)
    (h : N.ω s' t' = W)
    (hopt : N.C α β s' t' ≤ N.C α β (N.sOpt α β W) (N.tOpt α β W)) :
    s' = N.sOpt α β W ∧ t' = N.tOpt α β W := by
  have hid := N.C_sub_C_split α β W hα hβ s' t' h
  have h₁ : 0 ≤ α / 2 * (s' - N.sOpt α β W) ^ 2 := by positivity
  have h₂ : 0 ≤ β / 2 * ((t' - N.tOpt α β W) / N.e) ^ 2 := by positivity
  have he := N.e_ne_zero
  refine ⟨?_, ?_⟩
  · have hsq : (s' - N.sOpt α β W) ^ 2 = 0 := by nlinarith
    have := sq_eq_zero_iff.mp hsq
    linarith
  · have hsq : ((t' - N.tOpt α β W) / N.e) ^ 2 = 0 := by nlinarith
    have hz := sq_eq_zero_iff.mp hsq
    rcases div_eq_zero_iff.mp hz with h' | h'
    · linarith
    · exact absurd h' he

/-- Equation (eq:cstar): the optimal value is `C⋆(W) = (W - w)²/(2K)`. -/
theorem eq_cstar (α β W : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    N.C α β (N.sOpt α β W) (N.tOpt α β W) = (W - N.w) ^ 2 / (2 * N.K α β) := by
  have hK := N.K_ne_zero α β hα hβ
  have he := N.e_ne_zero
  have hlam := N.lam_mul_K α β W hα hβ
  have hC : N.C α β (N.sOpt α β W) (N.tOpt α β W) = N.lam α β W ^ 2 * N.K α β / 2 := by
    simp only [C, sOpt, tOpt, K, add_sub_cancel_left]
    field_simp
  rw [hC, ← hlam]
  field_simp

/-- Equation (eq:ratio): the two distortions are used in the fixed ratio
`g t / ((s-1) w) = α g² e² / (β w²)`, independently of `W`. -/
theorem eq_ratio (α β W : ℝ) (hα : 0 < α) (hβ : 0 < β) (hlam : N.lam α β W ≠ 0) :
    (N.g : ℝ) * N.tOpt α β W / ((N.sOpt α β W - 1) * N.w)
      = α * (N.g : ℝ) ^ 2 * N.e ^ 2 / (β * N.w ^ 2) := by
  have hw := N.hw.ne'
  simp only [sOpt, tOpt, add_sub_cancel_left]
  field_simp

/-! ### Section 3.3, feasibility and clamping -/

/-- Equation (eq:clamp): with the scale pinned at `ŝ`, the tracking that
re-solves the width constraint, `t̂ = (W - ŝ w)/g`. -/
def tHat (W ŝ : ℝ) : ℝ := (W - ŝ * N.w) / (N.g : ℝ)

lemma g_ne_zero (hg : 1 ≤ N.g) : ((N.g : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)

/-- (eq:clamp) stays feasible: re-solving for the tracking restores the width. -/
lemma omega_tHat (W : ℝ) (hg : 1 ≤ N.g) (ŝ : ℝ) : N.ω ŝ (N.tHat W ŝ) = W := by
  have hg' := N.g_ne_zero hg
  simp only [ω, tHat]
  field_simp
  ring

lemma tHat_sOpt (α β W : ℝ) (hg : 1 ≤ N.g) (hα : 0 < α) (hβ : 0 < β) :
    N.tHat W (N.sOpt α β W) = N.tOpt α β W := by
  have hg' := N.g_ne_zero hg
  have hfeas := N.omega_split α β W hα hβ
  simp only [ω] at hfeas
  simp only [tHat]
  field_simp
  linarith

/-- "Along the width constraint the cost becomes a convex quadratic in `s`
alone, centred at the unconstrained optimum" of (eq:split). -/
theorem phi_sub (α β W : ℝ) (hg : 1 ≤ N.g) (hα : 0 < α) (hβ : 0 < β) (s' : ℝ) :
    N.C α β s' (N.tHat W s') - N.C α β (N.sOpt α β W) (N.tOpt α β W)
      = (α + β * N.w ^ 2 / ((N.g : ℝ) ^ 2 * N.e ^ 2)) / 2 * (s' - N.sOpt α β W) ^ 2 := by
  have hg' := N.g_ne_zero hg
  have he := N.e_ne_zero
  have hid := N.C_sub_C_split α β W hα hβ s' (N.tHat W s') (N.omega_tHat W hg s')
  rw [hid, ← N.tHat_sOpt α β W hg hα hβ]
  have hv : N.tHat W s' - N.tHat W (N.sOpt α β W)
      = -(N.w * (s' - N.sOpt α β W) / (N.g : ℝ)) := by
    simp only [tHat]; field_simp; ring
  rw [hv]
  field_simp

/-- "This projection is exact."  Proposition 1 clamped to the typographic box
`s ∈ [smin, smax]`: the optimum of the box-constrained problem is the projection
of the unconstrained scale, with the tracking re-solved by (eq:clamp). -/
theorem eq_clamp (α β W : ℝ) (hg : 1 ≤ N.g) (hα : 0 < α) (hβ : 0 < β)
    (smin smax : ℝ) (hbox : smin ≤ smax) (s' : ℝ) (hs' : s' ∈ Set.Icc smin smax) :
    N.C α β (max smin (min smax (N.sOpt α β W)))
        (N.tHat W (max smin (min smax (N.sOpt α β W))))
      ≤ N.C α β s' (N.tHat W s') := by
  obtain ⟨h1, h2⟩ := hs'
  set x := N.sOpt α β W with hx
  have hg' := N.g_ne_zero hg
  have he := N.e_ne_zero
  have hM : 0 ≤ (α + β * N.w ^ 2 / ((N.g : ℝ) ^ 2 * N.e ^ 2)) / 2 := by
    have : 0 ≤ β * N.w ^ 2 / ((N.g : ℝ) ^ 2 * N.e ^ 2) := by positivity
    linarith
  have hproj : (max smin (min smax x) - x) ^ 2 ≤ (s' - x) ^ 2 := by
    rcases le_total x smin with h | h
    · rw [min_eq_right (h.trans hbox), max_eq_left h]; nlinarith
    · rcases le_total x smax with h' | h'
      · rw [min_eq_right h', max_eq_right h]; nlinarith
      · rw [min_eq_left h', max_eq_right hbox]; nlinarith
  have e1 := N.phi_sub α β W hg hα hβ (max smin (min smax x))
  have e2 := N.phi_sub α β W hg hα hβ s'
  nlinarith [mul_le_mul_of_nonneg_left hproj hM]

/-- "Single-character names (`g = 0`) have no gaps to track and must take
`s = W / w` regardless of the bounds; the model degenerates gracefully and stays
feasible." -/
theorem omega_of_g_eq_zero (W : ℝ) (hg : N.g = 0) (s t : ℝ) :
    N.ω s t = W ↔ s = W / N.w := by
  have hw := N.hw.ne'
  simp only [ω, hg, Nat.cast_zero, zero_mul, add_zero]
  rw [eq_div_iff hw]

/-! ### Section 4, implementation -/

/-- Equation (eq:measure), first half: `w = ω(1,0)`. -/
@[simp] theorem eq_measure_w : N.ω 1 0 = N.w := by simp [ω]

/-- Equation (eq:measure), second half.  "Since (eq:width) is affine in `t`,
that difference quotient is exact", so two box measurements recover `g`, and
with it `c = g + 1` and `e = w/c`, without ever parsing the name. -/
theorem eq_measure_g (em : ℝ) (hem : em ≠ 0) :
    (N.ω 1 em - N.ω 1 0) / em = (N.g : ℝ) := by
  simp only [ω]
  field_simp
  ring

/-- Microtype quantises the tracking `τ = t/s` it is handed to whole thousandths
of an em; re-solving the scale from `s (w + g τ) = W` keeps the realised width,
with realised tracking `t = s τ`, exactly `W⋆`. -/
theorem quantised_scale_exact (W τ : ℝ) (h : N.w + (N.g : ℝ) * τ ≠ 0) :
    N.ω (W / (N.w + (N.g : ℝ) * τ)) (W / (N.w + (N.g : ℝ) * τ) * τ) = W := by
  simp only [ω]
  rw [show W / (N.w + (N.g : ℝ) * τ) * N.w + (N.g : ℝ) * (W / (N.w + (N.g : ℝ) * τ) * τ)
      = W / (N.w + (N.g : ℝ) * τ) * (N.w + (N.g : ℝ) * τ) by ring]
  exact div_mul_cancel₀ W h

/-- "Typst applies tracking inside the scaled coordinate frame, so the tracking
handed to the engine is `t/s`; the realised width is then `s w + g t` as in
(eq:width)." -/
theorem typst_frame (s t : ℝ) (hs : s ≠ 0) :
    s * (N.w + (N.g : ℝ) * (t / s)) = N.ω s t := by
  simp only [ω]
  field_simp

end Name

/-! ### Section 3.2, the optimal common width -/

variable {ι : Type*} (S : Finset ι) (Ns : ι → Name) (α β : ℝ)

/-- The outer objective `F(W) = Σᵢ C⋆ᵢ(W)` of Proposition 2. -/
def F (W : ℝ) : ℝ := ∑ i ∈ S, (W - (Ns i).w) ^ 2 / (2 * (Ns i).K α β)

/-- The denominator of (eq:wstar), `Σᵢ 1/Kᵢ`. -/
def A : ℝ := ∑ i ∈ S, 1 / (Ns i).K α β

/-- The numerator of (eq:wstar), `Σᵢ wᵢ/Kᵢ`. -/
def B : ℝ := ∑ i ∈ S, (Ns i).w / (Ns i).K α β

/-- Equation (eq:wstar): the stiffness-weighted mean of the natural widths. -/
def Wstar : ℝ := B S Ns α β / A S Ns α β

lemma A_pos (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β) : 0 < A S Ns α β :=
  Finset.sum_pos (fun i _ => by have := (Ns i).K_pos α β hα hβ; positivity) hS

lemma B_eq (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β) :
    B S Ns α β = Wstar S Ns α β * A S Ns α β := by
  have hA := (A_pos S Ns α β hS hα hβ).ne'
  simp only [Wstar]
  field_simp

/-- The excess of the outer objective over its value at `W⋆`: as in
Proposition 1 it is an exact positive definite quadratic, which is both the
strict convexity `F'' = Σ 1/Kᵢ > 0` of the paper's proof and its uniqueness
claim. -/
theorem F_sub_F_Wstar (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β) (W : ℝ) :
    F S Ns α β W - F S Ns α β (Wstar S Ns α β)
      = A S Ns α β / 2 * (W - Wstar S Ns α β) ^ 2 := by
  set Ws := Wstar S Ns α β with hWs
  have hstep : ∀ i ∈ S,
      (W - (Ns i).w) ^ 2 / (2 * (Ns i).K α β)
          - (Ws - (Ns i).w) ^ 2 / (2 * (Ns i).K α β)
        = 1 / (Ns i).K α β * ((W - Ws) ^ 2 / 2)
          + (W - Ws) * (Ws * (1 / (Ns i).K α β) - (Ns i).w / (Ns i).K α β) := by
    intro i _
    have hK := (Ns i).K_ne_zero α β hα hβ
    field_simp
    ring
  have hsum1 : ∑ i ∈ S, 1 / (Ns i).K α β * ((W - Ws) ^ 2 / 2)
      = A S Ns α β * ((W - Ws) ^ 2 / 2) := by
    rw [← Finset.sum_mul]; simp only [A]
  have hsum2 : ∑ i ∈ S, (W - Ws) * (Ws * (1 / (Ns i).K α β) - (Ns i).w / (Ns i).K α β)
      = (W - Ws) * (Ws * A S Ns α β - B S Ns α β) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [A, B]
  calc F S Ns α β W - F S Ns α β Ws
      = ∑ i ∈ S, ((W - (Ns i).w) ^ 2 / (2 * (Ns i).K α β)
            - (Ws - (Ns i).w) ^ 2 / (2 * (Ns i).K α β)) := by
        simp only [F, Finset.sum_sub_distrib]
    _ = ∑ i ∈ S, (1 / (Ns i).K α β * ((W - Ws) ^ 2 / 2)
            + (W - Ws) * (Ws * (1 / (Ns i).K α β) - (Ns i).w / (Ns i).K α β)) :=
        Finset.sum_congr rfl hstep
    _ = A S Ns α β * ((W - Ws) ^ 2 / 2)
          + (W - Ws) * (Ws * A S Ns α β - B S Ns α β) := by
        rw [Finset.sum_add_distrib, hsum1, hsum2]
    _ = A S Ns α β / 2 * (W - Ws) ^ 2 := by
        rw [B_eq S Ns α β hS hα hβ, ← hWs]; ring

/-- Proposition 2 (prop:width): `W⋆` of (eq:wstar) minimises the total
distortion. -/
theorem prop_width (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β) (W : ℝ) :
    F S Ns α β (Wstar S Ns α β) ≤ F S Ns α β W := by
  have h := F_sub_F_Wstar S Ns α β hS hα hβ W
  have hA := A_pos S Ns α β hS hα hβ
  nlinarith [sq_nonneg (W - Wstar S Ns α β)]

/-- Proposition 2 (prop:width): "and it is unique". -/
theorem prop_width_unique (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β) (W : ℝ)
    (hopt : F S Ns α β W ≤ F S Ns α β (Wstar S Ns α β)) : W = Wstar S Ns α β := by
  have h := F_sub_F_Wstar S Ns α β hS hα hβ W
  have hA := A_pos S Ns α β hS hα hβ
  have hsq : (W - Wstar S Ns α β) ^ 2 = 0 := by nlinarith
  have := sq_eq_zero_iff.mp hsq
  linarith

/-! #### The corollary of Section 3.2 -/

lemma Wstar_le_sup (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β) :
    Wstar S Ns α β ≤ S.sup' hS fun i => (Ns i).w := by
  have hA := A_pos S Ns α β hS hα hβ
  rw [Wstar, div_le_iff₀ hA]
  calc B S Ns α β = ∑ i ∈ S, (Ns i).w * (1 / (Ns i).K α β) := by
        simp only [B, mul_one_div]
    _ ≤ ∑ i ∈ S, (S.sup' hS fun i => (Ns i).w) * (1 / (Ns i).K α β) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hK : (0:ℝ) < 1 / (Ns i).K α β := by
          have := (Ns i).K_pos α β hα hβ; positivity
        exact mul_le_mul_of_nonneg_right (Finset.le_sup' (fun i => (Ns i).w) hi) hK.le
    _ = (S.sup' hS fun i => (Ns i).w) * A S Ns α β := by
        rw [← Finset.mul_sum]; simp only [A]

lemma inf_le_Wstar (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β) :
    (S.inf' hS fun i => (Ns i).w) ≤ Wstar S Ns α β := by
  have hA := A_pos S Ns α β hS hα hβ
  rw [Wstar, le_div_iff₀ hA]
  calc (S.inf' hS fun i => (Ns i).w) * A S Ns α β
      = ∑ i ∈ S, (S.inf' hS fun i => (Ns i).w) * (1 / (Ns i).K α β) := by
        rw [← Finset.mul_sum]; simp only [A]
    _ ≤ ∑ i ∈ S, (Ns i).w * (1 / (Ns i).K α β) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hK : (0:ℝ) < 1 / (Ns i).K α β := by
          have := (Ns i).K_pos α β hα hβ; positivity
        exact mul_le_mul_of_nonneg_right (Finset.inf'_le (fun i => (Ns i).w) hi) hK.le
    _ = B S Ns α β := by simp only [B, mul_one_div]

/-- The corollary of Section 3.2: `minᵢ wᵢ ≤ W⋆ ≤ maxᵢ wᵢ`. -/
theorem Wstar_mem_Icc (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β) :
    Wstar S Ns α β ∈
      Set.Icc (S.inf' hS fun i => (Ns i).w) (S.sup' hS fun i => (Ns i).w) :=
  ⟨inf_le_Wstar S Ns α β hS hα hβ, Wstar_le_sup S Ns α β hS hα hβ⟩

/-- The corollary of Section 3.2, "with equality only if all `wᵢ` coincide",
at the upper end. -/
theorem Wstar_eq_sup_imp (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β)
    (h : Wstar S Ns α β = S.sup' hS fun i => (Ns i).w) :
    ∀ i ∈ S, (Ns i).w = S.sup' hS fun i => (Ns i).w := by
  set M := S.sup' hS fun i => (Ns i).w with hM
  have hzero : ∑ i ∈ S, (M - (Ns i).w) / (Ns i).K α β = 0 := by
    have hsplit : ∑ i ∈ S, (M - (Ns i).w) / (Ns i).K α β
        = M * A S Ns α β - B S Ns α β := by
      simp only [A, B, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, B_eq S Ns α β hS hα hβ, h]; ring
  have hnn : ∀ i ∈ S, 0 ≤ (M - (Ns i).w) / (Ns i).K α β := fun i hi => by
    have hK := (Ns i).K_pos α β hα hβ
    have hle : (Ns i).w ≤ M := Finset.le_sup' (fun i => (Ns i).w) hi
    exact div_nonneg (by linarith) hK.le
  intro i hi
  have hzi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero i hi
  have hK := (Ns i).K_ne_zero α β hα hβ
  rw [div_eq_zero_iff] at hzi
  rcases hzi with h' | h'
  · linarith
  · exact absurd h' hK

/-- The corollary of Section 3.2, "with equality only if all `wᵢ` coincide",
at the lower end. -/
theorem Wstar_eq_inf_imp (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β)
    (h : Wstar S Ns α β = S.inf' hS fun i => (Ns i).w) :
    ∀ i ∈ S, (Ns i).w = S.inf' hS fun i => (Ns i).w := by
  set m := S.inf' hS fun i => (Ns i).w with hm
  have hzero : ∑ i ∈ S, ((Ns i).w - m) / (Ns i).K α β = 0 := by
    have hsplit : ∑ i ∈ S, ((Ns i).w - m) / (Ns i).K α β
        = B S Ns α β - m * A S Ns α β := by
      simp only [A, B, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, B_eq S Ns α β hS hα hβ, h]; ring
  have hnn : ∀ i ∈ S, 0 ≤ ((Ns i).w - m) / (Ns i).K α β := fun i hi => by
    have hK := (Ns i).K_pos α β hα hβ
    have hle : m ≤ (Ns i).w := Finset.inf'_le (fun i => (Ns i).w) hi
    exact div_nonneg (by linarith) hK.le
  intro i hi
  have hzi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero i hi
  have hK := (Ns i).K_ne_zero α β hα hβ
  rw [div_eq_zero_iff] at hzi
  rcases hzi with h' | h'
  · linarith
  · exact absurd h' hK

/-- Definition (Equal-width superimposition problem), (eq:problem), solved:
the widths `W⋆` and the distortions (eq:split) are feasible and optimal for the
joint problem over all names and all common widths. -/
theorem eq_problem (hS : S.Nonempty) (hα : 0 < α) (hβ : 0 < β) :
    (∀ i ∈ S, (Ns i).ω ((Ns i).sOpt α β (Wstar S Ns α β))
        ((Ns i).tOpt α β (Wstar S Ns α β)) = Wstar S Ns α β)
    ∧ ∀ (W : ℝ) (s t : ι → ℝ), (∀ i ∈ S, (Ns i).ω (s i) (t i) = W) →
        ∑ i ∈ S, (Ns i).C α β ((Ns i).sOpt α β (Wstar S Ns α β))
            ((Ns i).tOpt α β (Wstar S Ns α β))
          ≤ ∑ i ∈ S, (Ns i).C α β (s i) (t i) := by
  refine ⟨fun i _ => (Ns i).omega_split α β _ hα hβ, fun W s t hfeas => ?_⟩
  have hF : ∀ V : ℝ, ∑ i ∈ S, (Ns i).C α β ((Ns i).sOpt α β V) ((Ns i).tOpt α β V)
      = F S Ns α β V := fun V =>
    Finset.sum_congr rfl fun i _ => (Ns i).eq_cstar α β V hα hβ
  calc ∑ i ∈ S, (Ns i).C α β ((Ns i).sOpt α β (Wstar S Ns α β))
          ((Ns i).tOpt α β (Wstar S Ns α β))
      = F S Ns α β (Wstar S Ns α β) := hF _
    _ ≤ F S Ns α β W := prop_width S Ns α β hS hα hβ W
    _ = ∑ i ∈ S, (Ns i).C α β ((Ns i).sOpt α β W) ((Ns i).tOpt α β W) := (hF W).symm
    _ ≤ ∑ i ∈ S, (Ns i).C α β (s i) (t i) :=
        Finset.sum_le_sum fun i hi => (Ns i).prop_split α β W hα hβ _ _ (hfeas i hi)

/-! ### Section 1, what the standard is for -/

/-- "If Yu Liu and Martin L. Demaine are overprinted, the shorter name is
contained in the longer one."  Superimposition pins both names to a common
origin, so the ink of a name is the interval `[0, ω]` and width alone recovers a
ranking. -/
theorem containment (M N : Name) (s t s' t' : ℝ) (h : M.ω s t ≤ N.ω s' t') :
    Set.Icc (0 : ℝ) (M.ω s t) ⊆ Set.Icc (0 : ℝ) (N.ω s' t') :=
  Set.Icc_subset_Icc le_rfl h

/-- The loophole is closed: any two names solving (eq:problem) cover exactly the
same interval, so no containment, and hence no ranking, survives. -/
theorem no_containment (M N : Name) (s t s' t' W : ℝ)
    (hM : M.ω s t = W) (hN : N.ω s' t' = W) :
    Set.Icc (0 : ℝ) (M.ω s t) = Set.Icc (0 : ℝ) (N.ω s' t') := by
  rw [hM, hN]

end

end EqualAuthors
