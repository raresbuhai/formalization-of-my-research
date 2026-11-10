module

public import ABBKS26.Common.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Expand

/-! Coefficient estimates for nonnegative homogeneous quartics. -/

@[expose] public section

namespace ABBKS26.Centered.PolyAux

open Common MvPolynomial
open scoped BigOperators

noncomputable section

private def exponent (a b c e : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c + Finsupp.single 3 e

private theorem exponent_inj (a b c e a' b' c' e' : ℕ) :
    exponent a b c e = exponent a' b' c' e' ↔
      a = a' ∧ b = b' ∧ c = c' ∧ e = e' := by
  constructor
  · intro h
    have h0 := congrArg (fun x ↦ x 0) h
    have h1 := congrArg (fun x ↦ x 1) h
    have h2 := congrArg (fun x ↦ x 2) h
    have h3 := congrArg (fun x ↦ x 3) h
    simp only [exponent, Finsupp.add_apply, Finsupp.single_apply, Fin.reduceEq,
      ↓reduceIte, add_zero, zero_add] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

private def exponents : Finset (Fin 4 →₀ ℕ) :=
  {exponent 0 0 0 4,
    exponent 0 0 1 3,
    exponent 0 0 2 2,
    exponent 0 0 3 1,
    exponent 0 0 4 0,
    exponent 0 1 0 3,
    exponent 0 1 1 2,
    exponent 0 1 2 1,
    exponent 0 1 3 0,
    exponent 0 2 0 2,
    exponent 0 2 1 1,
    exponent 0 2 2 0,
    exponent 0 3 0 1,
    exponent 0 3 1 0,
    exponent 0 4 0 0,
    exponent 1 0 0 3,
    exponent 1 0 1 2,
    exponent 1 0 2 1,
    exponent 1 0 3 0,
    exponent 1 1 0 2,
    exponent 1 1 1 1,
    exponent 1 1 2 0,
    exponent 1 2 0 1,
    exponent 1 2 1 0,
    exponent 1 3 0 0,
    exponent 2 0 0 2,
    exponent 2 0 1 1,
    exponent 2 0 2 0,
    exponent 2 1 0 1,
    exponent 2 1 1 0,
    exponent 2 2 0 0,
    exponent 3 0 0 1,
    exponent 3 0 1 0,
    exponent 3 1 0 0,
    exponent 4 0 0 0}

private theorem member_0004 : exponent 0 0 0 4 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inl True.intro

private theorem member_0013 : exponent 0 0 1 3 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inl True.intro)

private theorem member_0022 : exponent 0 0 2 2 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inl True.intro))

private theorem member_0031 : exponent 0 0 3 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inl True.intro)))

private theorem member_0040 : exponent 0 0 4 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))

private theorem member_0103 : exponent 0 1 0 3 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))

private theorem member_0112 : exponent 0 1 1 2 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))

private theorem member_0121 : exponent 0 1 2 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))

private theorem member_0130 : exponent 0 1 3 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))

private theorem member_0202 : exponent 0 2 0 2 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro
    )))))))))

private theorem member_0211 : exponent 0 2 1 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inl True.intro))))))))))

private theorem member_0220 : exponent 0 2 2 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inl True.intro)))))))))))

private theorem member_0301 : exponent 0 3 0 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inl True.intro))))))))))))

private theorem member_0310 : exponent 0 3 1 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))

private theorem member_0400 : exponent 0 4 0 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))

private theorem member_1003 : exponent 1 0 0 3 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))

private theorem member_1012 : exponent 1 0 1 2 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))

private theorem member_1021 : exponent 1 0 2 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))

private theorem member_1030 : exponent 1 0 3 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro
    ))))))))))))))))))

private theorem member_1102 : exponent 1 1 0 2 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inl True.intro)))))))))))))))))))

private theorem member_1111 : exponent 1 1 1 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inl True.intro))))))))))))))))))))

private theorem member_1120 : exponent 1 1 2 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inl True.intro)))))))))))))))))))))

private theorem member_1201 : exponent 1 2 0 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inl True.intro))))))))))))))))))))))

private theorem member_1210 : exponent 1 2 1 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))

private theorem member_1300 : exponent 1 3 0 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))

private theorem member_2002 : exponent 2 0 0 2 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))

private theorem member_2011 : exponent 2 0 1 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))

private theorem member_2020 : exponent 2 0 2 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))

private theorem member_2101 : exponent 2 1 0 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro
    ))))))))))))))))))))))))))))

private theorem member_2110 : exponent 2 1 1 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inl True.intro)))))))))))))))))))))))))))))

private theorem member_2200 : exponent 2 2 0 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inl True.intro))))))))))))))))))))))))))))))

private theorem member_3001 : exponent 3 0 0 1 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inl True.intro)))))))))))))))))))))))))))))))

private theorem member_3010 : exponent 3 0 1 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inl True.intro))))))))))))))))))))))))))))))))

private theorem member_3100 : exponent 3 1 0 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))

private theorem member_4000 : exponent 4 0 0 0 ∈ exponents := by
  simp only [exponents, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
    Or.inr (Or.inr (True.intro))))))))))))))))))))))))))))))))))

private theorem mem_exponents_0 (b c e : ℕ) (h : 0 + b + c + e = 4) :
    exponent 0 b c e ∈ exponents := by
  have hb : b ≤ 4 := by omega
  interval_cases b
  · have hc : c ≤ 4 := by omega
    interval_cases c
    · have he : e = 4 := by omega
      subst e
      exact member_0004
    · have he : e = 3 := by omega
      subst e
      exact member_0013
    · have he : e = 2 := by omega
      subst e
      exact member_0022
    · have he : e = 1 := by omega
      subst e
      exact member_0031
    · have he : e = 0 := by omega
      subst e
      exact member_0040
  · have hc : c ≤ 3 := by omega
    interval_cases c
    · have he : e = 3 := by omega
      subst e
      exact member_0103
    · have he : e = 2 := by omega
      subst e
      exact member_0112
    · have he : e = 1 := by omega
      subst e
      exact member_0121
    · have he : e = 0 := by omega
      subst e
      exact member_0130
  · have hc : c ≤ 2 := by omega
    interval_cases c
    · have he : e = 2 := by omega
      subst e
      exact member_0202
    · have he : e = 1 := by omega
      subst e
      exact member_0211
    · have he : e = 0 := by omega
      subst e
      exact member_0220
  · have hc : c ≤ 1 := by omega
    interval_cases c
    · have he : e = 1 := by omega
      subst e
      exact member_0301
    · have he : e = 0 := by omega
      subst e
      exact member_0310
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · have he : e = 0 := by omega
      subst e
      exact member_0400

private theorem mem_exponents_1 (b c e : ℕ) (h : 1 + b + c + e = 4) :
    exponent 1 b c e ∈ exponents := by
  have hb : b ≤ 3 := by omega
  interval_cases b
  · have hc : c ≤ 3 := by omega
    interval_cases c
    · have he : e = 3 := by omega
      subst e
      exact member_1003
    · have he : e = 2 := by omega
      subst e
      exact member_1012
    · have he : e = 1 := by omega
      subst e
      exact member_1021
    · have he : e = 0 := by omega
      subst e
      exact member_1030
  · have hc : c ≤ 2 := by omega
    interval_cases c
    · have he : e = 2 := by omega
      subst e
      exact member_1102
    · have he : e = 1 := by omega
      subst e
      exact member_1111
    · have he : e = 0 := by omega
      subst e
      exact member_1120
  · have hc : c ≤ 1 := by omega
    interval_cases c
    · have he : e = 1 := by omega
      subst e
      exact member_1201
    · have he : e = 0 := by omega
      subst e
      exact member_1210
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · have he : e = 0 := by omega
      subst e
      exact member_1300

private theorem mem_exponents_2 (b c e : ℕ) (h : 2 + b + c + e = 4) :
    exponent 2 b c e ∈ exponents := by
  have hb : b ≤ 2 := by omega
  interval_cases b
  · have hc : c ≤ 2 := by omega
    interval_cases c
    · have he : e = 2 := by omega
      subst e
      exact member_2002
    · have he : e = 1 := by omega
      subst e
      exact member_2011
    · have he : e = 0 := by omega
      subst e
      exact member_2020
  · have hc : c ≤ 1 := by omega
    interval_cases c
    · have he : e = 1 := by omega
      subst e
      exact member_2101
    · have he : e = 0 := by omega
      subst e
      exact member_2110
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · have he : e = 0 := by omega
      subst e
      exact member_2200

private theorem mem_exponents_3 (b c e : ℕ) (h : 3 + b + c + e = 4) :
    exponent 3 b c e ∈ exponents := by
  have hb : b ≤ 1 := by omega
  interval_cases b
  · have hc : c ≤ 1 := by omega
    interval_cases c
    · have he : e = 1 := by omega
      subst e
      exact member_3001
    · have he : e = 0 := by omega
      subst e
      exact member_3010
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · have he : e = 0 := by omega
      subst e
      exact member_3100

private theorem mem_exponents_4 (b c e : ℕ) (h : 4 + b + c + e = 4) :
    exponent 4 b c e ∈ exponents := by
  have hb : b ≤ 0 := by omega
  interval_cases b
  · have hc : c ≤ 0 := by omega
    interval_cases c
    · have he : e = 0 := by omega
      subst e
      exact member_4000

private theorem mem_exponents (α : Fin 4 →₀ ℕ) (hα : α.degree = 4) :
    α ∈ exponents := by
  have he : α = exponent (α 0) (α 1) (α 2) (α 3) := by
    ext i
    fin_cases i <;> simp [exponent]
  have hs : α 0 + α 1 + α 2 + α 3 = 4 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_succ,
      add_assoc] using hα
  have h0 : α 0 ≤ 4 := by omega
  rw [he]
  interval_cases h : α 0
  · exact mem_exponents_0 _ _ _ (by omega)
  · exact mem_exponents_1 _ _ _ (by omega)
  · exact mem_exponents_2 _ _ _ (by omega)
  · exact mem_exponents_3 _ _ _ (by omega)
  · exact mem_exponents_4 _ _ _ (by omega)


private theorem eval_monomial_exponent (x : Vec 4) (a b c e : ℕ) (r : ℝ) :
    eval x (monomial (exponent a b c e) r) =
      r * x 0 ^ a * x 1 ^ b * x 2 ^ c * x 3 ^ e := by
  simp [exponent, eval_monomial, Finsupp.prod_add_index, Finsupp.prod_single_index,
    pow_add, mul_assoc]

private theorem eval_expansion (q : RPoly 4) (hq : q.IsHomogeneous 4) (x : Vec 4) :
    eval x q =
      q.coeff (exponent 0 0 0 4) * x 3 ^ 4 +
      q.coeff (exponent 0 0 1 3) * x 2 * x 3 ^ 3 +
      q.coeff (exponent 0 0 2 2) * x 2 ^ 2 * x 3 ^ 2 +
      q.coeff (exponent 0 0 3 1) * x 2 ^ 3 * x 3 +
      q.coeff (exponent 0 0 4 0) * x 2 ^ 4 +
      q.coeff (exponent 0 1 0 3) * x 1 * x 3 ^ 3 +
      q.coeff (exponent 0 1 1 2) * x 1 * x 2 * x 3 ^ 2 +
      q.coeff (exponent 0 1 2 1) * x 1 * x 2 ^ 2 * x 3 +
      q.coeff (exponent 0 1 3 0) * x 1 * x 2 ^ 3 +
      q.coeff (exponent 0 2 0 2) * x 1 ^ 2 * x 3 ^ 2 +
      q.coeff (exponent 0 2 1 1) * x 1 ^ 2 * x 2 * x 3 +
      q.coeff (exponent 0 2 2 0) * x 1 ^ 2 * x 2 ^ 2 +
      q.coeff (exponent 0 3 0 1) * x 1 ^ 3 * x 3 +
      q.coeff (exponent 0 3 1 0) * x 1 ^ 3 * x 2 +
      q.coeff (exponent 0 4 0 0) * x 1 ^ 4 +
      q.coeff (exponent 1 0 0 3) * x 0 * x 3 ^ 3 +
      q.coeff (exponent 1 0 1 2) * x 0 * x 2 * x 3 ^ 2 +
      q.coeff (exponent 1 0 2 1) * x 0 * x 2 ^ 2 * x 3 +
      q.coeff (exponent 1 0 3 0) * x 0 * x 2 ^ 3 +
      q.coeff (exponent 1 1 0 2) * x 0 * x 1 * x 3 ^ 2 +
      q.coeff (exponent 1 1 1 1) * x 0 * x 1 * x 2 * x 3 +
      q.coeff (exponent 1 1 2 0) * x 0 * x 1 * x 2 ^ 2 +
      q.coeff (exponent 1 2 0 1) * x 0 * x 1 ^ 2 * x 3 +
      q.coeff (exponent 1 2 1 0) * x 0 * x 1 ^ 2 * x 2 +
      q.coeff (exponent 1 3 0 0) * x 0 * x 1 ^ 3 +
      q.coeff (exponent 2 0 0 2) * x 0 ^ 2 * x 3 ^ 2 +
      q.coeff (exponent 2 0 1 1) * x 0 ^ 2 * x 2 * x 3 +
      q.coeff (exponent 2 0 2 0) * x 0 ^ 2 * x 2 ^ 2 +
      q.coeff (exponent 2 1 0 1) * x 0 ^ 2 * x 1 * x 3 +
      q.coeff (exponent 2 1 1 0) * x 0 ^ 2 * x 1 * x 2 +
      q.coeff (exponent 2 2 0 0) * x 0 ^ 2 * x 1 ^ 2 +
      q.coeff (exponent 3 0 0 1) * x 0 ^ 3 * x 3 +
      q.coeff (exponent 3 0 1 0) * x 0 ^ 3 * x 2 +
      q.coeff (exponent 3 1 0 0) * x 0 ^ 3 * x 1 +
      q.coeff (exponent 4 0 0 0) * x 0 ^ 4 := by
  have hs : q.support ⊆ exponents := fun α hα ↦
    mem_exponents α (by
      simpa only [Finsupp.degree_apply, Finsupp.weight_apply, Pi.one_apply,
        smul_eq_mul, mul_one, Finsupp.sum] using hq (mem_support_iff.mp hα))
  have he : q = ∑ α ∈ exponents, monomial α (q.coeff α) := by
    nth_rw 1 [q.as_sum]
    exact Finset.sum_subset hs fun α _ hα ↦ by
      rw [notMem_support_iff.mp hα, monomial_zero]
  rw [he, map_sum]
  simp [exponents, exponent_inj, eval_monomial_exponent, add_assoc]

private theorem sample_m1m1m1m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![-1, -1, -1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1m1m11 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![-1, -1, -1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1m100 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![-1, -1, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1m101 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![-1, -1, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1m11m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![-1, -1, 1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1m110 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 1 0) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 1 0) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![-1, -1, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1m111 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![-1, -1, 1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m10m10 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 3 0) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 3 0) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![-1, 0, -1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m10m11 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) + q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) + q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![-1, 0, -1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m100m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 1 0 0 3) + q.coeff (exponent 2 0 0 2) +
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 1 0 0 3) + q.coeff (exponent 2 0 0 2) +
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![-1, 0, 0, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1001 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 1 0 0 3) + q.coeff (exponent 2 0 0 2) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 1 0 0 3) + q.coeff (exponent 2 0 0 2) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![-1, 0, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1002 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 0 4) - 8 * q.coeff (exponent 1 0 0 3) +
      4 * q.coeff (exponent 2 0 0 2) - 2 * q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ∧
      16 * q.coeff (exponent 0 0 0 4) - 8 * q.coeff (exponent 1 0 0 3) +
      4 * q.coeff (exponent 2 0 0 2) - 2 * q.coeff (exponent 3 0 0 1) +
      q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![-1, 0, 0, 2]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m101m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![-1, 0, 1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1010 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 3 0) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 3 0) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![-1, 0, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1011 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![-1, 0, 1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1020 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 4 0) - 8 * q.coeff (exponent 1 0 3 0) +
      4 * q.coeff (exponent 2 0 2 0) - 2 * q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      16 * q.coeff (exponent 0 0 4 0) - 8 * q.coeff (exponent 1 0 3 0) +
      4 * q.coeff (exponent 2 0 2 0) - 2 * q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![-1, 0, 2, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m11m1m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![-1, 1, -1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m11m10 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 3 0) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 1 0) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 1 0) - q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 3 0) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 1 0) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 1 0) - q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![-1, 1, -1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m11m11 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![-1, 1, -1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m110m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![-1, 1, 0, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1100 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![-1, 1, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1101 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![-1, 1, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m111m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![-1, 1, 1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1110 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 3 0) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 1 0) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 1 0) - q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 3 0) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 1 0) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 1 0) - q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![-1, 1, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1111 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![-1, 1, 1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_m1200 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 4 0 0) - 8 * q.coeff (exponent 1 3 0 0) +
      4 * q.coeff (exponent 2 2 0 0) - 2 * q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      16 * q.coeff (exponent 0 4 0 0) - 8 * q.coeff (exponent 1 3 0 0) +
      4 * q.coeff (exponent 2 2 0 0) - 2 * q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![-1, 2, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0m1m10 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ≤ 4 * B := by
  have h := hb ![0, -1, -1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0m1m11 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) +
      q.coeff (exponent 0 4 0 0) ≤ 9 * B := by
  have h := hb ![0, -1, -1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0m10m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ≤ 4 * B := by
  have h := hb ![0, -1, 0, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0m101 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ≤ 4 * B := by
  have h := hb ![0, -1, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0m102 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 0 4) - 8 * q.coeff (exponent 0 1 0 3) +
      4 * q.coeff (exponent 0 2 0 2) - 2 * q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ∧
      16 * q.coeff (exponent 0 0 0 4) - 8 * q.coeff (exponent 0 1 0 3) +
      4 * q.coeff (exponent 0 2 0 2) - 2 * q.coeff (exponent 0 3 0 1) +
      q.coeff (exponent 0 4 0 0) ≤ 25 * B := by
  have h := hb ![0, -1, 0, 2]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0m11m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) +
      q.coeff (exponent 0 4 0 0) ≤ 9 * B := by
  have h := hb ![0, -1, 1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0m110 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ≤ 4 * B := by
  have h := hb ![0, -1, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0m111 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) +
      q.coeff (exponent 0 4 0 0) ≤ 9 * B := by
  have h := hb ![0, -1, 1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0m120 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 4 0) - 8 * q.coeff (exponent 0 1 3 0) +
      4 * q.coeff (exponent 0 2 2 0) - 2 * q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      16 * q.coeff (exponent 0 0 4 0) - 8 * q.coeff (exponent 0 1 3 0) +
      4 * q.coeff (exponent 0 2 2 0) - 2 * q.coeff (exponent 0 3 1 0) +
      q.coeff (exponent 0 4 0 0) ≤ 25 * B := by
  have h := hb ![0, -1, 2, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_00m1m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ≤ 4 * B := by
  have h := hb ![0, 0, -1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_00m11 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ≤ 4 * B := by
  have h := hb ![0, 0, -1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_00m12 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 0 4) - 8 * q.coeff (exponent 0 0 1 3) +
      4 * q.coeff (exponent 0 0 2 2) - 2 * q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ∧
      16 * q.coeff (exponent 0 0 0 4) - 8 * q.coeff (exponent 0 0 1 3) +
      4 * q.coeff (exponent 0 0 2 2) - 2 * q.coeff (exponent 0 0 3 1) +
      q.coeff (exponent 0 0 4 0) ≤ 25 * B := by
  have h := hb ![0, 0, -1, 2]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0001 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) ∧
      q.coeff (exponent 0 0 0 4) ≤ 1 * B := by
  have h := hb ![0, 0, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_001m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ≤ 4 * B := by
  have h := hb ![0, 0, 1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0010 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) ∧
      q.coeff (exponent 0 0 4 0) ≤ 1 * B := by
  have h := hb ![0, 0, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0011 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ≤ 4 * B := by
  have h := hb ![0, 0, 1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0012 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 0 4) + 8 * q.coeff (exponent 0 0 1 3) +
      4 * q.coeff (exponent 0 0 2 2) + 2 * q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) ∧
      16 * q.coeff (exponent 0 0 0 4) + 8 * q.coeff (exponent 0 0 1 3) +
      4 * q.coeff (exponent 0 0 2 2) + 2 * q.coeff (exponent 0 0 3 1) +
      q.coeff (exponent 0 0 4 0) ≤ 25 * B := by
  have h := hb ![0, 0, 1, 2]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_002m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - 2 * q.coeff (exponent 0 0 1 3) +
      4 * q.coeff (exponent 0 0 2 2) - 8 * q.coeff (exponent 0 0 3 1) +
      16 * q.coeff (exponent 0 0 4 0) ∧
      q.coeff (exponent 0 0 0 4) - 2 * q.coeff (exponent 0 0 1 3) +
      4 * q.coeff (exponent 0 0 2 2) - 8 * q.coeff (exponent 0 0 3 1) +
      16 * q.coeff (exponent 0 0 4 0) ≤ 25 * B := by
  have h := hb ![0, 0, 2, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0021 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + 2 * q.coeff (exponent 0 0 1 3) +
      4 * q.coeff (exponent 0 0 2 2) + 8 * q.coeff (exponent 0 0 3 1) +
      16 * q.coeff (exponent 0 0 4 0) ∧
      q.coeff (exponent 0 0 0 4) + 2 * q.coeff (exponent 0 0 1 3) +
      4 * q.coeff (exponent 0 0 2 2) + 8 * q.coeff (exponent 0 0 3 1) +
      16 * q.coeff (exponent 0 0 4 0) ≤ 25 * B := by
  have h := hb ![0, 0, 2, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_01m1m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) +
      q.coeff (exponent 0 4 0 0) ≤ 9 * B := by
  have h := hb ![0, 1, -1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_01m10 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ≤ 4 * B := by
  have h := hb ![0, 1, -1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_01m11 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) +
      q.coeff (exponent 0 4 0 0) ≤ 9 * B := by
  have h := hb ![0, 1, -1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_010m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ≤ 4 * B := by
  have h := hb ![0, 1, 0, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0100 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 4 0 0) ≤ 1 * B := by
  have h := hb ![0, 1, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0101 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ≤ 4 * B := by
  have h := hb ![0, 1, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0102 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 0 4) + 8 * q.coeff (exponent 0 1 0 3) +
      4 * q.coeff (exponent 0 2 0 2) + 2 * q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) ∧
      16 * q.coeff (exponent 0 0 0 4) + 8 * q.coeff (exponent 0 1 0 3) +
      4 * q.coeff (exponent 0 2 0 2) + 2 * q.coeff (exponent 0 3 0 1) +
      q.coeff (exponent 0 4 0 0) ≤ 25 * B := by
  have h := hb ![0, 1, 0, 2]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_011m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) +
      q.coeff (exponent 0 4 0 0) ≤ 9 * B := by
  have h := hb ![0, 1, 1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0110 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ≤ 4 * B := by
  have h := hb ![0, 1, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0111 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) +
      q.coeff (exponent 0 4 0 0) ≤ 9 * B := by
  have h := hb ![0, 1, 1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0120 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 4 0) + 8 * q.coeff (exponent 0 1 3 0) +
      4 * q.coeff (exponent 0 2 2 0) + 2 * q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) ∧
      16 * q.coeff (exponent 0 0 4 0) + 8 * q.coeff (exponent 0 1 3 0) +
      4 * q.coeff (exponent 0 2 2 0) + 2 * q.coeff (exponent 0 3 1 0) +
      q.coeff (exponent 0 4 0 0) ≤ 25 * B := by
  have h := hb ![0, 1, 2, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_02m10 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - 2 * q.coeff (exponent 0 1 3 0) +
      4 * q.coeff (exponent 0 2 2 0) - 8 * q.coeff (exponent 0 3 1 0) +
      16 * q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 4 0) - 2 * q.coeff (exponent 0 1 3 0) +
      4 * q.coeff (exponent 0 2 2 0) - 8 * q.coeff (exponent 0 3 1 0) +
      16 * q.coeff (exponent 0 4 0 0) ≤ 25 * B := by
  have h := hb ![0, 2, -1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_020m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - 2 * q.coeff (exponent 0 1 0 3) +
      4 * q.coeff (exponent 0 2 0 2) - 8 * q.coeff (exponent 0 3 0 1) +
      16 * q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) - 2 * q.coeff (exponent 0 1 0 3) +
      4 * q.coeff (exponent 0 2 0 2) - 8 * q.coeff (exponent 0 3 0 1) +
      16 * q.coeff (exponent 0 4 0 0) ≤ 25 * B := by
  have h := hb ![0, 2, 0, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0201 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + 2 * q.coeff (exponent 0 1 0 3) +
      4 * q.coeff (exponent 0 2 0 2) + 8 * q.coeff (exponent 0 3 0 1) +
      16 * q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 0 4) + 2 * q.coeff (exponent 0 1 0 3) +
      4 * q.coeff (exponent 0 2 0 2) + 8 * q.coeff (exponent 0 3 0 1) +
      16 * q.coeff (exponent 0 4 0 0) ≤ 25 * B := by
  have h := hb ![0, 2, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_0210 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) + 2 * q.coeff (exponent 0 1 3 0) +
      4 * q.coeff (exponent 0 2 2 0) + 8 * q.coeff (exponent 0 3 1 0) +
      16 * q.coeff (exponent 0 4 0 0) ∧
      q.coeff (exponent 0 0 4 0) + 2 * q.coeff (exponent 0 1 3 0) +
      4 * q.coeff (exponent 0 2 2 0) + 8 * q.coeff (exponent 0 3 1 0) +
      16 * q.coeff (exponent 0 4 0 0) ≤ 25 * B := by
  have h := hb ![0, 2, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1m1m1m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![1, -1, -1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1m1m10 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 3 0) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 1 0) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 1 0) - q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 3 0) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 1 0) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 1 0) - q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, -1, -1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1m1m11 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![1, -1, -1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1m10m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, -1, 0, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1m100 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![1, -1, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1m101 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, -1, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1m11m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![1, -1, 1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1m110 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 3 0) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 1 0) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 1 0) - q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 3 0) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 1 0) - q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 1 0) - q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, -1, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1m111 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) - q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) -
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) -
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) -
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![1, -1, 1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_10m1m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, 0, -1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_10m10 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 3 0) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 3 0) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![1, 0, -1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_10m11 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 0 3) -
      q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, 0, -1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_100m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 1 0 0 3) + q.coeff (exponent 2 0 0 2) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 1 0 0 3) + q.coeff (exponent 2 0 0 2) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![1, 0, 0, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1000 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 4 0 0 0) ≤ 1 * B := by
  have h := hb ![1, 0, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1001 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 1 0 0 3) + q.coeff (exponent 2 0 0 2) +
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 1 0 0 3) + q.coeff (exponent 2 0 0 2) +
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![1, 0, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1002 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 0 4) + 8 * q.coeff (exponent 1 0 0 3) +
      4 * q.coeff (exponent 2 0 0 2) + 2 * q.coeff (exponent 3 0 0 1) + q.coeff (exponent 4 0 0 0) ∧
      16 * q.coeff (exponent 0 0 0 4) + 8 * q.coeff (exponent 1 0 0 3) +
      4 * q.coeff (exponent 2 0 0 2) + 2 * q.coeff (exponent 3 0 0 1) +
      q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![1, 0, 0, 2]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_101m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) + q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) + q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, 0, 1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1010 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 3 0) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 3 0) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![1, 0, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1011 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) + q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) + q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) + q.coeff (exponent 2 0 2 0) +
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, 0, 1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1020 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 0 4 0) + 8 * q.coeff (exponent 1 0 3 0) +
      4 * q.coeff (exponent 2 0 2 0) + 2 * q.coeff (exponent 3 0 1 0) + q.coeff (exponent 4 0 0 0) ∧
      16 * q.coeff (exponent 0 0 4 0) + 8 * q.coeff (exponent 1 0 3 0) +
      4 * q.coeff (exponent 2 0 2 0) + 2 * q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![1, 0, 2, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_11m1m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![1, 1, -1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_11m10 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 1 0) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 1 0) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, 1, -1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_11m11 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) -
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) - q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) - q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) - q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) -
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) - q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) - q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) - q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![1, 1, -1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_110m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) - q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) -
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, 1, 0, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1100 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 4 * B := by
  have h := hb ![1, 1, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1101 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 1 0 3) + q.coeff (exponent 0 2 0 2) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 0 3) +
      q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, 1, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_111m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) -
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) - q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) - q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) - q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) -
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) -
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) - q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) - q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) - q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) - q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) - q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) - q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![1, 1, 1, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1110 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 1 0) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 3 0) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) + q.coeff (exponent 1 0 3 0) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 1 0) + q.coeff (exponent 1 3 0 0) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 1 0) + q.coeff (exponent 2 2 0 0) +
      q.coeff (exponent 3 0 1 0) + q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 9 * B := by
  have h := hb ![1, 1, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1111 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + q.coeff (exponent 0 0 1 3) + q.coeff (exponent 0 0 2 2) +
      q.coeff (exponent 0 0 3 1) + q.coeff (exponent 0 0 4 0) + q.coeff (exponent 0 1 0 3) +
      q.coeff (exponent 0 1 1 2) + q.coeff (exponent 0 1 2 1) + q.coeff (exponent 0 1 3 0) +
      q.coeff (exponent 0 2 0 2) + q.coeff (exponent 0 2 1 1) + q.coeff (exponent 0 2 2 0) +
      q.coeff (exponent 0 3 0 1) + q.coeff (exponent 0 3 1 0) + q.coeff (exponent 0 4 0 0) +
      q.coeff (exponent 1 0 0 3) + q.coeff (exponent 1 0 1 2) + q.coeff (exponent 1 0 2 1) +
      q.coeff (exponent 1 0 3 0) + q.coeff (exponent 1 1 0 2) + q.coeff (exponent 1 1 1 1) +
      q.coeff (exponent 1 1 2 0) + q.coeff (exponent 1 2 0 1) + q.coeff (exponent 1 2 1 0) +
      q.coeff (exponent 1 3 0 0) + q.coeff (exponent 2 0 0 2) + q.coeff (exponent 2 0 1 1) +
      q.coeff (exponent 2 0 2 0) + q.coeff (exponent 2 1 0 1) + q.coeff (exponent 2 1 1 0) +
      q.coeff (exponent 2 2 0 0) + q.coeff (exponent 3 0 0 1) + q.coeff (exponent 3 0 1 0) +
      q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ≤ 16 * B := by
  have h := hb ![1, 1, 1, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_1200 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ 16 * q.coeff (exponent 0 4 0 0) + 8 * q.coeff (exponent 1 3 0 0) +
      4 * q.coeff (exponent 2 2 0 0) + 2 * q.coeff (exponent 3 1 0 0) + q.coeff (exponent 4 0 0 0) ∧
      16 * q.coeff (exponent 0 4 0 0) + 8 * q.coeff (exponent 1 3 0 0) +
      4 * q.coeff (exponent 2 2 0 0) + 2 * q.coeff (exponent 3 1 0 0) +
      q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![1, 2, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_2m100 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 4 0 0) - 2 * q.coeff (exponent 1 3 0 0) +
      4 * q.coeff (exponent 2 2 0 0) - 8 * q.coeff (exponent 3 1 0 0) +
      16 * q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 4 0 0) - 2 * q.coeff (exponent 1 3 0 0) +
      4 * q.coeff (exponent 2 2 0 0) - 8 * q.coeff (exponent 3 1 0 0) +
      16 * q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![2, -1, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_20m10 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) - 2 * q.coeff (exponent 1 0 3 0) +
      4 * q.coeff (exponent 2 0 2 0) - 8 * q.coeff (exponent 3 0 1 0) +
      16 * q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) - 2 * q.coeff (exponent 1 0 3 0) +
      4 * q.coeff (exponent 2 0 2 0) - 8 * q.coeff (exponent 3 0 1 0) +
      16 * q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![2, 0, -1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_200m1 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) - 2 * q.coeff (exponent 1 0 0 3) +
      4 * q.coeff (exponent 2 0 0 2) - 8 * q.coeff (exponent 3 0 0 1) +
      16 * q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) - 2 * q.coeff (exponent 1 0 0 3) +
      4 * q.coeff (exponent 2 0 0 2) - 8 * q.coeff (exponent 3 0 0 1) +
      16 * q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![2, 0, 0, -1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_2001 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 0 4) + 2 * q.coeff (exponent 1 0 0 3) +
      4 * q.coeff (exponent 2 0 0 2) + 8 * q.coeff (exponent 3 0 0 1) +
      16 * q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 0 4) + 2 * q.coeff (exponent 1 0 0 3) +
      4 * q.coeff (exponent 2 0 0 2) + 8 * q.coeff (exponent 3 0 0 1) +
      16 * q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![2, 0, 0, 1]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_2010 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 0 4 0) + 2 * q.coeff (exponent 1 0 3 0) +
      4 * q.coeff (exponent 2 0 2 0) + 8 * q.coeff (exponent 3 0 1 0) +
      16 * q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 0 4 0) + 2 * q.coeff (exponent 1 0 3 0) +
      4 * q.coeff (exponent 2 0 2 0) + 8 * q.coeff (exponent 3 0 1 0) +
      16 * q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![2, 0, 1, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem sample_2100 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    0 ≤ q.coeff (exponent 0 4 0 0) + 2 * q.coeff (exponent 1 3 0 0) +
      4 * q.coeff (exponent 2 2 0 0) + 8 * q.coeff (exponent 3 1 0 0) +
      16 * q.coeff (exponent 4 0 0 0) ∧
      q.coeff (exponent 0 4 0 0) + 2 * q.coeff (exponent 1 3 0 0) +
      4 * q.coeff (exponent 2 2 0 0) + 8 * q.coeff (exponent 3 1 0 0) +
      16 * q.coeff (exponent 4 0 0 0) ≤ 25 * B := by
  have h := hb ![2, 1, 0, 0]
  rw [eval_expansion q hq] at h
  norm_num [sqnorm, dotProduct, Fin.sum_univ_succ] at h
  constructor <;> linarith [h.1, h.2]

private theorem bound_0004 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 0 0 4)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0001 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0013 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 0 1 3)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0011 q hq B hb
  obtain ⟨l1, u1⟩ := sample_00m11 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0012 q hq B hb
  obtain ⟨l3, u3⟩ := sample_00m12 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0022 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 0 2 2)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0011 q hq B hb
  obtain ⟨l1, u1⟩ := sample_001m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0010 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0001 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0031 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 0 3 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0011 q hq B hb
  obtain ⟨l1, u1⟩ := sample_001m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0021 q hq B hb
  obtain ⟨l3, u3⟩ := sample_002m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0040 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 0 4 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0010 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0103 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 1 0 3)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0101 q hq B hb
  obtain ⟨l1, u1⟩ := sample_0m101 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0102 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0m102 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0112 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 1 1 2)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0111 q hq B hb
  obtain ⟨l1, u1⟩ := sample_01m11 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0m111 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0m1m11 q hq B hb
  obtain ⟨l4, u4⟩ := sample_0110 q hq B hb
  obtain ⟨l5, u5⟩ := sample_01m10 q hq B hb
  obtain ⟨l6, u6⟩ := sample_0m110 q hq B hb
  obtain ⟨l7, u7⟩ := sample_0m1m10 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0121 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 1 2 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0111 q hq B hb
  obtain ⟨l1, u1⟩ := sample_011m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0m111 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0m11m1 q hq B hb
  obtain ⟨l4, u4⟩ := sample_0101 q hq B hb
  obtain ⟨l5, u5⟩ := sample_010m1 q hq B hb
  obtain ⟨l6, u6⟩ := sample_0m101 q hq B hb
  obtain ⟨l7, u7⟩ := sample_0m10m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0130 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 1 3 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0110 q hq B hb
  obtain ⟨l1, u1⟩ := sample_0m110 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0120 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0m120 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0202 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 2 0 2)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0101 q hq B hb
  obtain ⟨l1, u1⟩ := sample_010m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0100 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0001 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0211 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 2 1 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0111 q hq B hb
  obtain ⟨l1, u1⟩ := sample_011m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_01m11 q hq B hb
  obtain ⟨l3, u3⟩ := sample_01m1m1 q hq B hb
  obtain ⟨l4, u4⟩ := sample_0011 q hq B hb
  obtain ⟨l5, u5⟩ := sample_001m1 q hq B hb
  obtain ⟨l6, u6⟩ := sample_00m11 q hq B hb
  obtain ⟨l7, u7⟩ := sample_00m1m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0220 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 2 2 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0110 q hq B hb
  obtain ⟨l1, u1⟩ := sample_01m10 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0100 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0010 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0301 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 3 0 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0101 q hq B hb
  obtain ⟨l1, u1⟩ := sample_010m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0201 q hq B hb
  obtain ⟨l3, u3⟩ := sample_020m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0310 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 3 1 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0110 q hq B hb
  obtain ⟨l1, u1⟩ := sample_01m10 q hq B hb
  obtain ⟨l2, u2⟩ := sample_0210 q hq B hb
  obtain ⟨l3, u3⟩ := sample_02m10 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_0400 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 0 4 0 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_0100 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1003 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 0 0 3)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1001 q hq B hb
  obtain ⟨l1, u1⟩ := sample_m1001 q hq B hb
  obtain ⟨l2, u2⟩ := sample_1002 q hq B hb
  obtain ⟨l3, u3⟩ := sample_m1002 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1012 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 0 1 2)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1011 q hq B hb
  obtain ⟨l1, u1⟩ := sample_10m11 q hq B hb
  obtain ⟨l2, u2⟩ := sample_m1011 q hq B hb
  obtain ⟨l3, u3⟩ := sample_m10m11 q hq B hb
  obtain ⟨l4, u4⟩ := sample_1010 q hq B hb
  obtain ⟨l5, u5⟩ := sample_10m10 q hq B hb
  obtain ⟨l6, u6⟩ := sample_m1010 q hq B hb
  obtain ⟨l7, u7⟩ := sample_m10m10 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1021 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 0 2 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1011 q hq B hb
  obtain ⟨l1, u1⟩ := sample_101m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_m1011 q hq B hb
  obtain ⟨l3, u3⟩ := sample_m101m1 q hq B hb
  obtain ⟨l4, u4⟩ := sample_1001 q hq B hb
  obtain ⟨l5, u5⟩ := sample_100m1 q hq B hb
  obtain ⟨l6, u6⟩ := sample_m1001 q hq B hb
  obtain ⟨l7, u7⟩ := sample_m100m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1030 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 0 3 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1010 q hq B hb
  obtain ⟨l1, u1⟩ := sample_m1010 q hq B hb
  obtain ⟨l2, u2⟩ := sample_1020 q hq B hb
  obtain ⟨l3, u3⟩ := sample_m1020 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1102 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 1 0 2)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1101 q hq B hb
  obtain ⟨l1, u1⟩ := sample_1m101 q hq B hb
  obtain ⟨l2, u2⟩ := sample_m1101 q hq B hb
  obtain ⟨l3, u3⟩ := sample_m1m101 q hq B hb
  obtain ⟨l4, u4⟩ := sample_1100 q hq B hb
  obtain ⟨l5, u5⟩ := sample_1m100 q hq B hb
  obtain ⟨l6, u6⟩ := sample_m1100 q hq B hb
  obtain ⟨l7, u7⟩ := sample_m1m100 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1111 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (_hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 1 1 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1111 q hq B hb
  obtain ⟨l1, u1⟩ := sample_111m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_11m11 q hq B hb
  obtain ⟨l3, u3⟩ := sample_11m1m1 q hq B hb
  obtain ⟨l4, u4⟩ := sample_1m111 q hq B hb
  obtain ⟨l5, u5⟩ := sample_1m11m1 q hq B hb
  obtain ⟨l6, u6⟩ := sample_1m1m11 q hq B hb
  obtain ⟨l7, u7⟩ := sample_1m1m1m1 q hq B hb
  obtain ⟨l8, u8⟩ := sample_m1111 q hq B hb
  obtain ⟨l9, u9⟩ := sample_m111m1 q hq B hb
  obtain ⟨l10, u10⟩ := sample_m11m11 q hq B hb
  obtain ⟨l11, u11⟩ := sample_m11m1m1 q hq B hb
  obtain ⟨l12, u12⟩ := sample_m1m111 q hq B hb
  obtain ⟨l13, u13⟩ := sample_m1m11m1 q hq B hb
  obtain ⟨l14, u14⟩ := sample_m1m1m11 q hq B hb
  obtain ⟨l15, u15⟩ := sample_m1m1m1m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1120 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 1 2 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1110 q hq B hb
  obtain ⟨l1, u1⟩ := sample_1m110 q hq B hb
  obtain ⟨l2, u2⟩ := sample_m1110 q hq B hb
  obtain ⟨l3, u3⟩ := sample_m1m110 q hq B hb
  obtain ⟨l4, u4⟩ := sample_1100 q hq B hb
  obtain ⟨l5, u5⟩ := sample_1m100 q hq B hb
  obtain ⟨l6, u6⟩ := sample_m1100 q hq B hb
  obtain ⟨l7, u7⟩ := sample_m1m100 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1201 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 2 0 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1101 q hq B hb
  obtain ⟨l1, u1⟩ := sample_110m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_m1101 q hq B hb
  obtain ⟨l3, u3⟩ := sample_m110m1 q hq B hb
  obtain ⟨l4, u4⟩ := sample_1001 q hq B hb
  obtain ⟨l5, u5⟩ := sample_100m1 q hq B hb
  obtain ⟨l6, u6⟩ := sample_m1001 q hq B hb
  obtain ⟨l7, u7⟩ := sample_m100m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1210 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 2 1 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1110 q hq B hb
  obtain ⟨l1, u1⟩ := sample_11m10 q hq B hb
  obtain ⟨l2, u2⟩ := sample_m1110 q hq B hb
  obtain ⟨l3, u3⟩ := sample_m11m10 q hq B hb
  obtain ⟨l4, u4⟩ := sample_1010 q hq B hb
  obtain ⟨l5, u5⟩ := sample_10m10 q hq B hb
  obtain ⟨l6, u6⟩ := sample_m1010 q hq B hb
  obtain ⟨l7, u7⟩ := sample_m10m10 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_1300 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 1 3 0 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1100 q hq B hb
  obtain ⟨l1, u1⟩ := sample_m1100 q hq B hb
  obtain ⟨l2, u2⟩ := sample_1200 q hq B hb
  obtain ⟨l3, u3⟩ := sample_m1200 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_2002 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 2 0 0 2)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1001 q hq B hb
  obtain ⟨l1, u1⟩ := sample_100m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_1000 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0001 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_2011 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 2 0 1 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1011 q hq B hb
  obtain ⟨l1, u1⟩ := sample_101m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_10m11 q hq B hb
  obtain ⟨l3, u3⟩ := sample_10m1m1 q hq B hb
  obtain ⟨l4, u4⟩ := sample_0011 q hq B hb
  obtain ⟨l5, u5⟩ := sample_001m1 q hq B hb
  obtain ⟨l6, u6⟩ := sample_00m11 q hq B hb
  obtain ⟨l7, u7⟩ := sample_00m1m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_2020 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 2 0 2 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1010 q hq B hb
  obtain ⟨l1, u1⟩ := sample_10m10 q hq B hb
  obtain ⟨l2, u2⟩ := sample_1000 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0010 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_2101 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 2 1 0 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1101 q hq B hb
  obtain ⟨l1, u1⟩ := sample_110m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_1m101 q hq B hb
  obtain ⟨l3, u3⟩ := sample_1m10m1 q hq B hb
  obtain ⟨l4, u4⟩ := sample_0101 q hq B hb
  obtain ⟨l5, u5⟩ := sample_010m1 q hq B hb
  obtain ⟨l6, u6⟩ := sample_0m101 q hq B hb
  obtain ⟨l7, u7⟩ := sample_0m10m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_2110 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 2 1 1 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1110 q hq B hb
  obtain ⟨l1, u1⟩ := sample_11m10 q hq B hb
  obtain ⟨l2, u2⟩ := sample_1m110 q hq B hb
  obtain ⟨l3, u3⟩ := sample_1m1m10 q hq B hb
  obtain ⟨l4, u4⟩ := sample_0110 q hq B hb
  obtain ⟨l5, u5⟩ := sample_01m10 q hq B hb
  obtain ⟨l6, u6⟩ := sample_0m110 q hq B hb
  obtain ⟨l7, u7⟩ := sample_0m1m10 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_2200 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 2 2 0 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1100 q hq B hb
  obtain ⟨l1, u1⟩ := sample_1m100 q hq B hb
  obtain ⟨l2, u2⟩ := sample_1000 q hq B hb
  obtain ⟨l3, u3⟩ := sample_0100 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_3001 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 3 0 0 1)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1001 q hq B hb
  obtain ⟨l1, u1⟩ := sample_100m1 q hq B hb
  obtain ⟨l2, u2⟩ := sample_2001 q hq B hb
  obtain ⟨l3, u3⟩ := sample_200m1 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_3010 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 3 0 1 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1010 q hq B hb
  obtain ⟨l1, u1⟩ := sample_10m10 q hq B hb
  obtain ⟨l2, u2⟩ := sample_2010 q hq B hb
  obtain ⟨l3, u3⟩ := sample_20m10 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_3100 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 3 1 0 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1100 q hq B hb
  obtain ⟨l1, u1⟩ := sample_1m100 q hq B hb
  obtain ⟨l2, u2⟩ := sample_2100 q hq B hb
  obtain ⟨l3, u3⟩ := sample_2m100 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem bound_4000 (q : RPoly 4) (hq : q.IsHomogeneous 4)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2) :
    |q.coeff (exponent 4 0 0 0)| ≤ 8 * B := by
  obtain ⟨l0, u0⟩ := sample_1000 q hq B hb
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A nonnegative quartic on four variables has coefficients at most eight times its bound. -/
theorem nonneg_coeff_four (q : RPoly 4) (hq : q.IsHomogeneous 4) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2)
    (α : Fin 4 →₀ ℕ) : |q.coeff α| ≤ 8 * B := by
  by_cases hα : α.degree = 4
  · have hm := mem_exponents α hα
    simp only [exponents, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound_0004 q hq B hB hb
    · exact bound_0013 q hq B hB hb
    · exact bound_0022 q hq B hB hb
    · exact bound_0031 q hq B hB hb
    · exact bound_0040 q hq B hB hb
    · exact bound_0103 q hq B hB hb
    · exact bound_0112 q hq B hB hb
    · exact bound_0121 q hq B hB hb
    · exact bound_0130 q hq B hB hb
    · exact bound_0202 q hq B hB hb
    · exact bound_0211 q hq B hB hb
    · exact bound_0220 q hq B hB hb
    · exact bound_0301 q hq B hB hb
    · exact bound_0310 q hq B hB hb
    · exact bound_0400 q hq B hB hb
    · exact bound_1003 q hq B hB hb
    · exact bound_1012 q hq B hB hb
    · exact bound_1021 q hq B hB hb
    · exact bound_1030 q hq B hB hb
    · exact bound_1102 q hq B hB hb
    · exact bound_1111 q hq B hB hb
    · exact bound_1120 q hq B hB hb
    · exact bound_1201 q hq B hB hb
    · exact bound_1210 q hq B hB hb
    · exact bound_1300 q hq B hB hb
    · exact bound_2002 q hq B hB hb
    · exact bound_2011 q hq B hB hb
    · exact bound_2020 q hq B hB hb
    · exact bound_2101 q hq B hB hb
    · exact bound_2110 q hq B hB hb
    · exact bound_2200 q hq B hB hb
    · exact bound_3001 q hq B hB hb
    · exact bound_3010 q hq B hB hb
    · exact bound_3100 q hq B hB hb
    · exact bound_4000 q hq B hB hb
  · rw [hq.coeff_eq_zero hα, abs_zero]
    exact mul_nonneg (by norm_num) hB

open Classical in
private def zeroExtend {σ τ : Type*} (g : σ ↪ τ) (x : σ → ℝ) (i : τ) : ℝ :=
  if h : i ∈ Set.range g then x ((Equiv.ofInjective g g.injective).symm ⟨i, h⟩)
  else 0

private theorem zeroExtend_apply {σ τ : Type*} (g : σ ↪ τ) (x : σ → ℝ) (i : σ) :
    zeroExtend g x (g i) = x i := by
  simp [zeroExtend, Equiv.ofInjective_symm_apply]

private theorem zeroExtend_sum_sq {σ τ : Type*} [Fintype σ] [Fintype τ]
    (g : σ ↪ τ) (x : σ → ℝ) :
    (∑ i, zeroExtend g x i ^ 2) = ∑ i, x i ^ 2 := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.image g, zeroExtend g x i ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hn : i ∉ Set.range g := by simpa using hi
      simp [zeroExtend, hn]
    _ = _ := by
      rw [Finset.sum_image g.injective.injOn]
      simp only [zeroExtend_apply]

private theorem eval_killCompl {σ τ : Type*} (g : σ ↪ τ)
    (q : MvPolynomial τ ℝ) (x : σ → ℝ) :
    eval x (q.killCompl g.injective) = eval (zeroExtend g x) q := by
  classical
  have he : (aeval x).comp (killCompl (R := ℝ) g.injective) =
      aeval (zeroExtend g x) := by
    ext i
    simp only [AlgHom.comp_apply, killCompl, aeval_X]
    split_ifs with hi
    · simp only [aeval_X, zeroExtend, dite_eq_left hi]
    · simp only [map_zero, zeroExtend, dite_eq_right hi]
  exact congrArg (fun f : MvPolynomial τ ℝ →ₐ[ℝ] ℝ ↦ f q) he

private theorem homogeneous_killCompl {σ τ : Type*} (g : σ ↪ τ)
    (q : MvPolynomial τ ℝ) (hq : q.IsHomogeneous 4) :
    (q.killCompl g.injective).IsHomogeneous 4 := by
  classical
  unfold killCompl
  convert hq.aeval _ (n := 1) ?_ using 1
  intro i
  split_ifs
  · exact isHomogeneous_X ℝ _
  · exact isHomogeneous_zero σ ℝ 1

/-- Restriction to the support of one coefficient makes the quartic estimate dimension free. -/
theorem nonneg_coeff {d : ℕ} (q : RPoly d) (hq : q.IsHomogeneous 4) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ x, 0 ≤ eval x q ∧ eval x q ≤ B * sqnorm x ^ 2)
    (α : Fin d →₀ ℕ) : |q.coeff α| ≤ 8 * B := by
  classical
  by_cases hα : α.degree = 4
  · let S := {i // i ∈ α.support}
    have hc : Fintype.card S ≤ 4 := by
      calc
        _ = ∑ i ∈ α.support, 1 := by
          change Fintype.card ↥α.support = _
          rw [Fintype.card_coe]
          simp
        _ ≤ ∑ i ∈ α.support, α i := Finset.sum_le_sum fun i hi ↦
          Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.mp hi)
        _ = 4 := hα
    let g : S ↪ Fin d := Function.Embedding.subtype _
    let f : S ↪ Fin 4 := (Fintype.equivFin S).toEmbedding.trans (Fin.castLEEmb hc)
    let r := q.killCompl g.injective
    let q₄ : RPoly 4 := rename f r
    let β : S →₀ ℕ := α.comapDomain g g.injective.injOn
    have hmap : β.mapDomain g = α := by
      apply Finsupp.mapDomain_comapDomain g g.injective α
      intro i hi
      exact ⟨⟨i, hi⟩, rfl⟩
    have he : q₄.coeff (β.mapDomain f) = q.coeff α := by
      rw [coeff_rename_mapDomain f f.injective, coeff_killCompl, hmap]
    rw [← he]
    apply nonneg_coeff_four q₄ (homogeneous_killCompl g q hq).rename_isHomogeneous B hB
    intro x
    have hv := hb (zeroExtend g (x ∘ f))
    have heval : eval x q₄ = eval (zeroExtend g (x ∘ f)) q := by
      rw [eval_rename]
      exact eval_killCompl g q (x ∘ f)
    rw [heval]
    refine ⟨hv.1, hv.2.trans ?_⟩
    have hn : sqnorm (zeroExtend g (x ∘ f)) ≤ sqnorm x := by
      simp only [sqnorm, dotProduct, ← pow_two, zeroExtend_sum_sq]
      change (∑ i : S, x (f i) ^ 2) ≤ _
      calc
        _ = ∑ j ∈ Finset.univ.image f, x j ^ 2 := by
          rw [Finset.sum_image f.injective.injOn]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ ↦ sq_nonneg (x i))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (by
        simp only [sqnorm, dotProduct, ← pow_two]
        positivity) hn 2) hB
  · rw [hq.coeff_eq_zero hα, abs_zero]
    exact mul_nonneg (by norm_num) hB

/-- Squaring the sum of coordinate squares gives coefficients zero, one, or two. -/
theorem nsq_sq_coeff {d : ℕ} (α : Fin d →₀ ℕ) :
    |((nsq : RPoly d) ^ 2).coeff α| ≤ 2 := by
  classical
  let P : RPoly d := (∑ i, X i) ^ 2
  have he : (nsq : RPoly d) ^ 2 = expand 2 P := by
    simp [P, nsq, map_pow, map_sum]
  rw [he]
  by_cases hα : (expand 2 P).coeff α = 0
  · simp [hα]
  · obtain ⟨β, _, hβ⟩ := Finset.mem_image.mp
      (support_expand_subset (p := 2) P (mem_support_iff.mpr hα))
    rw [← hβ, coeff_expand_smul 2 (by norm_num), coeff_sum_X_pow_of_fintype]
    split_ifs with hdeg
    · rw [Nat.abs_cast]
      have hb : β.multinomial ≤ 2 := by
        unfold Finsupp.multinomial
        change (β.sum (fun _ m ↦ m)).factorial / _ ≤ 2
        rw [hdeg]
        exact Nat.div_le_self _ _
      exact_mod_cast hb
    · norm_num

end

end ABBKS26.Centered.PolyAux
