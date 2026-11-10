module

public import ABBKS26.Assembly.Schedule
public import Mathlib.Tactic.FunProp
public import Mathlib.Algebra.Order.Floor.Semifield

/-! # Primitive recursive representations for the finite arithmetic ledger -/

@[expose] public section

namespace ABBKS26.Assembly.RunTimeAux

private class Representation (α : Type) where
  Code : Type
  prim : Primcodable Code
  value : Code → α
  repr : α → Code
  value_repr : ∀ a, value (repr a) = a

attribute [instance_reducible, instance] Representation.prim

private abbrev Code (α : Type) [Representation α] := Representation.Code α

private abbrev value {α : Type} [Representation α] : Code α → α :=
  Representation.value

private instance : Representation ℕ := ⟨ℕ, inferInstance, id, id, fun _ ↦ rfl⟩

private instance : Representation Bool := ⟨Bool, inferInstance, id, id, fun _ ↦ rfl⟩

private instance {α β : Type} [Representation α] [Representation β] :
    Representation (α × β) where
  Code := Code α × Code β
  prim := inferInstance
  value p := (value p.1, value p.2)
  repr p := (Representation.repr p.1, Representation.repr p.2)
  value_repr p := by simp [Representation.value_repr]

private instance {α : Type} [Representation α] : Representation (List α) where
  Code := List (Code α)
  prim := inferInstance
  value := List.map value
  repr := List.map Representation.repr
  value_repr xs := by simp [value, List.map_map, Function.comp_def,
    Representation.value_repr]

private def ratValue (p : ℕ × ℕ × ℕ) : ℚ :=
  ((p.1 : ℚ) - p.2.1) / (p.2.2 + 1 : ℕ)

private instance : Representation ℚ where
  Code := ℕ × ℕ × ℕ
  prim := inferInstance
  value := ratValue
  repr q := (q.num.toNat, (-q.num).toNat, q.den - 1)
  value_repr q := by
    have hn : (q.num.toNat : ℤ) - (-q.num).toNat = q.num := by omega
    have hd : q.den - 1 + 1 = q.den := Nat.sub_add_cancel q.pos
    dsimp [ratValue]
    rw [hd, ← Rat.intCast_natCast, ← Rat.intCast_natCast, ← Rat.intCast_sub, hn]
    exact Rat.num_div_den q

@[fun_prop]
private def Effective {α β : Type} [Representation α] [Representation β]
    (f : α → β) : Prop :=
  ∃ F : Code α → Code β, Primrec F ∧ ∀ c, value (F c) = f (value c)

private theorem effective_of_primrec {f : ℕ → ℕ} (h : Primrec f) : Effective f :=
  ⟨f, h, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_id {α : Type} [Representation α] : Effective (id : α → α) :=
  ⟨id, Primrec.id, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_const {α β : Type} [Representation α] [Representation β]
    (b : β) : Effective (fun _ : α ↦ b) :=
  ⟨fun _ ↦ Representation.repr b, Primrec.const _,
    fun _ ↦ Representation.value_repr b⟩

@[fun_prop]
private theorem effective_comp {α β γ : Type}
    [Representation α] [Representation β] [Representation γ]
    {f : β → γ} {g : α → β} (hf : Effective f) (hg : Effective g) :
    Effective (fun a ↦ f (g a)) := by
  obtain ⟨F, hF, eF⟩ := hf
  obtain ⟨G, hG, eG⟩ := hg
  exact ⟨fun c ↦ F (G c), hF.comp hG, fun c ↦ by rw [eF, eG]⟩

@[fun_prop]
private theorem effective_fst {α β : Type} [Representation α] [Representation β] :
    Effective (Prod.fst : α × β → α) := ⟨Prod.fst, Primrec.fst, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_snd {α β : Type} [Representation α] [Representation β] :
    Effective (Prod.snd : α × β → β) := ⟨Prod.snd, Primrec.snd, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_pair {α β γ : Type}
    [Representation α] [Representation β] [Representation γ]
    {f : α → β} {g : α → γ} (hf : Effective f) (hg : Effective g) :
    Effective (fun a ↦ (f a, g a)) := by
  obtain ⟨F, hF, eF⟩ := hf
  obtain ⟨G, hG, eG⟩ := hg
  exact ⟨fun c ↦ (F c, G c), hF.pair hG, fun c ↦ Prod.ext (eF c) (eG c)⟩

attribute [local fun_prop] Primrec
attribute [local fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.fst Primrec.snd
  Primrec.pair

private theorem primrec_add {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a ↦ f a + g a) :=
  Primrec.nat_add.comp hf hg

private theorem primrec_sub {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a ↦ f a - g a) :=
  Primrec.nat_sub.comp hf hg

private theorem primrec_mul {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a ↦ f a * g a) :=
  Primrec.nat_mul.comp hf hg

private theorem primrec_div {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a ↦ f a / g a) :=
  Primrec.nat_div.comp hf hg

attribute [local fun_prop] primrec_add primrec_sub primrec_mul primrec_div

@[local fun_prop]
private theorem primrec_cond {α β : Type} [Primcodable α] [Primcodable β]
    {b : α → Bool} {f g : α → β} (hb : Primrec b) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a ↦ cond (b a) (f a) (g a)) := Primrec.cond hb hf hg

@[local fun_prop]
private theorem primrec_decide_le {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a ↦ decide (f a ≤ g a)) :=
  (Primrec.nat_le.comp hf hg).decide

@[local fun_prop]
private theorem primrec_decide_eq {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a ↦ decide (f a = g a)) :=
  (Primrec.eq.comp hf hg).decide

@[fun_prop]
private theorem effective_nat_add : Effective (fun p : ℕ × ℕ ↦ p.1 + p.2) :=
  ⟨_, Primrec.nat_add, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_nat_sub : Effective (fun p : ℕ × ℕ ↦ p.1 - p.2) :=
  ⟨_, Primrec.nat_sub, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_nat_mul : Effective (fun p : ℕ × ℕ ↦ p.1 * p.2) :=
  ⟨_, Primrec.nat_mul, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_nat_max : Effective (fun p : ℕ × ℕ ↦ max p.1 p.2) :=
  ⟨_, Primrec.nat_max, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_rat_cast : Effective (fun n : ℕ ↦ (n : ℚ)) := by
  refine ⟨fun n ↦ (n, 0, 0), by fun_prop, ?_⟩
  intro n
  simp [value, Representation.value, ratValue]

@[fun_prop]
private theorem effective_rat_add : Effective (fun p : ℚ × ℚ ↦ p.1 + p.2) := by
  refine ⟨fun p ↦ (p.1.1 * (p.2.2.2 + 1) + p.2.1 * (p.1.2.2 + 1),
    p.1.2.1 * (p.2.2.2 + 1) + p.2.2.1 * (p.1.2.2 + 1),
    (p.1.2.2 + 1) * (p.2.2.2 + 1) - 1), by fun_prop, ?_⟩
  intro p
  change ratValue _ = ratValue p.1 + ratValue p.2
  have hd : 1 ≤ (p.1.2.2 + 1) * (p.2.2.2 + 1) := Nat.mul_pos (by omega) (by omega)
  simp only [ratValue, Nat.sub_add_cancel hd, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  field_simp
  ring

@[fun_prop]
private theorem effective_rat_neg : Effective (fun q : ℚ ↦ -q) := by
  refine ⟨fun p ↦ (p.2.1, p.1, p.2.2), by fun_prop, ?_⟩
  intro p
  change ratValue _ = -ratValue p
  simp only [ratValue]
  ring

@[fun_prop]
private theorem effective_rat_sub : Effective (fun p : ℚ × ℚ ↦ p.1 - p.2) := by
  simp only [sub_eq_add_neg]
  fun_prop

@[fun_prop]
private theorem effective_rat_mul : Effective (fun p : ℚ × ℚ ↦ p.1 * p.2) := by
  refine ⟨fun p ↦ (p.1.1 * p.2.1 + p.1.2.1 * p.2.2.1,
    p.1.1 * p.2.2.1 + p.1.2.1 * p.2.1,
    (p.1.2.2 + 1) * (p.2.2.2 + 1) - 1), by fun_prop, ?_⟩
  intro p
  change ratValue _ = ratValue p.1 * ratValue p.2
  have hd : 1 ≤ (p.1.2.2 + 1) * (p.2.2.2 + 1) := Nat.mul_pos (by omega) (by omega)
  simp only [ratValue, Nat.sub_add_cancel hd, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  field_simp
  ring

@[fun_prop]
private theorem effective_rat_inv : Effective (fun q : ℚ ↦ q⁻¹) := by
  refine ⟨fun p ↦ cond (decide (p.1 = p.2.1)) (0, 0, 0)
    (cond (decide (p.2.1 ≤ p.1)) (p.2.2 + 1, 0, p.1 - p.2.1 - 1)
      (0, p.2.2 + 1, p.2.1 - p.1 - 1)), by fun_prop, ?_⟩
  intro p
  change ratValue _ = (ratValue p)⁻¹
  by_cases he : p.1 = p.2.1
  · simp [he, ratValue]
  by_cases hle : p.2.1 ≤ p.1
  · have hd : p.1 - p.2.1 - 1 + 1 = p.1 - p.2.1 := by omega
    simp only [he, hle, decide_false, decide_true, Bool.cond_false, Bool.cond_true,
      ratValue, hd, Nat.cast_sub hle, Nat.cast_zero, sub_zero]
    rw [inv_div]
  · have hle' : p.1 ≤ p.2.1 := by omega
    have hd : p.2.1 - p.1 - 1 + 1 = p.2.1 - p.1 := by omega
    simp only [he, hle, decide_false, Bool.cond_false, ratValue, hd, Nat.cast_sub hle',
      Nat.cast_zero, zero_sub, inv_div]
    rw [show (p.1 : ℚ) - p.2.1 = -((p.2.1 : ℚ) - p.1) by ring, div_neg, neg_div]

@[fun_prop]
private theorem effective_rat_div : Effective (fun p : ℚ × ℚ ↦ p.1 / p.2) := by
  simp only [div_eq_mul_inv]
  fun_prop

@[fun_prop]
private theorem effective_rat_inv_raw : Effective Rat.inv := effective_rat_inv

@[fun_prop]
private theorem effective_rat_le :
    Effective (fun p : ℚ × ℚ ↦ decide (p.1 ≤ p.2)) := by
  refine ⟨fun p ↦ decide (p.1.1 * (p.2.2.2 + 1) + p.2.2.1 * (p.1.2.2 + 1) ≤
    p.2.1 * (p.1.2.2 + 1) + p.1.2.1 * (p.2.2.2 + 1)), by fun_prop, ?_⟩
  intro p
  change decide (p.1.1 * (p.2.2.2 + 1) + p.2.2.1 * (p.1.2.2 + 1) ≤
    p.2.1 * (p.1.2.2 + 1) + p.1.2.1 * (p.2.2.2 + 1)) =
      decide (ratValue p.1 ≤ ratValue p.2)
  apply decide_eq_decide.mpr
  rw [ratValue, ratValue, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  constructor <;> intro h
  · have hh : (p.1.1 : ℚ) * (p.2.2.2 + 1) + p.2.2.1 * (p.1.2.2 + 1) ≤
        p.2.1 * (p.1.2.2 + 1) + p.1.2.1 * (p.2.2.2 + 1) := by exact_mod_cast h
    nlinarith only [hh]
  · have hh : (p.1.1 : ℚ) * (p.2.2.2 + 1) + p.2.2.1 * (p.1.2.2 + 1) ≤
        p.2.1 * (p.1.2.2 + 1) + p.1.2.1 * (p.2.2.2 + 1) := by nlinarith only [h]
    exact_mod_cast hh

@[fun_prop]
private theorem effective_cond {α β : Type} [Representation α] [Representation β]
    {b : α → Bool} {f g : α → β} (hb : Effective b)
    (hf : Effective f) (hg : Effective g) :
    Effective (fun a ↦ cond (b a) (f a) (g a)) := by
  obtain ⟨B, hB, eB⟩ := hb
  obtain ⟨F, hF, eF⟩ := hf
  obtain ⟨G, hG, eG⟩ := hg
  refine ⟨fun c ↦ cond (B c) (F c) (G c), Primrec.cond hB hF hG, fun c ↦ ?_⟩
  have hb' := eB c
  change B c = b (value c) at hb'
  dsimp only
  rw [← hb']
  cases B c <;> simp [eF, eG]

@[fun_prop]
private theorem effective_rat_min : Effective (fun p : ℚ × ℚ ↦ min p.1 p.2) := by
  have h : Effective (fun p : ℚ × ℚ ↦ cond (decide (p.1 ≤ p.2)) p.1 p.2) := by fun_prop
  simpa only [Bool.cond_decide, min_def] using h

@[fun_prop]
private theorem effective_rat_max : Effective (fun p : ℚ × ℚ ↦ max p.1 p.2) := by
  have h : Effective (fun p : ℚ × ℚ ↦ cond (decide (p.1 ≤ p.2)) p.2 p.1) := by fun_prop
  simpa only [Bool.cond_decide, max_def] using h

@[fun_prop]
private theorem effective_rat_ceil : Effective (fun q : ℚ ↦ ⌈q⌉₊) := by
  refine ⟨fun p ↦ (p.1 - p.2.1 + p.2.2) / (p.2.2 + 1), by fun_prop, ?_⟩
  intro p
  change (p.1 - p.2.1 + p.2.2) / (p.2.2 + 1) = ⌈ratValue p⌉₊
  apply Nat.le_antisymm_iff.mpr
  constructor
  · rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have h := Nat.le_ceil (ratValue p)
    change ratValue p ≤ (⌈ratValue p⌉₊ : ℚ) at h
    unfold ratValue at h
    rw [div_le_iff₀ (by positivity)] at h
    change (p.1 : ℚ) - p.2.1 ≤ (⌈ratValue p⌉₊ : ℚ) * (p.2.2 + 1 : ℕ) at h
    have hh : (p.1 : ℚ) ≤ ⌈ratValue p⌉₊ * (p.2.2 + 1 : ℕ) + p.2.1 := by linarith
    have hn : p.1 ≤ ⌈ratValue p⌉₊ * (p.2.2 + 1) + p.2.1 := by exact_mod_cast hh
    rw [Nat.mul_comm (p.2.2 + 1)]
    omega
  · rw [Nat.ceil_le, ratValue, div_le_iff₀ (by positivity)]
    have h := Nat.lt_mul_div_succ (p.1 - p.2.1 + p.2.2) (by omega : 0 < p.2.2 + 1)
    have hn' : p.1 - p.2.1 ≤
        (p.1 - p.2.1 + p.2.2) / (p.2.2 + 1) * (p.2.2 + 1) := by
      nlinarith only [h]
    have hn : p.1 ≤ (p.1 - p.2.1 + p.2.2) / (p.2.2 + 1) * (p.2.2 + 1) + p.2.1 := by
      omega
    have hh : (p.1 : ℚ) ≤ ((p.1 - p.2.1 + p.2.2) / (p.2.2 + 1) : ℕ) *
        (p.2.2 + 1 : ℕ) + p.2.1 := by exact_mod_cast hn
    linarith

@[fun_prop]
private theorem effective_rat_floor : Effective (fun q : ℚ ↦ ⌊q⌋₊) := by
  refine ⟨fun p ↦ (p.1 - p.2.1) / (p.2.2 + 1), by fun_prop, ?_⟩
  intro p
  change (p.1 - p.2.1) / (p.2.2 + 1) = ⌊ratValue p⌋₊
  rw [ratValue, Nat.floor_div_natCast]
  rw [Nat.floor_sub_natCast, Nat.floor_natCast]

@[fun_prop]
private theorem effective_bool_not : Effective Bool.not :=
  ⟨Bool.not, Primrec.dom_finite Bool.not, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_rat_lt :
    Effective (fun p : ℚ × ℚ ↦ decide (p.1 < p.2)) := by
  have h : Effective (fun p : ℚ × ℚ ↦ !(decide (p.2 ≤ p.1))) :=
    effective_comp (f := Bool.not) (g := fun p : ℚ × ℚ ↦ decide (p.2 ≤ p.1))
      effective_bool_not
      (effective_comp (f := fun p : ℚ × ℚ ↦ decide (p.1 ≤ p.2)) (g := Prod.swap)
        effective_rat_le (effective_pair effective_snd effective_fst))
  convert h using 1
  funext p
  calc
    decide (p.1 < p.2) = decide (¬ p.2 ≤ p.1) := decide_eq_decide.mpr not_le.symm
    _ = !(decide (p.2 ≤ p.1)) := decide_not

@[fun_prop]
private theorem effective_ite {α β : Type} [Representation α] [Representation β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Effective (fun a ↦ decide (p a))) (hf : Effective f) (hg : Effective g) :
    Effective (fun a ↦ if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using effective_cond hp hf hg

@[fun_prop]
private theorem effective_iterate {α β : Type} [Representation α] [Representation β]
    {f : α → ℕ} {g : α → β} {h : α × β → β}
    (hf : Effective f) (hg : Effective g) (hh : Effective h) :
    Effective (fun a ↦ (fun b ↦ h (a, b))^[f a] (g a)) := by
  obtain ⟨F, hF, eF⟩ := hf
  obtain ⟨G, hG, eG⟩ := hg
  obtain ⟨H, hH, eH⟩ := hh
  refine ⟨fun c ↦ (fun b ↦ H (c, b))^[F c] (G c),
    Primrec.nat_iterate hF hG hH.to₂, fun c ↦ ?_⟩
  have hi (n : ℕ) (b : Code β) :
      value ((fun b ↦ H (c, b))^[n] b) =
        (fun b ↦ h (value c, b))^[n] (value b) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', eH]
      exact congrArg (fun b ↦ h (value c, b)) ih
  have ef := eF c
  change F c = f (value c) at ef
  dsimp only
  rw [hi, ef, eG]

@[fun_prop]
private theorem effective_nat_pow : Effective (fun p : ℕ × ℕ ↦ p.1 ^ p.2) := by
  have h : Effective (fun p : ℕ × ℕ ↦ (fun n ↦ p.1 * n)^[p.2] 1) :=
    effective_iterate (α := ℕ × ℕ) (β := ℕ) (f := Prod.snd) (g := fun _ ↦ 1)
      (h := fun p ↦ p.1.1 * p.2) (by fun_prop) (by fun_prop) (by fun_prop)
  convert h using 1
  funext p
  induction p.2 with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, pow_succ, Nat.mul_comm]

@[fun_prop]
private theorem effective_rat_pow : Effective (fun p : ℚ × ℕ ↦ p.1 ^ p.2) := by
  have h : Effective (fun p : ℚ × ℕ ↦ (fun q ↦ p.1 * q)^[p.2] 1) :=
    effective_iterate (α := ℚ × ℕ) (β := ℚ) (f := Prod.snd) (g := fun _ ↦ 1)
      (h := fun p ↦ p.1.1 * p.2) (by fun_prop) (by fun_prop) (by fun_prop)
  convert h using 1
  funext p
  induction p.2 with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, pow_succ, mul_comm]

@[fun_prop]
private theorem effective_nat_sqrt : Effective Nat.sqrt :=
  effective_of_primrec Primrec.nat_sqrt

private theorem primrec_nat_pow : Primrec (fun p : ℕ × ℕ ↦ p.1 ^ p.2) := by
  obtain ⟨F, hF, eF⟩ := effective_nat_pow
  exact hF.of_eq eF

@[local fun_prop]
private theorem primrec_pow {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a ↦ f a ^ g a) :=
  primrec_nat_pow.comp (hf.pair hg)

@[fun_prop]
private theorem effective_clog : Effective (Nat.clog 2) := by
  apply effective_of_primrec
  apply Primrec.of_graph
  · refine ⟨id, Primrec.id, fun n ↦ ?_⟩
    exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  · have h : PrimrecRel (fun n k : ℕ ↦
        n ≤ 2 ^ k ∧ (k = 0 ∨ 2 ^ (k - 1) < n)) := by
      apply PrimrecPred.and
      · exact Primrec.nat_le.comp Primrec.fst (by fun_prop)
      · apply PrimrecPred.or
        · exact Primrec.eq.comp Primrec.snd (Primrec.const 0)
        · exact Primrec.nat_lt.comp (by fun_prop) Primrec.fst
    apply h.of_eq
    intro n k
    constructor
    · rintro ⟨h₁, h₂⟩
      have hle := Nat.clog_le_of_le_pow h₁
      rcases h₂ with rfl | h₂
      · omega
      · have hlt := (Nat.lt_clog_iff_pow_lt (by decide)).mpr h₂
        omega
    · intro he
      subst k
      refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
      by_cases hz : Nat.clog 2 n = 0
      · exact Or.inl hz
      · exact Or.inr (Nat.pow_lt_of_lt_clog (by omega))

@[fun_prop]
private theorem effective_list_cons {α : Type} [Representation α] :
    Effective (fun p : α × List α ↦ p.1 :: p.2) :=
  ⟨_, Primrec.list_cons, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_list_range : Effective List.range :=
  ⟨_, Primrec.list_range, fun _ ↦ List.map_id _⟩

@[fun_prop]
private theorem effective_list_map {α β γ : Type}
    [Representation α] [Representation β] [Representation γ]
    {f : α → List β} {g : α × β → γ} (hf : Effective f) (hg : Effective g) :
    Effective (fun a ↦ (f a).map (fun b ↦ g (a, b))) := by
  obtain ⟨F, hF, eF⟩ := hf
  obtain ⟨G, hG, eG⟩ := hg
  refine ⟨fun c ↦ (F c).map (fun b ↦ G (c, b)),
    Primrec.list_map hF hG.to₂, fun c ↦ ?_⟩
  have ef := eF c
  change (F c).map value = f (value c) at ef
  dsimp only
  rw [← ef]
  change ((F c).map _).map value = ((F c).map value).map _
  simp only [List.map_map, Function.comp_def, eG]
  rfl

@[fun_prop]
private theorem effective_list_flatten {α : Type} [Representation α] :
    Effective (List.flatten : List (List α) → List α) := by
  refine ⟨List.flatten, Primrec.list_flatten, fun xs ↦ ?_⟩
  change xs.flatten.map value = (xs.map (List.map value)).flatten
  simp [List.map_flatten]

@[fun_prop]
private theorem effective_list_foldl {α β γ : Type}
    [Representation α] [Representation β] [Representation γ]
    {f : α → List β} {g : α → γ} {h : α × (γ × β) → γ}
    (hf : Effective f) (hg : Effective g) (hh : Effective h) :
    Effective (fun a ↦ (f a).foldl (fun c b ↦ h (a, c, b)) (g a)) := by
  obtain ⟨F, hF, eF⟩ := hf
  obtain ⟨G, hG, eG⟩ := hg
  obtain ⟨H, hH, eH⟩ := hh
  refine ⟨fun c ↦ (F c).foldl (fun b d ↦ H (c, b, d)) (G c),
    Primrec.list_foldl hF hG hH.to₂, fun c ↦ ?_⟩
  have hi (xs : List (Code β)) (b : Code γ) :
      value (xs.foldl (fun b d ↦ H (c, b, d)) b) =
        (xs.map value).foldl (fun b d ↦ h (value c, b, d)) (value b) := by
    induction xs generalizing b with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, ih]
      rw [eH]
      rfl
  have ef := eF c
  change (F c).map value = f (value c) at ef
  dsimp only
  rw [hi, eG, ef]

@[fun_prop]
private theorem effective_list_prod : Effective (List.prod : List ℕ → ℕ) := by
  have h : Effective (fun xs : List ℕ ↦ xs.foldl (· * ·) 1) :=
    effective_list_foldl (h := fun p ↦ p.2.1 * p.2.2)
      (by fun_prop) (by fun_prop) (by fun_prop)
  convert h using 1
  funext xs
  exact List.prod_eq_foldl


open _root_.ABBKS26.Tree Common

private abbrev ParamsTuple :=
  ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ

private def paramsTuple (p : StepParams) : ParamsTuple :=
  (p.w, p.straddle, p.windowMass, p.verifyMass, p.tail, p.K, p.WF, p.DF, p.R, p.sigmaSq,
    p.subspaceAccuracy, p.isotropy, p.momentError, p.frameAccuracy, p.contamination, p.leakage,
    p.separation)

private def tupleParams (p : ParamsTuple) : StepParams :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

private instance : Representation StepParams where
  Code := Code ParamsTuple
  prim := inferInstance
  value c := tupleParams (value c)
  repr p := Representation.repr (paramsTuple p)
  value_repr p := by
    change tupleParams (Representation.value (Representation.repr (paramsTuple p))) = p
    rw [Representation.value_repr]
    cases p
    rfl

@[fun_prop]
private theorem effective_tupleParams : Effective tupleParams :=
  ⟨id, Primrec.id, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_w : Effective StepParams.w :=
  ⟨fun p ↦ p.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_straddle : Effective StepParams.straddle :=
  ⟨fun p ↦ p.2.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_windowMass : Effective StepParams.windowMass :=
  ⟨fun p ↦ p.2.2.1, by fun_prop, fun _ ↦ rfl⟩


@[fun_prop]
private theorem effective_tail : Effective StepParams.tail :=
  ⟨fun p ↦ p.2.2.2.2.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_K : Effective StepParams.K :=
  ⟨fun p ↦ p.2.2.2.2.2.1, by fun_prop, fun _ ↦ rfl⟩


@[fun_prop]
private theorem effective_sigmaSq : Effective StepParams.sigmaSq :=
  ⟨fun p ↦ p.2.2.2.2.2.2.2.2.2.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_subspaceAccuracy : Effective StepParams.subspaceAccuracy :=
  ⟨fun p ↦ p.2.2.2.2.2.2.2.2.2.2.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_isotropy : Effective StepParams.isotropy :=
  ⟨fun p ↦ p.2.2.2.2.2.2.2.2.2.2.2.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_momentError : Effective StepParams.momentError :=
  ⟨fun p ↦ p.2.2.2.2.2.2.2.2.2.2.2.2.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_frameAccuracy : Effective StepParams.frameAccuracy :=
  ⟨fun p ↦ p.2.2.2.2.2.2.2.2.2.2.2.2.2.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_contamination : Effective StepParams.contamination :=
  ⟨fun p ↦ p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_leakage : Effective StepParams.leakage :=
  ⟨fun p ↦ p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_separation : Effective StepParams.separation :=
  ⟨fun p ↦ p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, by fun_prop, fun _ ↦ rfl⟩

@[fun_prop]
private theorem effective_mk {α : Type} [Representation α]
    {f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : α → ℚ}
    (h0 : Effective f0) (h1 : Effective f1) (h2 : Effective f2) (h3 : Effective f3) (h4 :
      Effective f4) (h5 : Effective f5) (h6 : Effective f6) (h7 : Effective f7) (h8 : Effective
      f8) (h9 : Effective f9) (h10 : Effective f10) (h11 : Effective f11) (h12 : Effective f12)
      (h13 : Effective f13) (h14 : Effective f14) (h15 : Effective f15) (h16 : Effective f16) :
    Effective (fun a ↦ StepParams.mk (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8
      a) (f9 a) (f10 a) (f11 a) (f12 a) (f13 a) (f14 a) (f15 a) (f16 a)) := by
  change Effective (fun a ↦ tupleParams (f0 a, f1 a, f2 a, f3 a, f4 a, f5 a, f6 a, f7 a, f8 a, f9
    a, f10 a, f11 a, f12 a, f13 a, f14 a, f15 a, f16 a))
  fun_prop

@[fun_prop]
private theorem effective_map {α β γ : Type}
    [Representation α] [Representation β] [Representation γ]
    {f : α → List β} {g : α → β → γ} (hf : Effective f)
    (hg : Effective (fun p : α × β ↦ g p.1 p.2)) :
    Effective (fun a ↦ (f a).map (g a)) :=
  effective_list_map hf hg

@[fun_prop]
private theorem effective_foldl {α β γ : Type}
    [Representation α] [Representation β] [Representation γ]
    {f : α → List β} {g : α → γ} {h : α → γ → β → γ}
    (hf : Effective f) (hg : Effective g)
    (hh : Effective (fun p : α × γ × β ↦ h p.1 p.2.1 p.2.2)) :
    Effective (fun a ↦ (f a).foldl (h a) (g a)) :=
  effective_list_foldl hf hg hh

@[fun_prop]
private theorem effective_flatMap {α β γ : Type}
    [Representation α] [Representation β] [Representation γ]
    {f : α → List β} {g : α → β → List γ} (hf : Effective f)
    (hg : Effective (fun p : α × β ↦ g p.1 p.2)) :
    Effective (fun a ↦ (f a).flatMap (g a)) := by
  have h := effective_comp effective_list_flatten (effective_map hf hg)
  simpa only [List.flatMap_def] using h

@[fun_prop]
private theorem effective_logInv : Effective logInv := by
  unfold logInv
  fun_prop

@[fun_prop]
private theorem effective_dyadicDown : Effective dyadicDown := by
  unfold dyadicDown
  apply effective_ite
  · exact effective_comp effective_rat_lt (effective_pair (effective_const 0) effective_id)
  · fun_prop
  · fun_prop

@[fun_prop]
private theorem effective_dyadicUp : Effective dyadicUp := by
  unfold dyadicUp
  fun_prop

@[fun_prop]
private theorem effective_sqrtUp : Effective sqrtUp := by
  unfold sqrtUp
  fun_prop

@[fun_prop]
private theorem effective_centered_gamma : Effective (fun p : ℚ × ℚ ↦
    Centered.gammaStar p.1 p.2) := by
  unfold Centered.gammaStar Centered.delta Centered.nu
  fun_prop

@[fun_prop]
private theorem effective_centered_eta : Effective (fun p : ℚ × ℚ ↦
    Centered.etaStar p.1 p.2) := by
  unfold Centered.etaStar Centered.delta Centered.nu
  fun_prop

@[fun_prop]
private theorem effective_tDegree : Effective IdCov.tDegree := by
  unfold IdCov.tDegree
  fun_prop

@[fun_prop]
private theorem effective_identical_gamma : Effective IdCov.gammaStar := by
  unfold IdCov.gammaStar IdCov.epsilonR
  fun_prop

@[fun_prop]
private theorem effective_identical_tau : Effective IdCov.tauStar := by
  unfold IdCov.tauStar IdCov.epsilonR
  fun_prop

@[fun_prop]
private theorem effective_identical_eta : Effective (fun p : ℚ × ℚ ↦
    IdCov.etaStar p.1 p.2) := by
  unfold IdCov.etaStar IdCov.epsilonSys IdCov.epsilonId IdCov.cStar IdCov.epsilonR
  fun_prop

@[fun_prop]
private theorem effective_terminal : Effective Schedule.terminal := by
  unfold Schedule.terminal
  fun_prop

@[fun_prop]
private theorem effective_step (mode : Mode) :
    Effective (fun p : ℚ × ℕ × StepParams ↦ Schedule.step mode p.1 p.2.1 p.2.2) := by
  cases mode
  all_goals
    unfold Schedule.step
    simp (config := { zeta := false }) only [reduceCtorEq, ite_true, ite_false]
    fun_prop

@[fun_prop]
private theorem effective_params (mode : Mode) :
    Effective (fun p : ℚ × ℕ × ℕ ↦ Schedule.params mode p.1 p.2.1 p.2.2) := by
  unfold Schedule.params
  exact effective_iterate (α := ℚ × ℕ × ℕ) (β := StepParams)
    (f := fun p ↦ p.2.1 - 1 - p.2.2) (g := fun p ↦ Schedule.terminal p.1)
    (h := fun p ↦ Schedule.step mode p.1.1 p.1.2.1 p.2)
    (by fun_prop) (by fun_prop) (by fun_prop)

@[fun_prop]
private theorem effective_etaReq (mode : Mode) :
    Effective (fun p : ℚ × ℕ ↦ Schedule.etaReq mode p.1 p.2) := by
  cases mode
  all_goals
    unfold Schedule.etaReq
    simp (config := { zeta := false }) only [reduceCtorEq, ite_true, ite_false]
    fun_prop

@[fun_prop]
private theorem effective_nWeight (mode : Mode) :
    Effective (fun p : ℚ × ℕ ↦ Schedule.nWeight mode p.1 p.2) := by
  unfold Schedule.nWeight
  fun_prop

@[fun_prop]
private theorem effective_packCount :
    Effective (fun p : ℚ × ℕ ↦ Rounding.packCount p.1 p.2) := by
  unfold Rounding.packCount
  fun_prop

@[fun_prop]
private theorem effective_greedyCap :
    Effective (fun p : ℚ × ℕ ↦ Rounding.greedyCap p.1 p.2) := by
  unfold Rounding.greedyCap Rounding.greedyThreshold
  fun_prop

@[fun_prop]
private theorem effective_rankCap :
    Effective (fun p : ℚ × ℕ ↦ Rounding.rankCap p.1 p.2) := by
  unfold Rounding.rankCap
  fun_prop

@[fun_prop]
private theorem effective_dimensionCap :
    Effective (fun p : ℚ × ℚ × ℚ ↦ Centered.dimensionCap p.1 p.2.1 p.2.2) := by
  unfold Centered.dimensionCap Centered.rankBound Centered.radius Centered.delta Centered.nu
  fun_prop

@[fun_prop]
private theorem effective_netBound : Effective (fun p : ℕ × ℚ ↦ netBound p.1 p.2) := by
  unfold netBound
  fun_prop

@[fun_prop]
private theorem effective_frobCap : Effective frobCap := by
  unfold frobCap
  fun_prop

@[fun_prop]
private theorem effective_stepBranchCap (mode : Mode) :
    Effective (fun p : ℕ × StepParams ↦ stepBranchCap mode p.1 p.2) := by
  cases mode
  all_goals
    unfold stepBranchCap
    simp only [IdCov.N_pack]
    fun_prop

@[fun_prop]
private theorem effective_branchCap (mode : Mode) :
    Effective (fun p : ℚ × ℕ ↦ branchCap mode p.2 (Schedule.params mode p.1 p.2)) := by
  unfold branchCap
  fun_prop

@[fun_prop]
private theorem effective_treeCap (mode : Mode) :
    Effective (fun p : ℚ × ℕ ↦ treeCap mode p.2 (Schedule.params mode p.1 p.2)) := by
  unfold treeCap
  fun_prop


@[fun_prop]
private theorem effective_ledger (mode : Mode) :
    Effective (fun p : ℚ × ℕ ↦ Schedule.ledger mode p.1 p.2) := by
  unfold Schedule.ledger Schedule.ledgerCore
  dsimp only
  fun_prop

/-- The schedule's finite rational arithmetic ledger has a primitive recursive evaluator. -/
theorem H_primrec : Primrec Schedule.H := by
  have h : Effective Schedule.H := by
    unfold Schedule.H
    fun_prop
  obtain ⟨F, hF, eF⟩ := h
  exact hF.of_eq eF

end ABBKS26.Assembly.RunTimeAux
