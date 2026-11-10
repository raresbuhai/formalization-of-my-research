module

public import ABBKS26.Assembly.RunTimeAuxPadding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
public import Mathlib.Computability.Partrec

/-! # Computations with a separately accounted size -/

@[expose] public section

namespace ABBKS26.Assembly.RunTimeAuxBudgetAuxCost

open Turing.MultiTapeTM

def Feasible {α β : Type} (size : α → ℕ) (f : α → β)
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) : Prop :=
  ∃ T S, PolyBounded size T ∧ PolyBounded size S ∧
    ComputableInO f encIn encOut T S

namespace Feasible

variable {α β γ : Type} {size : α → ℕ} {size' : β → ℕ}
  {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}

theorem of_polytime {f : α → β} (hf : ComputableInPolyTime f encIn encMid)
    (hlen : PolyBounded size (fun a ↦ (encIn a).length)) :
    Feasible size f encIn encMid := by
  obtain ⟨T, S, hT, hS, h⟩ := hf.exists_computableInO
  exact ⟨T, S, hT.comp hlen, hS.comp hlen, h⟩

theorem resize {f : α → β} {newSize : α → ℕ} (hf : Feasible size f encIn encMid)
    (hs : PolyBounded newSize size) : Feasible newSize f encIn encMid := by
  obtain ⟨T, S, hT, hS, h⟩ := hf
  exact ⟨T, S, hT.comp hs, hS.comp hs, h⟩

theorem comp {f : β → γ} {g : α → β} (hf : Feasible size' f encMid encOut)
    (hg : Feasible size g encIn encMid) (hs : PolyBounded size (fun a ↦ size' (g a))) :
    Feasible size (fun a ↦ f (g a)) encIn encOut := by
  obtain ⟨Tf, Sf, hTf, hSf, hf⟩ := hf
  obtain ⟨Tg, Sg, hTg, hSg, hg⟩ := hg
  exact ⟨_, _, hTg.add (hTf.comp hs), hSg.add (hSf.comp hs), hf.comp hg⟩

theorem length {f : α → β} (hf : Feasible size f encIn encMid) :
    PolyBounded size (fun a ↦ (encMid (f a)).length) := by
  obtain ⟨T, S, _, hS, h⟩ := hf
  obtain ⟨c, hc⟩ := h.length_le
  exact ((PolyBounded.const c).mul (hS.add (.const 1))).mono hc

theorem post {f : β → γ} {g : α → β}
    (hf : ComputableInPolyTime f encMid encOut) (hg : Feasible size g encIn encMid) :
    Feasible size (fun a ↦ f (g a)) encIn encOut :=
  (of_polytime hf .self).comp hg hg.length

theorem prod {δ : Type} {enc₂ : δ ↪ List Bool} {f : α → β} {g : α → δ}
    (hf : Feasible size f encIn encMid) (hg : Feasible size g encIn enc₂) :
    Feasible size (fun a ↦ (f a, g a)) encIn (encPair encMid enc₂) := by
  obtain ⟨Tf, Sf, hTf, hSf, hf⟩ := hf
  obtain ⟨Tg, Sg, hTg, hSg, hg⟩ := hg
  exact ⟨_, _, hTf.add hTg, hSf.add hSg, hf.prod hg⟩

theorem unaryOfBinary {f : α → ℕ} (hf : Feasible size f encIn encNat)
    (hv : PolyBounded size f) : Feasible size f encIn encUnary := by
  have hu : Feasible (id : ℕ → ℕ) id encNat encUnary :=
    ⟨_, _, (PolyBounded.self.add (.const 1)).pow 2, .self, ComputableInO.natToUnary⟩
  exact hu.comp hf hv

theorem add {f g : α → ℕ} (hf : Feasible size f encIn encUnary)
    (hg : Feasible size g encIn encUnary) :
    Feasible size (fun a ↦ f a + g a) encIn encUnary :=
  post ComputableInPolyTime.unary_add (hf.prod hg)

theorem mul {f g : α → ℕ} (hf : Feasible size f encIn encUnary)
    (hg : Feasible size g encIn encUnary) :
    Feasible size (fun a ↦ f a * g a) encIn encUnary :=
  post ComputableInPolyTime.unary_mul (hf.prod hg)

theorem pow_const {f : α → ℕ} (hf : Feasible size f encIn encUnary) (d : ℕ) :
    Feasible size (fun a ↦ f a ^ d) encIn encUnary :=
  post (ComputableInPolyTime.unary_pow d) hf

theorem pow {f g : α → ℕ} (hf : Feasible size f encIn encUnary)
    (hg : Feasible size g encIn encUnary) (hp : PolyBounded size (fun a ↦ f a ^ g a)) :
    Feasible size (fun a ↦ f a ^ g a) encIn encUnary := by
  have hbin : ComputableInPolyTime (fun p : ℕ × ℕ ↦ p.1 ^ p.2)
      (encPair encUnary encUnary) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_pow'
      (ComputableTidilyInPolyTime.unary_to_binary.comp
        (ComputableTidilyInPolyTime.fst encUnary encUnary))
      (ComputableTidilyInPolyTime.snd encUnary encUnary))
  exact (post hbin (hf.prod hg)).unaryOfBinary hp

theorem power_certificate {f : α → β} (hf : Feasible size f encIn encMid)
    (hs : ∀ a, 1 ≤ size a) : ∃ E, ComputableTidilyInO f encIn encMid
      (fun a ↦ size a ^ E) (fun a ↦ size a ^ E) := by
  obtain ⟨T, S, hT, hS, h⟩ := hf
  obtain ⟨ct, dt, hct⟩ := hT.exists_le
  obtain ⟨cs, ds, hcs⟩ := hS.exists_le
  refine ⟨max dt ds, (h.mono (ct * 2 ^ dt + cs * 2 ^ ds) (fun a ↦ ?_)
    (fun a ↦ ?_)).tidy⟩
  · calc T a ≤ ct * (2 * size a) ^ dt :=
          (hct a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hs a; omega) _))
      _ = ct * 2 ^ dt * size a ^ dt := by rw [mul_pow]; ring
      _ ≤ (ct * 2 ^ dt + cs * 2 ^ ds) * (size a ^ max dt ds + 1) :=
        Nat.mul_le_mul (Nat.le_add_right _ _)
          ((Nat.pow_le_pow_right (hs a) (le_max_left _ _)).trans (Nat.le_succ _))
  · calc S a ≤ cs * (2 * size a) ^ ds :=
          (hcs a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hs a; omega) _))
      _ = cs * 2 ^ ds * size a ^ ds := by rw [mul_pow]; ring
      _ ≤ (ct * 2 ^ dt + cs * 2 ^ ds) * (size a ^ max dt ds + 1) :=
        Nat.mul_le_mul (Nat.le_add_left _ _)
          ((Nat.pow_le_pow_right (hs a) (le_max_right _ _)).trans (Nat.le_succ _))

theorem guard {p : α → Prop} [DecidablePred p] {f : α → ℕ} {oldSize : α → ℕ}
    (hc : ComputableInPolyTime (fun a ↦ decide (p a)) encIn encBool)
    (hf : Feasible oldSize f encIn encUnary)
    (hlen : PolyBounded size (fun a ↦ (encIn a).length))
    (hs : ∀ a, p a → oldSize a ≤ size a) :
    Feasible size (fun a ↦ if p a then f a else 0) encIn encUnary := by
  obtain ⟨Tf, Sf, hTf, hSf, hf⟩ := hf
  obtain ⟨Tc, Sc, hTc, hSc, hc⟩ := Feasible.of_polytime hc hlen
  obtain ⟨ct, dt, ht⟩ := hTf.exists_le
  obtain ⟨cs, ds, hsp⟩ := hSf.exists_le
  have ht' : PolyBounded size (fun a ↦ if p a then Tf a else 0) := by
    apply PolyBounded.of_forall_le ct dt
    intro a
    split_ifs with ha
    · exact (ht a).trans (Nat.mul_le_mul_left ct
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hs a ha) 1) dt))
    · exact Nat.zero_le _
  have hs' : PolyBounded size (fun a ↦ if p a then Sf a else 0) := by
    apply PolyBounded.of_forall_le cs ds
    intro a
    split_ifs with ha
    · exact (hsp a).trans (Nat.mul_le_mul_left cs
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hs a ha) 1) ds))
    · exact Nat.zero_le _
  have h := hc.tidy.ite hf.tidy (ComputableTidilyInO.const (encIn := encIn)
    (encMid := encUnary) 0)
  simp only [decide_eq_true_eq] at h
  refine ⟨_, _, ?_, ?_, h.computableInO⟩
  · exact hTc.add ((ht'.add hlen).mono fun a ↦ by split_ifs <;> omega)
  · exact hSc.add ((hs'.add hlen).mono fun a ↦ by split_ifs <;> omega)

end Feasible

private def sqrtStep (n i : ℕ) : ℕ := if (i + 1) * (i + 1) ≤ n then i + 1 else i

private theorem sqrtStep_iterate (n k : ℕ) :
    (sqrtStep n)^[k] 0 = min k n.sqrt := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, sqrtStep]
    split_ifs with h
    · have := Nat.le_sqrt.mpr h
      omega
    · have := mt Nat.le_sqrt.mp h
      omega

theorem sqrt_polytime : ComputableInPolyTime Nat.sqrt encUnary encUnary := by
  have hs : ComputableTidilyInPolyTime (fun p : ℕ × ℕ ↦ sqrtStep p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    unfold sqrtStep
    have hc : ComputableTidilyInPolyTime (fun p : ℕ × ℕ ↦
        decide ((p.2 + 1) * (p.2 + 1) ≤ p.1)) (encPair encUnary encUnary) encBool :=
      ComputableTidilyInPolyTime.unary_le' (by fun_prop) (by fun_prop)
    simpa only [decide_eq_true_eq] using hc.ite'
      (show ComputableTidilyInPolyTime (fun p : ℕ × ℕ ↦ p.2 + 1)
        (encPair encUnary encUnary) encUnary from by fun_prop)
      (ComputableTidilyInPolyTime.snd encUnary encUnary)
  have h := ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
    (par := id) (count := id) (init := fun _ : ℕ ↦ 0) (step := sqrtStep)
    (encIn := encUnary) (encPar := encUnary) (encState := encUnary)
    (by fun_prop) (by fun_prop) (by fun_prop) hs (PolyBounded.const 1)
    (fun n i ↦ by simp only [encUnary_apply, List.length_replicate, sqrtStep]; split_ifs <;>
      omega)
  convert h.computableInPolyTime using 1
  funext n
  exact (sqrtStep_iterate n n).trans (Nat.min_eq_right (Nat.sqrt_le_self n)) |>.symm

theorem unpair_polytime : ComputableInPolyTime Nat.unpair encUnary
    (encPair encUnary encUnary) := by
  have hs := sqrt_polytime.tidy
  apply ComputableInPolyTime.of_tidy
  unfold Nat.unpair
  dsimp only
  have hc : ComputableTidilyInPolyTime (fun n : ℕ ↦ decide (n - n.sqrt * n.sqrt < n.sqrt))
      encUnary encBool := ComputableTidilyInPolyTime.unary_lt' (by fun_prop) hs
  simpa only [decide_eq_true_eq] using hc.ite'
    (show ComputableTidilyInPolyTime (fun n : ℕ ↦ (n - n.sqrt * n.sqrt, n.sqrt))
      encUnary (encPair encUnary encUnary) from by fun_prop)
    (show ComputableTidilyInPolyTime (fun n : ℕ ↦ (n.sqrt, n - n.sqrt * n.sqrt - n.sqrt))
      encUnary (encPair encUnary encUnary) from by fun_prop)

def HasCost (f : ℕ → ℕ) : Prop :=
  Computable f ∧ ∃ t : ℕ → ℕ, Computable t ∧ (∀ n, n + f n + 1 ≤ t n) ∧
    Feasible t (fun n ↦ (f n, t n)) encUnary (encPair encUnary encUnary)

namespace HasCost

attribute [local fun_prop] Computable
attribute [local fun_prop] Computable.id Computable.const Computable.comp Computable.fst
  Computable.snd Computable.pair Computable.unpair

@[local fun_prop]
private theorem computable_add {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun a ↦ f a + g a) :=
  Primrec.nat_add.to_comp.comp hf hg

@[local fun_prop]
private theorem computable_pair {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun a ↦ Nat.pair (f a) (g a)) :=
  Primrec₂.pair.to_comp.comp hf hg

theorem of_polytime {f : ℕ → ℕ} (hf : ComputableInPolyTime f encUnary encUnary)
    (hc : Computable f) : HasCost f := by
  refine ⟨hc, fun n ↦ n + f n + 1,
    Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp .id hc) (.const 1),
    fun _ ↦ le_rfl, ?_⟩
  apply Feasible.of_polytime
  · exact hf.prod (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add' ComputableInPolyTime.id' hf) (.const 1))
  · apply PolyBounded.self.mono
    intro n
    simp only [encUnary_apply, List.length_replicate]
    omega

theorem comp {f g : ℕ → ℕ} (hf : HasCost f) (hg : HasCost g) :
    HasCost (fun n ↦ f (g n)) := by
  obtain ⟨hfc, tf, htfc, htf, hfm⟩ := hf
  obtain ⟨hgc, tg, htgc, htg, hgm⟩ := hg
  let t := fun n ↦ tf (g n) + tg n + 1
  have htf' : PolyBounded t (fun n ↦ tf (g n)) :=
    PolyBounded.self.mono fun n ↦ by dsimp [t]; omega
  have htg' : PolyBounded t tg :=
    PolyBounded.self.mono fun n ↦ by dsimp [t]; omega
  have hgm' := hgm.resize htg'
  have hfm' := hfm.comp
    (Feasible.post (ComputableInPolyTime.fst encUnary encUnary) hgm') htf'
  refine ⟨hfc.comp hgc, t,
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp (htfc.comp hgc) htgc) (.const 1), ?_, ?_⟩
  · intro n
    have := htf (g n)
    have := htg n
    dsimp [t]
    omega
  · exact Feasible.post (f := fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦
        (p.2.1, p.2.2 + p.1.2 + 1))
      (ComputableInPolyTime.of_tidy (by fun_prop)) (hgm'.prod hfm')

theorem pair {f g : ℕ → ℕ} (hf : HasCost f) (hg : HasCost g) :
    HasCost (fun n ↦ Nat.pair (f n) (g n)) := by
  obtain ⟨hfc, tf, htfc, htf, hfm⟩ := hf
  obtain ⟨hgc, tg, htgc, htg, hgm⟩ := hg
  let t := fun n ↦ Nat.pair (f n) (g n) + tf n + tg n + 1
  have htf' : PolyBounded t tf :=
    PolyBounded.self.mono fun n ↦ by dsimp [t]; omega
  have htg' : PolyBounded t tg :=
    PolyBounded.self.mono fun n ↦ by dsimp [t]; omega
  have hp := Primrec₂.pair.to_comp.comp hfc hgc
  refine ⟨hp, t, Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp hp htfc) htgc)
      (.const 1), ?_, ?_⟩
  · intro n
    have := htf n
    dsimp [t]
    omega
  · exact Feasible.post (f := fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦
        (Nat.pair p.1.1 p.2.1, Nat.pair p.1.1 p.2.1 + p.1.2 + p.2.2 + 1))
      (ComputableInPolyTime.of_tidy (by fun_prop))
      ((hfm.resize htf').prod (hgm.resize htg'))

private abbrev State := ℕ × ℕ × ℕ
private abbrev encState := encPair encUnary (encPair encUnary encUnary)

private theorem length_encState (s : State) :
    (encState s).length = 2 * s.1 + 2 * s.2.1 + s.2.2 + 2 := by
  change (encPair encUnary (encPair encUnary encUnary) s).length = _
  simp only [length_encPair, encUnary_apply, List.length_replicate]
  omega

private def recStep (g tg : ℕ → ℕ) (a : ℕ) (s : State) : State :=
  let arg := Nat.pair a (Nat.pair s.1 s.2.1)
  (s.1 + 1, g arg, s.2.2 + a + s.1 + s.2.1 + tg arg + 1)

private def recState (f tf g tg : ℕ → ℕ) (a : ℕ) : ℕ → State
  | 0 => (0, f a, a + tf a + 1)
  | n + 1 => recStep g tg a (recState f tf g tg a n)

private theorem recState_iterate (f tf g tg : ℕ → ℕ) (a n : ℕ) :
    (recStep g tg a)^[n] (0, f a, a + tf a + 1) = recState f tf g tg a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

private theorem recState_fst (f tf g tg : ℕ → ℕ) (a n : ℕ) :
    (recState f tf g tg a n).1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recState, recStep, ih]

private theorem recState_bound (f tf g tg : ℕ → ℕ)
    (htf : ∀ a, a + f a + 1 ≤ tf a) (htg : ∀ a, a + g a + 1 ≤ tg a) (a n : ℕ) :
    a + n + (recState f tf g tg a n).2.1 + 1 ≤ (recState f tf g tg a n).2.2 := by
  cases n with
  | zero => dsimp [recState]; have := htf a; omega
  | succ n =>
    have h := htg (Nat.pair a (Nat.pair (recState f tf g tg a n).1
      (recState f tf g tg a n).2.1))
    dsimp [recState, recStep]
    rw [recState_fst] at h ⊢
    omega

private theorem recState_mono (f tf g tg : ℕ → ℕ) (a : ℕ) :
    Monotone (fun n ↦ (recState f tf g tg a n).2.2) := by
  apply monotone_nat_of_le_succ
  intro n
  dsimp [recState, recStep]
  omega

private theorem recState_value (f tf g tg : ℕ → ℕ) (a n : ℕ) :
    (recState f tf g tg a n).2.1 =
      Nat.rec (f a) (fun i v ↦ g (Nat.pair a (Nat.pair i v))) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recState, recStep, recState_fst, ih]

private theorem recState_computable {f tf g tg : ℕ → ℕ}
    (hf : Computable f) (htf : Computable tf) (hg : Computable g) (htg : Computable tg) :
    Computable (fun p : ℕ × ℕ ↦ recState f tf g tg p.1 p.2) := by
  have ha : Computable (fun p : ℕ × State ↦
      Nat.pair p.1 (Nat.pair p.2.1 p.2.2.1)) :=
    computable_pair Computable.fst (computable_pair (Computable.fst.comp Computable.snd)
      (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hstep : Computable (fun p : ℕ × State ↦ recStep g tg p.1 p.2) := by
    exact Computable.pair
      (computable_add (Computable.fst.comp Computable.snd) (.const 1))
      ((hg.comp ha).pair
        (computable_add
          (computable_add
            (computable_add
              (computable_add
                (computable_add (Computable.snd.comp (Computable.snd.comp Computable.snd))
                  Computable.fst) (Computable.fst.comp Computable.snd))
              (Computable.fst.comp (Computable.snd.comp Computable.snd))) (htg.comp ha))
          (.const 1)))
  have h : Computable (fun p : ℕ × ℕ ↦
    Nat.rec (motive := fun _ ↦ State) (0, f p.1, p.1 + tf p.1 + 1)
      (fun _ s ↦ recStep g tg p.1 s) p.2) := by
    refine Computable.nat_rec (f := Prod.snd)
      (g := fun p : ℕ × ℕ ↦ (0, f p.1, p.1 + tf p.1 + 1))
      (h := fun p : ℕ × ℕ ↦ fun q : ℕ × State ↦ recStep g tg p.1 q.2)
      Computable.snd (by fun_prop) ?_
    exact (hstep.comp ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.comp Computable.snd))).to₂
  apply h.of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => simp only [recState, ih]

private theorem recStep_feasible {g tg : ℕ → ℕ}
    (hm : Feasible tg (fun n ↦ (g n, tg n)) encUnary (encPair encUnary encUnary)) :
    Feasible (fun p : ℕ × State ↦ (recStep g tg p.1 p.2).2.2)
      (fun p : ℕ × State ↦ recStep g tg p.1 p.2)
      (encPair encUnary encState) encState := by
  let arg := fun p : ℕ × State ↦ Nat.pair p.1 (Nat.pair p.2.1 p.2.2.1)
  let size := fun p : ℕ × State ↦ (recStep g tg p.1 p.2).2.2
  have hlen : PolyBounded size (fun p ↦ (encPair encUnary encState p).length) := by
    apply PolyBounded.of_forall_le 16 1
    intro p
    simp only [length_encPair, encUnary_apply, List.length_replicate, pow_one]
    dsimp [size, recStep]
    omega
  have ha : Feasible size arg (encPair encUnary encState) encUnary :=
    Feasible.of_polytime (ComputableInPolyTime.of_tidy (by dsimp [arg]; fun_prop)) hlen
  have hm' := hm.comp ha (PolyBounded.self.mono (fun p ↦ by
    dsimp [size, recStep, arg]
    omega))
  have hid : Feasible size id (encPair encUnary encState) (encPair encUnary encState) :=
    Feasible.of_polytime ComputableInPolyTime.id' hlen
  exact Feasible.post (f := fun p : (ℕ × State) × (ℕ × ℕ) ↦
      (p.1.2.1 + 1, p.2.1,
        p.1.2.2.2 + p.1.1 + p.1.2.1 + p.1.2.2.1 + p.2.2 + 1))
    (ComputableInPolyTime.of_tidy (by fun_prop)) (hid.prod hm')

theorem prec {f g : ℕ → ℕ} (hf : HasCost f) (hg : HasCost g) :
    HasCost (Nat.unpaired fun a n ↦
      Nat.rec (motive := fun _ ↦ ℕ) (f a) (fun i v ↦ g (Nat.pair a (Nat.pair i v))) n) := by
  obtain ⟨hfc, tf, htfc, htf, hfm⟩ := hf
  obtain ⟨hgc, tg, htgc, htg, hgm⟩ := hg
  let st := recState f tf g tg
  let t := fun m ↦ m + (st m.unpair.1 m.unpair.2).2.2 + 1
  have hstc := recState_computable hfc htfc hgc htgc
  have htc : Computable t := by dsimp [t, st]; fun_prop
  have hval := recState_value f tf g tg
  have hc : Computable (Nat.unpaired fun a n ↦
      Nat.rec (motive := fun _ ↦ ℕ) (f a) (fun i v ↦ g (Nat.pair a (Nat.pair i v))) n) := by
    have h := Computable.fst.comp (Computable.snd.comp (hstc.comp Computable.unpair))
    exact h.of_eq fun m ↦ hval m.unpair.1 m.unpair.2
  have hdom (m : ℕ) : m + (st m.unpair.1 m.unpair.2).2.1 + 1 ≤ t m := by
    have := recState_bound f tf g tg htf htg m.unpair.1 m.unpair.2
    dsimp [t, st]
    omega
  refine ⟨hc, t, htc, fun m ↦ by simpa only [Nat.unpaired, ← hval] using hdom m, ?_⟩
  have hlen : PolyBounded t (fun m ↦ (encUnary m).length) :=
    PolyBounded.self.mono fun m ↦ by
      simp only [encUnary_apply, List.length_replicate]
      have := hdom m
      omega
  have hpair : Feasible t Nat.unpair encUnary (encPair encUnary encUnary) :=
    Feasible.of_polytime unpair_polytime hlen
  have hpar := Feasible.post (ComputableInPolyTime.fst encUnary encUnary) hpair
  have hcount := Feasible.post (ComputableInPolyTime.snd encUnary encUnary) hpair
  have hf' := hfm.comp hpar (PolyBounded.self.mono fun m ↦ by
    have h₁ := recState_mono f tf g tg m.unpair.1 (Nat.zero_le m.unpair.2)
    change tf m.unpair.1 ≤ t m
    dsimp [recState] at h₁
    dsimp [t, st]
    omega)
  have hi := Feasible.post (encOut := encState) (f := fun p : ℕ × (ℕ × ℕ) ↦
      (0, p.2.1, p.1 + p.2.2 + 1))
    (ComputableInPolyTime.of_tidy (by fun_prop)) (hpar.prod hf')
  have hl := Feasible.post (f := fun n : ℕ ↦ List.replicate n true)
    (show ComputableInPolyTime (fun n : ℕ ↦ List.replicate n true) encUnary encBits from
      .of_eq fun _ ↦ rfl) hcount
  have hplen := hpar.length
  have hllen := hl.length
  obtain ⟨Tp, Sp, hTp, hSp, hp⟩ := hpar
  obtain ⟨Tl, Sl, hTl, hSl, hlm⟩ := hl
  obtain ⟨Ti, Si, hTi, hSi, him⟩ := hi
  obtain ⟨Ts, Ss, hTs, hSs, hsm⟩ := recStep_feasible hgm
  obtain ⟨ct, dt, hct⟩ := hTs.exists_le
  obtain ⟨cs, ds, hcs⟩ := hSs.exists_le
  let R := fun m ↦ ct * (t m + 1) ^ dt
  let Q := fun m ↦ cs * (t m + 1) ^ ds
  let B := fun m ↦ 16 * (t m + 1)
  have hfold (m i : ℕ) (hi : i ≤ m.unpair.2) :
      ((List.replicate m.unpair.2 true).take i).foldl
        (fun s _ ↦ recStep g tg m.unpair.1 s)
        (0, f m.unpair.1, m.unpair.1 + tf m.unpair.1 + 1) = st m.unpair.1 i := by
    rw [List.take_replicate, List.foldl_const, List.length_replicate, Nat.min_eq_left hi]
    exact recState_iterate f tf g tg _ _
  have hnext (m i : ℕ) (hi : i < m.unpair.2) :
      (recStep g tg m.unpair.1 (st m.unpair.1 i)).2.2 ≤ t m := by
    change (st m.unpair.1 (i + 1)).2.2 ≤ t m
    have := recState_mono f tf g tg m.unpair.1 (by omega : i + 1 ≤ m.unpair.2)
    dsimp [t, st] at *
    omega
  have hstate (m i : ℕ) (hi : i ≤ m.unpair.2) :
      (encState (st m.unpair.1 i)).length ≤ B m := by
    have h₁ := recState_mono f tf g tg m.unpair.1 hi
    have h₂ := recState_bound f tf g tg htf htg m.unpair.1 i
    rw [length_encState]
    dsimp [B, t, st] at *
    rw [recState_fst]
    omega
  have hsm' := hsm.comp (ComputableInO.fst (encPair encUnary encState) encBool)
  have hloop := ComputableInO.foldlWith (par := fun m : ℕ ↦ m.unpair.1)
    (list := fun m : ℕ ↦ List.replicate m.unpair.2 true)
    (init := fun m : ℕ ↦ (0, f m.unpair.1, m.unpair.1 + tf m.unpair.1 + 1))
    (step := fun a s (_ : Bool) ↦ recStep g tg a s)
    hp hlm him hsm' (R := fun m ↦ 64 * (t m + 1) + R m)
    (Q := fun m ↦ 64 * (t m + 1) + Q m) (B := B)
    (fun m i hi ↦ by
      simp only [List.length_replicate] at hi
      simp only [List.getElem_replicate]
      rw [hfold m i (by omega)]
      have h := hct (m.unpair.1, st m.unpair.1 i)
      have hb := hstate m i (by omega)
      have ha := recState_bound f tf g tg htf htg m.unpair.1 m.unpair.2
      dsimp [R]
      apply Nat.add_le_add
      · simp only [length_encPair, encBool_apply, List.length_singleton,
          encUnary_apply, List.length_replicate, List.length_append, length_frame] at *
        dsimp [B, t, st] at *
        omega
      · exact h.trans (Nat.mul_le_mul_left ct
          (Nat.pow_le_pow_left (Nat.add_le_add_right (hnext m i hi) 1) dt)))
    (fun m i hi ↦ by
      simp only [List.length_replicate] at hi
      simp only [List.getElem_replicate]
      rw [hfold m i (by omega)]
      have h := hcs (m.unpair.1, st m.unpair.1 i)
      have hb := hstate m i (by omega)
      have ha := recState_bound f tf g tg htf htg m.unpair.1 m.unpair.2
      dsimp [Q]
      apply Nat.add_le_add
      · simp only [length_encPair, encBool_apply, List.length_singleton,
          encUnary_apply, List.length_replicate, List.length_append, length_frame] at *
        dsimp [B, t, st] at *
        omega
      · exact h.trans (Nat.mul_le_mul_left cs
          (Nat.pow_le_pow_left (Nat.add_le_add_right (hnext m i hi) 1) ds)))
    (fun m i hi ↦ by
      simp only [List.length_replicate] at hi
      rw [hfold m i hi]
      exact hstate m i hi)
  have hn : PolyBounded t (fun m ↦ m.unpair.2) := PolyBounded.self.mono fun m ↦ by
    have := Nat.unpair_right_le m
    dsimp [t]
    omega
  have hR : PolyBounded t R := (PolyBounded.const ct).mul
    ((PolyBounded.self.add (.const 1)).pow dt)
  have hQ : PolyBounded t Q := (PolyBounded.const cs).mul
    ((PolyBounded.self.add (.const 1)).pow ds)
  have hB : PolyBounded t B := (PolyBounded.const 16).mul
    (PolyBounded.self.add (.const 1))
  have h64 : PolyBounded t (fun m ↦ 64 * (t m + 1)) := (PolyBounded.const 64).mul
    (PolyBounded.self.add (.const 1))
  have hloop' : Feasible t (fun m ↦ st m.unpair.1 m.unpair.2) encUnary encState := by
    refine ⟨_, _, ?_, ?_, hloop.of_enc_eq (fun m ↦ ?_)⟩
    · simpa only [List.length_replicate] using ((hTp.add hTl).add hTi).add
        ((hn.add (.const 1)).mul (((h64.add hR).add hB).add hplen |>.add hllen))
    · exact ((((((hSp.add hSl).add hSi).add (h64.add hQ)).add hB).add hplen).add hllen)
    · rw [List.foldl_const, List.length_replicate, recState_iterate]
  have hid : Feasible t id encUnary encUnary := Feasible.of_polytime
    ComputableInPolyTime.id' hlen
  have hout := Feasible.post (encOut := encPair encUnary encUnary)
    (f := fun p : ℕ × State ↦ (p.2.2.1, p.1 + p.2.2.2 + 1))
    (ComputableInPolyTime.of_tidy (by fun_prop)) (hid.prod hloop')
  simpa only [id_eq, st, recState_value, t, Nat.unpaired] using hout

end HasCost

/-- An evaluator can carry a computable account of all its intermediate work. -/
theorem primrec_hasCost {f : ℕ → ℕ} (hf : Primrec f) : HasCost f := by
  have hnat := Primrec.nat_iff.mp hf
  clear hf
  induction hnat with
  | zero => exact HasCost.of_polytime (.const 0) (.const 0)
  | succ =>
    exact HasCost.of_polytime
      (ComputableInPolyTime.of_tidy (by
        change ComputableTidilyInPolyTime (fun n : ℕ ↦ n + 1) encUnary encUnary
        fun_prop)) Primrec.succ.to_comp
  | left =>
    exact HasCost.of_polytime
      ((ComputableInPolyTime.fst encUnary encUnary).comp unpair_polytime)
      (Computable.fst.comp Computable.unpair)
  | right =>
    exact HasCost.of_polytime
      ((ComputableInPolyTime.snd encUnary encUnary).comp unpair_polytime)
      (Computable.snd.comp Computable.unpair)
  | pair _ _ ihf ihg => exact ihf.pair ihg
  | comp _ _ ihf ihg => exact ihf.comp ihg
  | prec _ _ ihf ihg => exact ihf.prec ihg

open Encoding (encRat)

private theorem input_tuple_polytime : ComputableInPolyTime
    (fun x : Input ↦ (x.k, x.wmin, x.Δ, x.δ, x.points)) encInput
    (encPair encNat (encPair encRat (encPair encRat (encPair encRat encPoints)))) :=
  .of_eq fun _ ↦ rfl

@[fun_prop]
theorem wmin_polytime : ComputableInPolyTime Input.wmin encInput encRat :=
  (ComputableInPolyTime.fst _ _).comp
    ((ComputableInPolyTime.snd _ _).comp input_tuple_polytime)

@[fun_prop]
theorem delta_polytime : ComputableInPolyTime Input.δ encInput encRat :=
  (ComputableInPolyTime.fst _ _).comp
    ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp input_tuple_polytime)))

@[fun_prop]
theorem dim_polytime : ComputableInPolyTime (fun x : Input ↦ dim x.points)
    encInput encUnary :=
  (ComputableInPolyTime.length_list encRat).comp
    ((ComputableInPolyTime.headD (encA := encList encRat)
      (encL := encList (encList encRat)) []).comp Exec.points_polytime)

@[fun_prop]
theorem input_length_polytime : ComputableInPolyTime (fun x : Input ↦ (encInput x).length)
    encInput encUnary :=
  ComputableInPolyTime.length_bits.comp (.of_eq fun _ ↦ rfl)

theorem rat_ceil_polytime : ComputableInPolyTime (fun q : ℚ ↦ ⌈q⌉₊) encRat encNat := by
  have h := ComputableInPolyTime.intBin_toNat.comp
    (show ComputableInPolyTime (fun q : ℚ ↦ -⌊-q⌋) encRat encIntBin from by fun_prop)
  change ComputableInPolyTime (fun q : ℚ ↦ (⌈q⌉ : ℤ).toNat) encRat encNat at h
  simpa only [Int.ceil_toNat] using h

@[fun_prop]
theorem parameter_polytime : ComputableInPolyTime (fun x : Input ↦ ⌈1 / x.wmin⌉₊)
    encInput encNat := rat_ceil_polytime.comp (by fun_prop)

theorem valid_polytime : ComputableInPolyTime (fun x : Input ↦ decide (Exec.Valid x))
    encInput encBool := by
  have hrect : ComputableTidilyInPolyTime
      (fun x : Input ↦ x.points.all fun row ↦ decide (row.length = dim x.points))
      encInput encBool :=
    ComputableTidilyInPolyTime.allWith
      (test := fun p : ℕ × List ℚ ↦ decide (p.2.length = p.1))
      (ComputableTidilyInPolyTime.decide_eq'
        ((ComputableTidilyInPolyTime.length_list encRat).comp
          (ComputableTidilyInPolyTime.snd encUnary (encList encRat)))
        (ComputableTidilyInPolyTime.fst encUnary (encList encRat)))
      dim_polytime.tidy Exec.points_polytime.tidy
  have hrect' : ComputableTidilyInPolyTime
      (fun x : Input ↦ decide (∀ row ∈ x.points, row.length = dim x.points))
      encInput encBool := by
    convert hrect using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp
  have h0 := ComputableInPolyTime.rat_lt' (ComputableInPolyTime.const 0) wmin_polytime
  have h1 := ComputableInPolyTime.rat_le' wmin_polytime (ComputableInPolyTime.const 1)
  have h2 := ComputableInPolyTime.rat_le'
    (ComputableInPolyTime.rat_mul' (ComputableInPolyTime.rat_natCast' Exec.k_polytime)
      wmin_polytime) (ComputableInPolyTime.const 1)
  have h3 := ComputableTidilyInPolyTime.binary_le' (ComputableTidilyInPolyTime.const 1)
    Exec.k_polytime.tidy
  have h4 := ComputableInPolyTime.rat_lt' (ComputableInPolyTime.const 0) delta_polytime
  exact .of_tidy (h0.tidy.decide_and (h1.tidy.decide_and
    (h2.tidy.decide_and (h3.decide_and (h4.tidy.decide_and hrect')))))

end ABBKS26.Assembly.RunTimeAuxBudgetAuxCost
