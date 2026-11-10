module

public import ABBKS26.Assembly.ExecNestedAuxData

/-!
# A capped rational list implementation of NestedEncode

Auxiliary variables precede the solver variables during expansion. Coefficient splitting
then deletes that prefix. Products in family substitution are capped per input term, rather
than by enumerating every monomial in all the solver variables.

`NestedSpec.represents` requires exact representation for every valid rational input. Thus
sample-independent magnitude checks and moment rounding belong before this interface; a
builder cannot reject a valid input merely because its coefficients have many bits.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.NestedProgram

open Common Encoding
open SoS.Solver (RawPoly Problem)

/-- Dense exponent vector for a single variable; out-of-range indices give zero. -/
def unitExp (v i e : ℕ) : List ℕ :=
  (List.range v).map fun j ↦ if j = i then e else 0

def constant (c : ℚ) : RawPoly := [([], c)]

def scale (c : ℚ) (p : RawPoly) : RawPoly := p.map fun t ↦ (t.1, c * t.2)

/-- Delete all copies of a cancelled monomial before inspecting its exponents.
This matters for valid inputs containing huge exponents which cancel exactly. -/
def clean (v : ℕ) (p : RawPoly) : RawPoly :=
  (p.filter fun t ↦ SoS.Poly.coeff v p (SoS.Poly.expo v t.1) ≠ 0).map
    fun t ↦ (SoS.Poly.expo v t.1, t.2)

/-- All Gram bases use the existing capped monomial enumerator. -/
def plainBases (I : Rounding.RawInput) : List (List (List ℕ)) :=
  (constant 1 :: I.family.plain).map fun p ↦
    SoS.Mono.allB I.fuel I.family.dimension
      ((I.degree - SoS.Poly.degree I.family.dimension p) / 2)

def familyBases (I : Rounding.RawInput) : List (List (List ℕ)) :=
  I.family.families.map fun p ↦
    SoS.Mono.allB I.fuel I.family.dimension
      ((I.degree - SoS.Poly.degree (2 * I.family.dimension) p) / 2)

/-- This is the same filtering of invalid slot labels as `RawFamily.real`. -/
def slots (I : Rounding.RawInput) : List ℕ :=
  I.family.slots.filter fun a ↦ a < I.family.families.length

def plainStart (I : Rounding.RawInput) (j : ℕ) : ℕ :=
  I.family.dimension + ((plainBases I).take j |>.map fun M ↦ M.length ^ 2).sum

def slotStart (I : Rounding.RawInput) (a : ℕ) : ℕ :=
  plainStart I (plainBases I).length + ((slots I).take a |>.map fun s ↦
    ((familyBases I).getD s []).length ^ 2 + I.family.dimension ^ 2).sum

def numVars (I : Rounding.RawInput) : ℕ := slotStart I (slots I).length

/-- Row-major Gram entries share a column in each quadratic product. -/
def gramRaw (I : Rounding.RawInput) (start : ℕ) (M : List (List ℕ)) : RawPoly :=
  let d := I.family.dimension
  let n := numVars I
  (List.range M.length).flatMap fun c ↦
    let row := M.zipIdx.map fun a ↦
      (a.1 ++ unitExp n (start + a.2 * M.length + c) 1, (1 : ℚ))
    SoS.Coords.mulRaw (d + n) row row

/-- A family variable is replaced by Xi*v, or by the corresponding auxiliary variable. -/
def replacement (I : Rounding.RawInput) (a i : ℕ) : RawPoly :=
  let d := I.family.dimension
  let n := numVars I
  let M := (familyBases I).getD ((slots I).getD a 0) []
  if i < d then
    (List.range d).map fun j ↦
      (unitExp d j 1 ++ unitExp n (slotStart I a + M.length ^ 2 + i * d + j) 1, 1)
  else [(unitExp d (i - d) 1, 1)]

/-- The cap is applied separately to each surviving input term. Exponents are capped
before `replicate`, including on malformed inputs with binary-encoded huge exponents. -/
def substitute (I : Rounding.RawInput) (a : ℕ) (p : RawPoly) : RawPoly :=
  let d := I.family.dimension
  (clean (2 * d) p).flatMap fun t ↦
    scale t.2 (SoS.Poly.prodRaw (d + numVars I) I.fuel
      ((List.range (2 * d)).flatMap fun i ↦
        List.replicate (min (t.1.getD i 0) I.degree) (replacement I a i)))

def templateRaw (I : Rounding.RawInput) : RawPoly :=
  let d := I.family.dimension
  let n := numVars I
  ((constant 1 :: I.family.plain).zipIdx.flatMap fun p ↦
    SoS.Coords.mulRaw (d + n)
      (gramRaw I (plainStart I p.2) ((plainBases I).getD p.2 [])) (clean d p.1)) ++
    ((slots I).zipIdx.flatMap fun a ↦
      SoS.Coords.mulRaw (d + n)
        (gramRaw I (slotStart I a.2) ((familyBases I).getD a.1 []))
        (substitute I a.2 (I.family.families.getD a.1 [])))

/-- The target and the template still have the auxiliary-variable prefix. -/
def residual (I : Rounding.RawInput) : RawPoly :=
  let d := I.family.dimension
  let n := numVars I
  let uv := (List.range d).map fun i ↦
    (unitExp d i 1 ++ unitExp n i 1, (1 : ℚ))
  constant (4 * I.epsilon) ++ scale (-1) (SoS.Coords.mulRaw (d + n) uv uv) ++
    scale (-1) (templateRaw I)

def normRaw (n d : ℕ) : RawPoly :=
  (List.range d).map fun i ↦ (unitExp n i 2, 1)

/-- Sphere pair, paired coefficient equations in canonical order, then the explicit ball. -/
def constraints (I : Rounding.RawInput) : List RawPoly :=
  let n := numVars I
  let sphere := normRaw n I.family.dimension ++ constant (-1)
  [sphere, scale (-1) sphere] ++
    ((SoS.Mono.allB I.fuel I.family.dimension I.degree).flatMap fun μ ↦
      let c := Rounding.splitCoeffsRaw I.family.dimension μ (residual I)
      [c, scale (-1) c]) ++
    [constant I.ball ++ scale (-1) (normRaw n n)]

/-- Preserve the solver's even-degree convention, including unused families. -/
def degree (I : Rounding.RawInput) : ℕ :=
  let outer := 2 + (I.family.families.map
    (SoS.Poly.degree (2 * I.family.dimension))).foldl max 0
  2 * ((2 * I.degree + outer + 1) / 2)

def build (q : NestedArgs × ℕ) : Problem :=
  let I := nestedInput q
  (numVars I, degree I, constraints I, [], [])

def code : NestedCode := ⟨build⟩

end ABBKS26.Assembly.Exec.NestedProgram
