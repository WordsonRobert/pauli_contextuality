/-
Qm7Data.lean — computable data and Boolean checkers for the certificate deg Q⁻(7,2) ≥ 216
(blueprint GEO-1, GEO-2 in 07_geometry.md; mirrors code/cert216_full.py).

This module imports only Lean core so that it can be compiled to native code
(`precompileModules`); all heavy evaluation in `Qminus.lean` (`native_decide`) happens here.

Points are bit-packed Nats < 256: bits 0..3 = x₁..x₄, bits 4..7 = z₁..z₄.
Point *indices* are positions in `pts` (0..118); line *indices* are positions in `lines` (0..1070).
Nothing about how the data is generated matters for soundness: every property used in the proof
is re-checked by `certificate216`.
-/

namespace PauliCtx.Qm7

/-- Population count of the low 8 bits. -/
def popcount (p : Nat) : Nat := (List.range 8).countP (fun i => p.testBit i)

def xpart (p : Nat) : Nat := p % 16
def zpart (p : Nat) : Nat := p / 16

/-- ω(p,q) as a Bool (odd parity of x·z' + z·x'). -/
def om (p q : Nat) : Bool :=
  (popcount (xpart p &&& zpart q) + popcount (zpart p &&& xpart q)) % 2 == 1

/-- q⁻(x|z) = x·z + x₁ + z₁. -/
def qm (p : Nat) : Bool := (popcount (xpart p &&& zpart p) + (xpart p % 2) + (zpart p % 2)) % 2 == 1

def ycnt (p : Nat) : Nat := popcount (xpart p &&& zpart p)

/-- Sign of a commuting zero-sum triple, via k = y(a)+y(b)+y(c)+2(z_a·x_b + (z_a⊕z_b)·x_c) mod 4. -/
def sgn (a b c : Nat) : Bool :=
  let k := ycnt a + ycnt b + ycnt c
    + 2 * (popcount (zpart a &&& xpart b) + popcount ((zpart a ^^^ zpart b) &&& xpart c))
  k % 4 == 2

def isPt (p : Nat) : Bool := p != 0 && !qm p

/-- Singular points (q⁻ = 0), sorted. -/
def ptsL : List Nat := (List.range 256).filter isPt
def pts : Array Nat := ptsL.toArray

/-- value ↦ index in `pts` (junk 0 for non-points). -/
def idxOf : Array Nat :=
  (List.range 256).toArray.map (fun v => (ptsL.idxOf v))

/-- Lines as sorted triples of point *indices*. -/
def linesL : List (Nat × Nat × Nat) :=
  (List.range 119).flatMap fun i => (List.range 119).filterMap fun j =>
    let a := pts[i]!
    let b := pts[j]!
    if i < j && !om a b && isPt (a ^^^ b) then
      let k := idxOf[a ^^^ b]!
      if j < k then some (i, j, k) else none
    else none

def lines : Array (Nat × Nat × Nat) := linesL.toArray

def nL : Nat := lines.size

/-- The three point indices of line `j`. -/
def lpl (j : Nat) : List Nat := [(lines[j]!).1, (lines[j]!).2.1, (lines[j]!).2.2]

/-- Sign bit of line `j`. -/
def lsgn (j : Nat) : Bool := sgn pts[(lines[j]!).1]! pts[(lines[j]!).2.1]! pts[(lines[j]!).2.2]!

/-- (point index, point index) ↦ index of the line through them (junk 0 otherwise). -/
def lidx : Array Nat := Id.run do
  let mut t := Array.replicate (119 * 119) 0
  for j in [0:lines.size] do
    let (a, b, c) := lines[j]!
    t := t.set! (a * 119 + b) j
    t := t.set! (b * 119 + a) j
    t := t.set! (a * 119 + c) j
    t := t.set! (c * 119 + a) j
    t := t.set! (b * 119 + c) j
    t := t.set! (c * 119 + b) j
  return t

def lineOf (i j : Nat) : Nat := lidx[i * 119 + j]!

/-- line `j` lies in `v^⊥` -/
def perpV (v j : Nat) : Bool := (lpl j).all (fun i => !om pts[i]! v)

/-- line `j` belongs to `O_a` (not contained in `a^⊥`) -/
def inO (a j : Nat) : Bool := !perpV a j

def nonsing : List Nat := (List.range 256).filter (fun p => p != 0 && qm p)

/-! ### Doilies: one per 3-space `T = ⟨c,u,v⟩` (c non-singular radical, ⟨u,v⟩ hyperbolic);
the doily is the set of lines inside `T^⊥`. `(u,v)` is the canonical generator pair of `T`. -/

def canonUV (c u v : Nat) : Bool :=
  let m6 := [v, u ^^^ c, v ^^^ c, u ^^^ v, u ^^^ v ^^^ c]
  let m4 := [v ^^^ c, u ^^^ v, u ^^^ v ^^^ c]
  m6.all (u < ·) && m4.all (v < ·)

def doilyOf (c u v : Nat) : List Nat :=
  (List.range 1071).filter (fun j => perpV c j && perpV u j && perpV v j)

def doilies : List (List Nat) :=
  nonsing.flatMap fun c =>
    (List.range 256).flatMap fun u =>
      if u != 0 && u != c && !om u c then
        (List.range 256).filterMap fun v =>
          if u < v && v != c && !om v c && om u v && canonUV c u v then some (doilyOf c u v) else none
      else []

/-! ### Grids of a doily: one per ordered pair of disjoint lines (each grid arises 6 times). -/

def disjointL (r1 r2 : Nat) : Bool := (lpl r1).all (fun p => !(lpl r2).contains p)

/-- column through point `p` of `r1`: (line index, index of third point) -/
def colOf (p : Nat) (r2 : Nat) : Nat × Nat :=
  match (lpl r2).find? (fun q => !om pts[p]! pts[q]!) with
  | some q => (lineOf p q, idxOf[pts[p]! ^^^ pts[q]!]!)
  | none => (0, 0)

def gridOf (r1 r2 : Nat) : List Nat :=
  let cols := (lpl r1).map (fun p => colOf p r2)
  let r3 := match cols with
    | [(_, t1), (_, t2), _] => lineOf t1 t2
    | _ => 0
  [r1, r2, r3] ++ cols.map (·.1)

def gridsOf (D : List Nat) : List (List Nat) :=
  D.flatMap fun r1 => D.filterMap fun r2 =>
    if r1 < r2 && disjointL r1 r2 then some (gridOf r1 r2) else none

/-- multiset of point indices of a list of lines -/
def ptsOfLines (G : List Nat) : List Nat := G.flatMap lpl

/-- `G` is an odd cycle inside `D`: every point occurs an even number of times, odd sign sum. -/
def gridOK (D G : List Nat) : Bool :=
  G.all (fun j => D.contains j) &&
  (ptsOfLines G).all (fun p => (ptsOfLines G).count p % 2 == 0) &&
  G.countP lsgn % 2 == 1

def doilyOK (D : List Nat) : Bool :=
  D.all (· < nL) &&
  (let gs := gridsOf D
   gs.length == 60 && gs.all (gridOK D) && D.all (fun j => gs.countP (fun G => G.contains j) ≤ 24))

def famO (a : Nat) : List (List Nat) := doilies.filter (fun D => D.all (inO a))

def checkO (a : Nat) : Bool :=
  let fam := famO a
  fam.length == 4032 &&
  (List.range nL).all (fun j => !inO a j || fam.countP (fun D => D.contains j) ≤ 80)

/-- basic well-formedness of the line table -/
def linesOK : Bool :=
  pts.size == 119 && nL == 1071 &&
  (List.range nL).all (fun j =>
    (lines[j]!).1 < (lines[j]!).2.1 && (lines[j]!).2.1 < (lines[j]!).2.2 && (lines[j]!).2.2 < 119) &&
  (List.range nL).all (fun j => (List.range nL).all (fun k => j == k || lines[j]! != lines[k]!))

/-- The full certificate (blueprint GEO-2). -/
def certificate216 : Bool :=
  linesOK &&
  doilies.all doilyOK &&
  nonsing.length == 136 &&
  nonsing.all checkO &&
  (List.range nL).all (fun j => nonsing.countP (fun a => inO a j) ≤ 96)

/-! ### Upper-bound witness (GEO-5): `certificates/witness_Qm7_2.txt` -/

/-- the witness bits, in the point order of `certify.py` (lexicographic in (x₁..x₄,z₁..z₄)) -/
def witnessQm7Py : List Bool := [false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, true, true, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, true, true, true, true, false, true, true, false, false, false, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, false, false, false, false, false, true, false, false, false, true, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false, false, false, false, true, false, false, false, true, false, false]

/-- lexicographic key of a bit-packed point (x₁ most significant) -/
def lexKey (p : Nat) : Nat := (List.range 8).foldl (fun acc i => acc * 2 + (if p.testBit i then 1 else 0)) 0

/-- points in `certify.py` order -/
def ptsPy : List Nat := (ptsL.map (fun p => (lexKey p, p))).mergeSort (fun u v => u.1 ≤ v.1) |>.map (·.2)

/-- witness bit of point index `i` (index into `pts`) -/
def wbit (i : Nat) : Bool := witnessQm7Py.getD (ptsPy.idxOf pts[i]!) false

/-- line `j` is violated by the witness -/
def violW (j : Nat) : Bool :=
  (wbit (lines[j]!).1 ^^ wbit (lines[j]!).2.1 ^^ wbit (lines[j]!).2.2) != lsgn j

def witnessOK : Bool := (List.range nL).countP violW == 315

end PauliCtx.Qm7
