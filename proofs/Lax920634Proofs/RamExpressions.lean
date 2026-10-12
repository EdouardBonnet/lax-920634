import Lax920634Proofs.RamArithmetic

namespace Lax920634Proofs.RamExpressions

set_option maxHeartbeats 600000

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax920634.ZigZagConstruction RamArithmetic

local notation "D" => Lax920634.SeedSearch.seedDegree
local notation "d" => Lax920634.ZigZagConstruction.degree
local notation "b" => Lax920634.SeedSearch.seedDegree ^ 4

attribute [local irreducible] Lax920634.SeedSearch.seedDegree Lax920634.SeedSearch.poweringExponent

/-- Remainder is implemented using registered division, multiplication and subtraction. -/
def rem (e : Expr) (r : ℕ) : Expr := .sub e (.mul (.div e (.lit r)) (.lit r))

/-- An indexed lookup in a packed rotation table. -/
def lookup (a : String) (off : Expr) (r : ℕ) (v i : Expr) : Expr :=
  .get a (.add off (.add (.mul v (.lit r)) i))

def seedLookup (v i : Expr) : Expr := lookup "seed" (.lit 0) D v i

def previousLookup (v i : Expr) : Expr := lookup "table" (.var "start") d v i

/-- Evaluate the next rotation using a fixed expression of indexed table accesses. -/
def nextRow : Expr :=
  let v := .div (.var "j") (.lit d)
  let i := rem (.var "j") d
  let p := seedLookup (rem v b) (.div i (.lit D))
  let q₀ := previousLookup (.div v (.lit b)) (.div (.div p (.lit D)) (.lit d))
  let q₁ := previousLookup (.div q₀ (.lit d)) (rem (.div p (.lit D)) d)
  let r := seedLookup (.add (rem q₀ d) (.mul (.lit d) (rem q₁ d))) (rem i D)
  .add (.add (rem p D) (.mul (.lit D) (rem r D)))
    (.mul (.lit d) (.add (.div r (.lit D)) (.mul (.lit b) (.div q₁ (.lit d)))))

/-- The fixed seed array contains its complete packed rotation. -/
def SeedTable (σ : Env) : Prop := ∀ v < b, ∀ i < D,
  (σ.arrs "seed")[v * D + i]? = some (pack D (seedValue (v,i)))

/-- A materialized regular rotation table at one level. -/
def RotationTable (k off : ℕ) (σ : Env) : Prop := ∀ j < order k,
  (σ.arrs "table")[off + j]? = some (matchingNeighbor k j)

variable {B : ℕ} {σ : Env} {e f : Expr} {m n : ℕ}

theorem eval_add (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n)
    (h : m+n < B) : (Expr.add e f).evalB B σ = some (m+n) := evalB_bin he hf h

theorem eval_mul (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n)
    (h : m*n < B) : (Expr.mul e f).evalB B σ = some (m*n) := evalB_bin he hf h

theorem eval_div (he : e.evalB B σ = some m) (r : ℕ) (hr : r < B) :
    (Expr.div e (.lit r)).evalB B σ = some (m/r) := by
  exact evalB_bin he (evalB_lit hr) ((Nat.div_le_self _ _).trans_lt (Expr.lt_of_evalB he))

theorem eval_rem (he : e.evalB B σ = some m) (r : ℕ) (hr : r < B) :
    (rem e r).evalB B σ = some (m%r) := by
  have hm := Expr.lt_of_evalB he
  have hp : m/r*r ≤ m := Nat.div_mul_le_self _ _
  have hh := eval_mul (eval_div he r hr) (evalB_lit hr) (hp.trans_lt hm)
  have hsub := evalB_bin (op := .sub) he hh ((Nat.sub_le _ _).trans_lt hm)
  have heq : m - m/r*r = m%r := by
    have h := Nat.mod_add_div m r
    rw [Nat.mul_comm r (m/r)] at h
    omega
  simpa only [rem, Bop.apply_sub, heq] using hsub

theorem eval_lookup {a : String} {off v i : Expr} {o x y r z : ℕ}
    (ho : off.evalB B σ = some o) (hv : v.evalB B σ = some x)
    (hi : i.evalB B σ = some y) (hr : r < B)
    (hindex : o + (x*r+y) < B)
    (hget : (σ.arrs a)[o+(x*r+y)]? = some z) (hz : z < B) :
    (lookup a off r v i).evalB B σ = some z := by
  apply evalB_get (v := z) (hv := hz)
  · exact eval_add ho (eval_add (eval_mul hv (evalB_lit hr) (by omega)) hi (by omega)) hindex
  · exact hget

theorem eval_seed {v i : Expr} {x y : ℕ} (hT : SeedTable σ)
    (hv : v.evalB B σ = some x) (hi : i.evalB B σ = some y)
    (hx : x < b) (hy : y < D) (hsize : b*D < B) :
    (seedLookup v i).evalB B σ = some (pack D (seedValue (x,y))) := by
  have hp := seed_bounds x y hx hy
  have hindex : x*D+y < b*D := by nlinarith
  exact eval_lookup (evalB_lit (by have := D_pos; omega)) hv hi
    (by have := D_pos; have := b_ge_two; nlinarith)
    (by simpa using hindex.trans hsize) (by simpa using hT x hx y hy)
    ((pack_lt hp.1 hp.2).trans hsize)

theorem eval_previous {v i : Expr} {k off x y : ℕ} (hT : RotationTable k off σ)
    (hstart : σ.vars "start" = off)
    (hv : v.evalB B σ = some x) (hi : i.evalB B σ = some y)
    (hx : x < baseOrder k) (hy : y < d) (hsize : off+order k < B) :
    (previousLookup v i).evalB B σ = some (pack d (rotation k (x,y))) := by
  have hindex : x*d+y < order k := by unfold order; nlinarith
  have hp := rotation_bounds k x y hx hy
  have hz : pack d (rotation k (x,y)) < order k := pack_lt hp.1 hp.2
  have hs : (Expr.var "start").evalB B σ = some off := by
    simpa only [hstart] using evalB_var (show σ.vars "start" < B by rw [hstart]; omega)
  exact eval_lookup hs hv hi
    (by have := Tower.baseOrder_pos k; have := d_pos; unfold order at hsize; nlinarith)
    (by omega) (by simpa only [packed_rotation k x y hy, Nat.add_assoc] using hT _ hindex)
    (by omega)

theorem eval_fst {r : ℕ} {p : ℕ × ℕ} (he : e.evalB B σ = some (pack r p))
    (hr : 0 < r) (hrB : r < B) (hi : p.2 < r) :
    (Expr.div e (.lit r)).evalB B σ = some p.1 := by
  have h : pack r p / r = p.1 := congrArg Prod.fst (unpack_pack hr p hi)
  simpa only [h] using eval_div he r hrB

theorem eval_snd {r : ℕ} {p : ℕ × ℕ} (he : e.evalB B σ = some (pack r p))
    (hr : 0 < r) (hrB : r < B) (hi : p.2 < r) :
    (rem e r).evalB B σ = some p.2 := by
  have h : pack r p % r = p.2 := congrArg Prod.snd (unpack_pack hr p hi)
  simpa only [h] using eval_rem he r hrB

theorem nextRow_eval (k off j : ℕ) (hseed : SeedTable σ)
    (hprevious : RotationTable k off σ) (hstart : σ.vars "start" = off)
    (hjvar : σ.vars "j" = j) (hj : j < order (k+1))
    (hsize : off + order (k+1) < B) :
    nextRow.evalB B σ = some (matchingNeighbor (k+1) j) := by
  have hkN : order k ≤ order (k+1) := order_mono (by omega : k ≤ k+1)
  have hbaseB : baseOrder (k+1) < B := (Nat.le_mul_of_pos_right _ d_pos).trans_lt (show order (k+1) < B by omega)
  have hbB : b < B := lt_of_le_of_lt (b_le_order (k+1)) (by omega)
  have hdB : d < B := lt_of_le_of_lt d_le_b hbB
  have hDB : D < B := lt_of_le_of_lt D_le_b hbB
  have hseedB : b*D < B := lt_of_le_of_lt (seed_size_le_order (k+1)) (by omega)
  let v := j/d
  let i := j%d
  have hv : v < baseOrder (k+1) := (Nat.div_lt_iff_lt_mul d_pos).2 hj
  have hi : i < d := Nat.mod_lt _ d_pos
  have hx : v/b < baseOrder k := (Nat.div_lt_iff_lt_mul (by have := b_ge_two; omega)).2
    (by simpa only [baseOrder_succ] using hv)
  have hpv : v%b < b := Nat.mod_lt _ (by have := b_ge_two; omega)
  have hpi : i/D < D := (Nat.div_lt_iff_lt_mul D_pos).2 (by simpa only [d_eq] using hi)
  let p := seedValue (v%b,i/D)
  have hp : p.1 < b ∧ p.2 < D := seed_bounds _ _ hpv hpi
  have hq₀i : p.1/d < d := (Nat.div_lt_iff_lt_mul d_pos).2 (by rw [← b_eq]; exact hp.1)
  let q₀ := rotation k (v/b,p.1/d)
  have hq₀ : q₀.1 < baseOrder k ∧ q₀.2 < d := rotation_bounds k _ _ hx hq₀i
  have hq₁i : p.1%d < d := Nat.mod_lt _ d_pos
  let q₁ := rotation k (q₀.1,p.1%d)
  have hq₁ : q₁.1 < baseOrder k ∧ q₁.2 < d := rotation_bounds k _ _ hq₀.1 hq₁i
  have hrx : q₀.2+d*q₁.2 < b :=
    lt_of_lt_of_eq (pack_lt (p := (q₁.2,q₀.2)) hq₁.2 hq₀.2) b_eq.symm
  have hri : i%D < D := Nat.mod_lt _ D_pos
  let r := seedValue (q₀.2+d*q₁.2,i%D)
  have hr : r.1 < b ∧ r.2 < D := seed_bounds _ _ hrx hri
  have houtv : r.1+b*q₁.1 < baseOrder (k+1) :=
    lt_of_lt_of_eq (pack_lt (p := (q₁.1,r.1)) hq₁.1 hr.1) (baseOrder_succ k).symm
  have houti : p.2+D*r.2 < d :=
    lt_of_lt_of_eq (pack_lt (p := (r.2,p.2)) hr.2 hp.2) d_eq.symm
  have hout : (p.2+D*r.2)+d*(r.1+b*q₁.1) < order (k+1) := by
    exact pack_lt (p := (r.1+b*q₁.1,p.2+D*r.2)) houtv houti
  have ej : (Expr.var "j").evalB B σ = some j := by rw [← hjvar]; exact evalB_var (by omega)
  let ev := Expr.div (.var "j") (.lit d)
  let ei := rem (.var "j") d
  have evh : ev.evalB B σ = some v := eval_div ej d hdB
  have eih : ei.evalB B σ = some i := eval_rem ej d hdB
  let ep := seedLookup (rem ev b) (.div ei (.lit D))
  have eph : ep.evalB B σ = some (pack D p) :=
    eval_seed hseed (eval_rem evh b hbB) (eval_div eih D hDB) hpv hpi hseedB
  have epvh := eval_fst eph D_pos hDB hp.2
  have epih := eval_snd eph D_pos hDB hp.2
  let eq₀ := previousLookup (.div ev (.lit b)) (.div (.div ep (.lit D)) (.lit d))
  have eq₀h : eq₀.evalB B σ = some (pack d q₀) :=
    eval_previous hprevious hstart (eval_div evh b hbB) (eval_div epvh d hdB) hx hq₀i (by omega)
  have eq₀vh := eval_fst eq₀h d_pos hdB hq₀.2
  have eq₀ih := eval_snd eq₀h d_pos hdB hq₀.2
  let eq₁ := previousLookup (.div eq₀ (.lit d)) (rem (.div ep (.lit D)) d)
  have eq₁h : eq₁.evalB B σ = some (pack d q₁) :=
    eval_previous hprevious hstart eq₀vh (eval_rem epvh d hdB) hq₀.1 hq₁i (by omega)
  have eq₁vh := eval_fst eq₁h d_pos hdB hq₁.2
  have eq₁ih := eval_snd eq₁h d_pos hdB hq₁.2
  let er := seedLookup (.add (rem eq₀ d) (.mul (.lit d) (rem eq₁ d))) (rem ei D)
  have erxh := eval_add eq₀ih (eval_mul (evalB_lit hdB) eq₁ih (by omega)) (hrx.trans hbB)
  have erh : er.evalB B σ = some (pack D r) :=
    eval_seed hseed erxh (eval_rem eih D hDB) hrx hri hseedB
  have ervh := eval_fst erh D_pos hDB hr.2
  have erih := eval_snd erh D_pos hDB hr.2
  have eoutih := eval_add epih (eval_mul (evalB_lit hDB) erih (by omega)) (houti.trans hdB)
  have eoutvh := eval_add ervh (eval_mul (evalB_lit hbB) eq₁vh (by omega)) (houtv.trans hbaseB)
  have eout := eval_add eoutih (eval_mul (evalB_lit hdB) eoutvh (by omega)) (by omega)
  have heq : matchingNeighbor (k+1) j = (p.2+D*r.2)+d*(r.1+b*q₁.1) := by
    rfl
  simpa only [heq, nextRow, ev, ei, ep, eq₀, eq₁, er] using eout

end Lax920634Proofs.RamExpressions
