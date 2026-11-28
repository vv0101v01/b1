///|
/// hodgetate.mbt — 104. 霍奇-泰特分解 (Hodge–Tate decomposition)
///
/// A p-adic representation V is Hodge–Tate iff
///   V ⊗ C_p ≅ ⊕_i C_p(i)^{h_i}
/// with Hodge numbers h_i (HT weights). For E/Q_p: HT weights of E[p^∞] are
/// {0, 1} with h = (1, 1). Mazur weak admissibility: for the filtered
/// φ-module D of V: t_H(D) = t_N(D) and t_N(S) ≤ t_H(S) for subobjects —
/// graphically: the Newton polygon lies ON OR ABOVE the Hodge polygon.
///
/// Theorem engine:
///   T104a (HT 維數): Σ h_i = dim V（E: (1,1) → 2 ✓）
///   T104b (Newton 多邊形 ≥ Hodge 多邊形): 普通曲線 (0,1)=(0,1) 相等；
///       超奇異 (1/2,1/2) vs (0,1)：部分和 1/2 ≥ 0、總和相等
///   T104c (Newton 多邊形演算法): 由 φ 的特徵多項式係數 p-adic 賦值
///       計算特徵值賦值（下凸包）

///|
/// p-adic valuation of a nonzero integer.
pub fn vp(n : Int64, p : Int32) -> Int32 {
  if n == 0L {
    return 1000000
  }
  let mut v = 0
  let mut m = if n < 0L { -n } else { n }
  let p64 = p.to_int64()
  while m % p64 == 0L {
    m = m / p64
    v = v + 1
  }
  v
}

///|
/// Root valuations of x² + b x + c over Q_p via the Newton polygon:
/// points (0, v(c)), (1, v(b)), (2, 0); lower convex hull; slopes negated.
/// Returns the two valuations sorted ascending (as halves: return Doubles).
pub fn newton_slopes_quadratic(
  b : Int64,
  c : Int64,
  p : Int32,
) -> (Double, Double) {
  let v0 = vp(c, p).to_double()
  let v1 = if b == 0L { 1000000.0 } else { vp(b, p).to_double() }
  let v2 = 0.0
  // lower convex hull of (0,v0),(1,v1),(2,v2): two segments or one
  // slope of chord (0,v0)-(2,v2) = (v2-v0)/2
  let chord = (v2 - v0) / 2.0
  // if v1 <= v0 + chord... hull includes (1,v1) iff v1 < v0 + chord... 
  // lower hull: middle point is ON or ABOVE the chord means it's not a vertex:
  if v1 >= v0 + chord - 0.000000001 {
    // one segment: two equal valuations = -chord
    let s = -chord
    (s, s)
  } else {
    // two segments: slopes (v1-v0), (v2-v1); valuations = negated
    (-(v1 - v0), -(v2 - v1))
  }
}

///|
/// Hodge numbers of a filtered module: gr dims of the filtration.
pub(all) struct HodgeData {
  weights : Array[Int32] // list of HT weights with multiplicity
}

///|
pub fn HodgeData::total_dim(self : HodgeData) -> Int32 {
  self.weights.length()
}

///|
/// Hodge polygon partial sums: sorted ascending weights, cumulative.
pub fn hodge_partial_sums(h : HodgeData) -> Array[Double] {
  // sort weights ascending (small arrays: insertion sort copy)
  let w : Array[Int32] = []
  for x in h.weights {
    w.push(x)
  }
  let mut i = 1
  while i < w.length() {
    let key = w[i]
    let mut j = i
    while j > 0 && w[j - 1] > key {
      w[j] = w[j - 1]
      j = j - 1
    }
    w[j] = key
    i = i + 1
  }
  let res : Array[Double] = []
  let mut acc = 0.0
  let mut k = 0
  while k < w.length() {
    acc = acc + w[k].to_double()
    res.push(acc)
    k = k + 1
  }
  res
}

///|
/// Newton partial sums from slope pair (ascending).
pub fn newton_partial_sums(s1 : Double, s2 : Double) -> Array[Double] {
  let a = if s1 <= s2 { s1 } else { s2 }
  let b = if s1 <= s2 { s2 } else { s1 }
  [a, a + b]
}

///|
/// Weak admissibility check (rank 2): total equality |t_H − t_N| < tol and
/// partial: newton[0] ≥ hodge[0] (Newton above Hodge on the first step).
pub fn weak_admissible_2d(h : HodgeData, s1 : Double, s2 : Double) -> Bool {
  let hp = hodge_partial_sums(h)
  let np = newton_partial_sums(s1, s2)
  if hp.length() != 2 {
    return false
  }
  let total_diff = hp[1] - np[1]
  let td = if total_diff < 0.0 { -total_diff } else { total_diff }
  if td > 0.000001 {
    return false
  }
  np[0] >= hp[0] - 0.000001
}
