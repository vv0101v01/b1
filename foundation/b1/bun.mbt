///|
/// bun.mbt — 主叢模疊 Bun_G（此處 G = GL_2 在 P^1 上）：
///   Birkhoff–Grothendieck 分解、Harder–Narasimhan 分層、自同構群、質量公式
///
/// Theorem engine:
///   T14 (Birkhoff–Grothendieck): P^1 上每個向量叢 = ⊕ O(a_i)
///   T15 (HN 分層唯一性): 每個叢恰有一個 HN 型；半穩定 ⇔ a = b
///   T16 (自同構計數): E = O(a)⊕O(b), a > b ⇒ |Aut(E)| = (q-1)²·q^{a-b+1}
///   T17 (質量公式/幾何級數): Σ_{HN 型} 1/|Aut| 的截斷和收斂於封閉形式

///|
/// Split bundle on P^1: E = O(a) ⊕ O(b) with a ≥ b (Birkhoff–Grothendieck).
pub(all) struct SplitBundle(Int32, Int32)

///|
/// Slope of E: deg/rank = (a+b)/2 as a double.
pub fn SplitBundle::slope(self : SplitBundle) -> Double {
  (self.0 + self.1).to_double() / 2.0
}

///|
/// Whether E is semistable: min slope of subbundles ≤ slope(E).
/// Sub line bundles: O(a), O(b), O(c) for c between; slope of O(a) is a.
pub fn SplitBundle::is_semistable(self : SplitBundle) -> Bool {
  // stable sub = O(max summand); semistable iff a = b
  self.0 == self.1
}

///|
/// HN type: (a, b) with a > b strictly, or (m, m) semistable.
pub fn SplitBundle::hn_type(self : SplitBundle) -> (Int32, Int32) {
  (self.0, self.1)
}

///|
/// Instability measure: a - b ≥ 0.
pub fn SplitBundle::instability(self : SplitBundle) -> Int32 {
  self.0 - self.1
}

///|
/// Dimension of H^0(P^1, O(n)) = n + 1 for n ≥ 0, 0 for n < 0.
pub fn h0_o(n : Int32) -> Int32 {
  if n < 0 {
    0
  } else {
    n + 1
  }
}

///|
/// Dimension of H^1(P^1, O(n)) = -n - 1 for n ≤ -2, 0 for n ≥ -1.
/// (Riemann–Roch: χ = n + 1 = h⁰ - h¹.)
pub fn h1_o(n : Int32) -> Int32 {
  if n <= -2 {
    -n - 1
  } else {
    0
  }
}

///|
/// Euler characteristic χ(O(n)) = n + 1 (Riemann–Roch on P^1).
pub fn chi_o(n : Int32) -> Int32 {
  n + 1
}

///|
/// |Aut(E)| over F_q for E = O(a) ⊕ O(b):
///   a = b: GL_2(q);
///   a > b: lower-triangular invertibles = (q-1)²·q^{h⁰(O(a-b))} = (q-1)²·q^{a-b+1}.
pub fn aut_order(e : SplitBundle, q : Int32) -> Int64 {
  if e.0 == e.1 {
    return gl_order(2, q)
  }
  let d = e.0 - e.1
  q_pow(q - 1, 2) * q_pow(q, d + 1)
}

///|
/// Direct verification of |Aut(E)| by enumerating endomorphism shapes for
/// small q: End(E) = [[H⁰(O), H⁰(O(b-a))], [H⁰(O(a-b)), H⁰(O)]].
pub fn aut_order_bruteforce(e : SplitBundle, q : Int32) -> Int64 {
  let a = e.0
  let b = e.1
  if a == b {
    return count_gl_bruteforce(2, q)
  }
  // endomorphism = (α ∈ F_q, δ ∈ F_q, γ ∈ F_q^{a-b+1})
  // invertible iff αδ ≠ 0: (q-1)² · q^{a-b+1} choices
  let h10 = h0_o(a - b) // Hom(O(b), O(a)) = H⁰(O(a-b)) = a-b+1
  let mut count = 0L
  let total = q_pow(q, 2).to_int()
  let mut idx = 0
  while idx < total {
    let alpha = idx % q
    let delta = idx / q
    if alpha != 0 && delta != 0 {
      count = count + 1L
    }
    idx = idx + 1
  }
  count * q_pow(q, h10)
}

///|
/// Enumerate all rank-2 bundles on P^1 with det O(d) and instability ≤ bound.
pub fn enumerate_bundles(det_deg : Int32, bound : Int32) -> Array[SplitBundle] {
  let res : Array[SplitBundle] = []
  // a + b = det_deg, a ≥ b, a - b ≤ bound and a - b ≡ det_deg (mod 2)
  let mut diff = det_deg % 2
  if diff < 0 {
    diff = diff + 2
  }
  while diff <= bound {
    let a = (det_deg + diff) / 2
    let b = det_deg - a
    res.push(SplitBundle(a, b))
    diff = diff + 2
  }
  res
}

///|
/// HN stratification: assign each bundle its HN type; verify uniqueness
/// (each bundle appears in exactly one stratum) and compute stratum sizes.
pub fn hn_strata(
  det_deg : Int32,
  bound : Int32,
) -> Array[((Int32, Int32), Int32)] {
  let res : Array[((Int32, Int32), Int32)] = []
  let bs = enumerate_bundles(det_deg, bound)
  for e in bs {
    let tp = e.hn_type()
    let mut found = false
    let mut i = 0
    while i < res.length() {
      if res[i].0.0 == tp.0 && res[i].0.1 == tp.1 {
        res[i] = (tp, res[i].1 + 1)
        found = true
      }
      i = i + 1
    }
    if !found {
      res.push((tp, 1))
    }
  }
  res
}

///|
/// Truncated mass of Bun_2^{det O(d)}(P^1): Σ_{instability ≤ bound} 1/|Aut(E)|.
pub fn bun_mass_truncated(det_deg : Int32, bound : Int32, q : Int32) -> Double {
  let mut acc = 0.0
  for e in enumerate_bundles(det_deg, bound) {
    acc = acc + 1.0 / aut_order(e, q).to_double()
  }
  acc
}

///|
/// Closed form of the truncated mass: 1/|GL_2(q)| (semistable, diff = 0) plus
/// Σ_{i=1..bound, i ≡ d mod 2} 1/((q-1)² q^{i+1}).
pub fn bun_mass_closed(det_deg : Int32, bound : Int32, q : Int32) -> Double {
  let mut acc = 1.0 / gl_order(2, q).to_double()
  let mut i = det_deg % 2
  if i < 0 {
    i = i + 2
  }
  if i == 0 {
    i = 2 // skip semistable diff = 0
  }
  while i <= bound {
    acc = acc +
      1.0 /
      ((q - 1).to_double() * (q - 1).to_double() * q_pow(q, i + 1).to_double())
    i = i + 2
  }
  acc
}
