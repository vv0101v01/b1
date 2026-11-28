///|
/// evolve.mbt — 衍生演生法 (derived evolutionary / generative algorithms)
/// 由上述數學結構「演化」而出的三個演算法：
///   A1 Hecke 特徵形式演化（冪法）：隨機權 24 形式 → 演化為 Hecke 特徵形式
///      = 自守表示的生成元（計算機版「找到一個自守表示」）
///   A2 Hitchin 譜曲線演化（基因演算法）：在 Hitchin 基底上搜尋高點數譜曲線
///      （橢圓曲線密碼學的點數問題 = 希欽纖維的點計數）
///   A3 二次型約化演化：隨機正定型 → 鄰居步 + 約化步 → 類群約化代表元

///|
/// Weight-24 Hecke operator T_2 on a coefficient vector (a_1..a_N) as Double:
/// (T_2 v)_n = v_{2n} + 2^{23}·v_{n/2}.
fn t2_weight24(v : Array[Double]) -> Array[Double] {
  let m = v.length()
  let res : Array[Double] = []
  let mut n = 1
  while n <= m {
    let mut acc = 0.0
    if 2 * n <= m {
      acc = acc + v[2 * n - 1]
    }
    if n % 2 == 0 {
      acc = acc + 8388608.0 * v[n / 2 - 1]
    }
    res.push(acc)
    n = n + 1
  }
  res
}

///|
/// Solve the 2×2 linear system [[a11,a12],[a21,a22]]·[x,y] = [b1,b2].
fn solve2(
  a11 : Double,
  a12 : Double,
  a21 : Double,
  a22 : Double,
  b1 : Double,
  b2 : Double,
) -> (Double, Double) {
  let det = a11 * a22 - a12 * a21
  ((b1 * a22 - a12 * b2) / det, (a11 * b2 - b1 * a21) / det)
}

///|
/// Basis of S_24 = Δ · M_12 = span{Δ², Δ·E12} as coefficient vectors
/// (index n−1 ↔ coefficient of q^n, n = 1..30), in Double precision.
/// Both basis elements are genuine weight-24 cusp forms; T_2 (weight-24
/// normalization) preserves their span.
pub fn s24_basis() -> (Array[Double], Array[Double]) {
  let d = delta_series(31)
  let v1 : Array[Double] = []
  let v2 : Array[Double] = []
  let mut n = 1
  while n <= 30 {
    // v1 = Δ² : convolution of τ with τ
    let mut acc1 = 0.0
    let mut i1 = 1
    while i1 < n {
      acc1 = acc1 + d.coeff(i1).to_double() * d.coeff(n - i1).to_double()
      i1 = i1 + 1
    }
    v1.push(acc1)
    // v2 = Δ·E12
    let mut acc = 0.0
    let mut i = 1
    while i <= n {
      let e12 = if n - i == 0 {
        1.0
      } else {
        65520.0 / 691.0 * sigma(n - i, 11).to_double()
      }
      acc = acc + d.coeff(i).to_double() * e12
      i = i + 1
    }
    v2.push(acc)
    n = n + 1
  }
  (v1, v2)
}

///|
/// A1: power-method evolution toward a Hecke eigenform of S_24.
/// The Hecke operator T_2 acts on the 2-dimensional space S_24 = span{Δ², Δ·E12};
/// its restriction is a 2×2 matrix M (computed exactly from coefficient data).
/// A random element of S_24 evolves under normalized iteration c ← Mc/‖Mc‖
/// and converges to a dominant eigenvector — a Hecke eigenform, i.e. a
/// generator of an automorphic representation.
/// Returns (eigenvalue, final residual ‖Mc − λc‖, iterations).
pub fn hecke_eigenform_evolution(
  seed : Int64,
  steps : Int32,
) -> (Double, Double, Int32) {
  let rng = LCG::make(seed)
  let (v1, v2) = s24_basis()
  let w1 = t2_weight24(v1)
  let w2 = t2_weight24(v2)
  // columns of M: express T_2(v_j) = M1j·v1 + M2j·v2 using coefficients at
  // n = 1, 2 (exact data, no truncation)
  let (m11, m21) = solve2(v1[0], v2[0], v1[1], v2[1], w1[0], w1[1])
  let (m12, m22) = solve2(v1[0], v2[0], v1[1], v2[1], w2[0], w2[1])
  // power iteration on M
  let mut c1 = (rng.next(1000L) - 500L).to_double()
  let mut c2 = (rng.next(1000L) - 500L).to_double()
  let nn0 = @math.pow(c1 * c1 + c2 * c2, 0.5)
  c1 = c1 / nn0
  c2 = c2 / nn0
  let mut lam = 0.0
  let mut iter = 0
  while iter < steps {
    let n1 = m11 * c1 + m12 * c2
    let n2 = m21 * c1 + m22 * c2
    lam = c1 * n1 + c2 * n2
    let nn = @math.pow(n1 * n1 + n2 * n2, 0.5)
    c1 = n1 / nn
    c2 = n2 / nn
    iter = iter + 1
  }
  // residual ||M c − λ c||
  let r1 = m11 * c1 + m12 * c2 - lam * c1
  let r2 = m21 * c1 + m22 * c2 - lam * c2
  (lam, @math.pow(r1 * r1 + r2 * r2, 0.5), iter)
}

///|
/// A2: evolutionary search on the Hitchin base of GL_2 (logarithmic model):
/// individuals are coefficient vectors of spectral curves y² = f(x) over F_q
/// (deg 5, genus 2); fitness = #C(F_q) (maximizing).
/// Returns the best fitness per generation.
pub fn hitchin_spectral_curve_ga(
  p : Int32,
  population : Int32,
  generations : Int32,
  seed : Int64,
) -> Array[Int32] {
  let rng = LCG::make(seed)
  // population: arrays of 6 coefficients mod p (deg ≤ 5)
  let pop : Array[Array[Int32]] = []
  let mut i = 0
  while i < population {
    let ind : Array[Int32] = []
    let mut j = 0
    while j < 6 {
      ind.push(rng.next(p.to_int64()).to_int())
      j = j + 1
    }
    pop.push(ind)
    i = i + 1
  }
  let best_per_gen : Array[Int32] = []
  let mut g = 0
  while g < generations {
    // fitness: point count (needs odd degree & square-free; add penalty)
    let fits : Array[Int32] = []
    let mut idx = 0
    while idx < pop.length() {
      let ind = pop[idx]
      // ensure deg 5 odd: leading coeff nonzero
      let ind2 : Array[Int32] = []
      let mut j = 0
      while j < 6 {
        ind2.push(ind[j])
        j = j + 1
      }
      if ind2[5] == 0 {
        ind2[5] = 1
      }
      // square-free check: gcd(f, f') = 1 (small field)
      let curve = HypCurve(ind2)
      let sf = hyp_squarefree(ind2, p)
      if sf {
        fits.push(curve.point_count(p, 1))
      } else {
        fits.push(-100)
      }
      idx = idx + 1
    }
    // best
    let mut best = fits[0]
    let mut bi = 0
    let mut t = 0
    while t < fits.length() {
      if fits[t] > best {
        best = fits[t]
        bi = t
      }
      t = t + 1
    }
    best_per_gen.push(best)
    // next generation: elitism + crossover + mutation
    let next : Array[Array[Int32]] = []
    // keep best individual unchanged
    let elite : Array[Int32] = []
    let mut j2 = 0
    while j2 < 6 {
      elite.push(pop[bi][j2])
      j2 = j2 + 1
    }
    next.push(elite)
    while next.length() < population {
      // pick two parents biased toward fitness (tournament of 2)
      let a1 = rng.next(population.to_int64()).to_int()
      let a2 = rng.next(population.to_int64()).to_int()
      let pa = if fits[a1] >= fits[a2] { a1 } else { a2 }
      let b1 = rng.next(population.to_int64()).to_int()
      let b2 = rng.next(population.to_int64()).to_int()
      let pb = if fits[b1] >= fits[b2] { b1 } else { b2 }
      // uniform crossover
      let child : Array[Int32] = []
      let mut j3 = 0
      while j3 < 6 {
        if rng.next(2L).to_int() == 0 {
          child.push(pop[pa][j3])
        } else {
          child.push(pop[pb][j3])
        }
        j3 = j3 + 1
      }
      // mutation
      let mut jm = 0
      while jm < 6 {
        if rng.next(4L).to_int() == 0 {
          child[jm] = rng.next(p.to_int64()).to_int()
        }
        jm = jm + 1
      }
      next.push(child)
    }
    // replace pop in place
    let mut r = 0
    while r < population {
      let mut j4 = 0
      while j4 < 6 {
        pop[r][j4] = next[r][j4]
        j4 = j4 + 1
      }
      r = r + 1
    }
    g = g + 1
  }
  best_per_gen
}

///|
/// Square-free check for f over F_p: gcd(f, f') = 1, computed by evaluating
/// the resultant-free criterion: f has no repeated root iff for all x,
/// f(x) = 0 ⇒ f'(x) ≠ 0 (small fields: brute force).
pub fn hyp_squarefree(coeffs : Array[Int32], p : Int32) -> Bool {
  let fld = GF::make(p, 1)
  let curve = HypCurve(coeffs)
  // derivative coefficients
  let deriv : Array[Int32] = []
  deriv.push(0)
  let mut i = 1
  while i < coeffs.length() {
    deriv.push(coeffs[i] * i % p)
    i = i + 1
  }
  let dcurve = HypCurve(deriv)
  let mut x = 0
  while x < p {
    if curve.eval(x, fld) == 0 && dcurve.eval(x, fld) == 0 {
      return false
    }
    x = x + 1
  }
  true
}

///|
/// A3: evolution of binary quadratic forms toward reduced representatives.
/// Gauss reduction steps (all in SL_2(Z), disc preserved):
///   S: (a,b,c) → (c,−b,a) when c < a;
///   T^k: (a,b,c) → (a, b+2ak, ak²+bk+c) with k = −round(b/2a) minimizing |b|;
///   edge tie: τ: (a,b,c) → (a, b+2a, a+b+c) when |b| = a but b < 0.
/// Fitness a + c decreases along the evolution; returns (steps, final a+c).
pub fn form_reduction_evolution(
  a0 : Int32,
  b0 : Int32,
  c0 : Int32,
  max_steps : Int32,
) -> (Int32, Int32) {
  let mut a = a0
  let mut b = b0
  let mut c = c0
  let mut steps = 0
  let mut done = false
  while steps < max_steps && !done {
    let f = QForm(a, b, c)
    if f.is_reduced() {
      done = true
    } else if c < a {
      // S move
      let na = c
      let nb = -b
      let nc = a
      a = na
      b = nb
      c = nc
    } else {
      let ab = if b < 0 { -b } else { b }
      if ab > a {
        // T^k: choose k = -round(b / 2a) — use truncation toward zero of b/2a
        let k = -(b / (2 * a))
        let nb = b + 2 * k * a
        let nc = a * k * k + b * k + c
        b = nb
        c = nc
      } else {
        // |b| = a with b < 0 (tie case): τ
        let nb = b + 2 * a
        let nc = a + b + c
        b = nb
        c = nc
      }
    }
    steps = steps + 1
  }
  (steps, a + c)
}
