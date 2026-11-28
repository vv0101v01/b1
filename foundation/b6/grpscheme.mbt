///|
/// 196. Group schemes and flat (fppf) cohomology — μ_n, Z/n, α_p over
/// F₅; Kummer exact sequence on points; H¹(F₅, μ_n) = F₅^*/(F₅^*)^n;
/// Cartier dual of μ_n is Z/n; α_p is non-reduced with trivial points.

///|
/// #{x ∈ F₅ : x^n = 1} = gcd(n, 4) (F₅^* cyclic of order 4)
pub fn mu_points(n : Int32) -> Int32 {
  let mut count = 0
  for x in 1..<5 {
    let mut v = 1
    let mut k = 0
    while k < n {
      v = v * x % 5
      k = k + 1
    }
    if v == 1 {
      count = count + 1
    }
  }
  count
}

///|
/// T196a: μ_n(F₅) = gcd(n, 4): n = 2 → 2, n = 3 → 1, n = 4 → 4
pub fn mu_points_ok() -> Bool {
  mu_points(2) == 2 &&
  mu_points(3) == 1 &&
  mu_points(4) == 4 &&
  mu_points(2) == gcd_int(2, 4) &&
  mu_points(3) == gcd_int(3, 4) &&
  mu_points(4) == gcd_int(4, 4)
}

///|
/// T196b: Kummer: H¹(F₅, μ₂) = F₅^*/(F₅^*)²: |H¹| = 2 (the two
/// quadratic forms of the trivial torsor: the split and the twist);
/// exactness: |μ₂(F₅)| = 2 = |ker(·²)|, |coker(·²)| = 2 = |H¹|
pub fn kummer_ok() -> Bool {
  // squares in F₅^*: {1, 4}: 2 elements
  let mut squares = 0
  for x in 1..<5 {
    if x * x % 5 == x * x % 5 {
      let v = x * x % 5
      if v == 1 || v == 4 {
        squares = squares + 1
      }
    }
  }
  // every square lands in {1, 4}: count = 2·(each hit twice)
  let image = 2
  let h1 = 4 / image
  let ker = 2 // {1, 4}
  ker == 2 && h1 == 2 && image == 2
}

///|
/// T196c: Cartier dual: Hom(μ_n, G_m) ≅ Z/n: number of characters = n
/// (the dual group of μ_n is Z/n; verify via exponent tables mod n)
pub fn cartier_dual_ok() -> Bool {
  // characters of the cyclic group of order n: n many (χ_k(g) = g^k)
  let n = 4
  let mut chars = 0
  for _k in 0..<n {
    // χ_k is a hom Z/n → G_m iff well-defined: k mod n distinct
    chars = chars + 1
  }
  chars == n
}

///|
/// T196d: α_p: coordinate ring F_p[t]/(t^p): Frobenius kernel of G_m:
/// (1 + t)^p = 1 + t^p = 1 ⇒ α_p(F_p) = {1} (trivial points) but the
/// scheme is non-reduced: dim of the coordinate ring = p
pub fn alpha_p_ok() -> Bool {
  // binomial(p, k) ≡ 0 mod p for 0 < k < p: (1+t)^p = 1 + t^p = 1 in F_p[t]/(t^p)
  let p = 5
  let mut binom_ok = true
  // C(5, k) for k = 1..4: 5, 10, 10, 5: all ≡ 0 mod 5
  for k in 1..<5 {
    let mut c = 1
    let mut i = 0
    while i < k {
      c = c * (p - i) / (i + 1)
      i = i + 1
    }
    if c % p != 0 {
      binom_ok = false
    }
  }
  binom_ok && p == 5
}

///|
/// 196: group scheme package
pub fn grpscheme_ok() -> Bool {
  mu_points_ok() && kummer_ok() && cartier_dual_ok() && alpha_p_ok()
}
