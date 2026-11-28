///|
/// motivic.mbt — 103. 動機伽羅瓦群 (motivic Galois group)
///
/// For an Artin motive M_K (K/Q finite), G_mot(M) = Gal(K/Q) — computed here
/// from Frobenius cycle types of factorization patterns mod p (Dedekind).
/// The Tannakian character of the permutation motive decomposes into
/// irreducibles, matching the factorization ζ_K = Π L(ρ, s)^{d_ρ}.
///
/// Theorem engine:
///   T103a (Artin 動機 = 伽羅瓦群): G_mot(x³−2) = S₃（模 p 分解型態集合
///       = {1³, 1·2, 3} 觀測到全部三種；1·2 的出現排除 A₃）
///   T103b (二次動機): G_mot(x²−5) = Z/2（型態 {1², 2}）
///   T103c (Dedekind zeta 分解): Q(ζ₇) 係數 a_p = #{f=1 素理想} = Σ_χ χ(p)
///       （六個 Dirichlet 特徵 mod 7 的 L 之積 = ζ_K，逐素數驗證）

///|
/// Factor x^deg + ... (monic integer coeffs) mod p into irreducible-degree
/// pattern via brute-force: find the degrees of the irreducible factors of
/// the polynomial over F_p (gcd(x^{p^d} − x) method on the polynomial ring).
/// Simplified: compute factorization pattern by tracking orbit degrees of the
/// action of Frobenius on roots in GF(p, k) for k ≤ deg·(small): instead we
/// use the classical gcd method on F_p[x]:
///   for each root-locating step: find smallest d with gcd(f, x^{p^d} − x) > 1.
/// Concrete small implementation: split f into linear factors by scanning
/// roots in F_p, then recursively split residual via GF(p, 2) roots etc.
/// For deg ≤ 3 with pattern output we only need degrees: implement by
/// computing the number of roots in F_p, F_{p²}, F_{p³} of f.
/// Returns sorted factor degrees (e.g. [1,1,1], [1,2], [3]).

///|
/// Number of roots of monic integer poly in GF(p, k) (k ≤ 3 in practice).
fn roots_in_gfpk(coeffs : Array[Int64], p : Int32, k : Int32) -> Int32 {
  let fld = GF::make(p, k)
  let q = fld.q()
  let mut count = 0
  let mut x = 0
  while x < q {
    // evaluate poly at x
    let mut acc = 0
    let mut i = coeffs.length() - 1
    while i >= 0 {
      let c = ((coeffs[i] % p.to_int64() + p.to_int64()) % p.to_int64()).to_int()
      acc = fld.add(fld.mul(acc, x), c)
      i = i - 1
    }
    if acc == 0 {
      count = count + 1
    }
    x = x + 1
  }
  count
}

///|
/// Factorization pattern of f mod p: factor degrees as sorted array.
/// Uses root counts in F_p^j for j = 1..deg (determines pattern for deg ≤ 4).
pub fn factor_pattern_modp(coeffs : Array[Int64], p : Int32) -> Array[Int32] {
  let deg = coeffs.length() - 1
  // skip bad primes: repeated factors ⇔ gcd(f, f') nontrivial — approximate
  // by requiring total root count consistency; caller avoids bad primes.
  let r1 = roots_in_gfpk(coeffs, p, 1)
  if r1 == deg {
    let pat : Array[Int32] = []
    let mut i = 0
    while i < deg {
      pat.push(1)
      i = i + 1
    }
    return pat
  }
  if deg == 2 {
    return [2]
  }
  if deg == 3 {
    // either [1, 2] (one root in F_p) or [3]
    if r1 == 1 {
      return [1, 2]
    }
    return [3]
  }
  // deg 4 fallback: [1,3] vs [2,2] vs [1,1,2]
  let r2 = roots_in_gfpk(coeffs, p, 2)
  if r1 == 2 {
    return [1, 1, 2]
  }
  if r2 == 4 {
    return [2, 2]
  }
  [1, 3]
}

///|
/// Distinct factorization patterns of f mod p for primes p ≤ p_max not in
/// bad_primes (the bad primes divide disc(f)).
pub fn observed_patterns(
  coeffs : Array[Int64],
  p_max : Int32,
  bad_primes : Array[Int32],
) -> Array[Array[Int32]] {
  let res : Array[Array[Int32]] = []
  for p in primes_upto(p_max) {
    let mut bad = false
    for q in bad_primes {
      if p == q {
        bad = true
      }
    }
    if !bad {
      let pat = factor_pattern_modp(coeffs, p)
      let mut seen = false
      for q in res {
        if pattern_eq(q, pat) {
          seen = true
        }
      }
      if !seen {
        res.push(pat)
      }
    }
  }
  res
}

///|
pub fn pattern_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let mut i = 0
  while i < a.length() {
    if a[i] != b[i] {
      return false
    }
    i = i + 1
  }
  true
}

///|
/// Pattern of the identity element: all ones.
pub fn pattern_identity(deg : Int32) -> Array[Int32] {
  let res : Array[Int32] = []
  let mut i = 0
  while i < deg {
    res.push(1)
    i = i + 1
  }
  res
}

///|
/// Pattern of a transposition on deg letters (1...1 2).
pub fn pattern_transposition(deg : Int32) -> Array[Int32] {
  let res : Array[Int32] = []
  let mut i = 0
  while i < deg - 2 {
    res.push(1)
    i = i + 1
  }
  res.push(2)
  res
}

///|
/// Pattern of a deg-cycle.
pub fn pattern_cycle(deg : Int32) -> Array[Int32] {
  [deg]
}

///|
/// All Dirichlet characters mod 7 (primitive root 3): values as Cx arrays
/// indexed by a ∈ 0..6. Returns array of 6 characters.
pub fn dir_chars_mod7() -> Array[Array[Cx]] {
  // ind: 3^ind ≡ a mod 7; chars ω^ind with ω = e^{2πi/6}
  let res : Array[Array[Cx]] = []
  let mut m = 0
  while m < 6 {
    let vals : Array[Cx] = []
    let mut a = 0
    while a < 7 {
      if a == 0 {
        vals.push(Cx(0.0, 0.0))
      } else {
        let mut ind = 0
        let mut cur = 1
        while cur != a {
          cur = cur * 3 % 7
          ind = ind + 1
        }
        // ω = e^{2πi/6} = 1/2 + i·√3/2; ω^{m·ind} by complex powers
        let omega = Cx(0.5, 0.8660254037844386)
        let mut z = Cx(1.0, 0.0)
        let mut e = 0
        let expo = m * ind % 6
        while e < expo {
          z = z.mul(omega)
          e = e + 1
        }
        vals.push(z)
      }
      a = a + 1
    }
    res.push(vals)
    m = m + 1
  }
  res
}

///|
/// Coefficient a_p of ζ_{Q(ζ₇)} at prime p = #{degree-1 primes above p}
/// = 6/ord_7(p) if ord_7(p) = 1 else 0... generally: number of primes with
/// residue degree 1 = 6 if p ≡ 1 mod 7 else 0.
pub fn zeta_cyclo_coeff_prime(p : Int32) -> Int32 {
  if p == 7 {
    return -1 // ramified
  }
  if p % 7 == 1 {
    6
  } else {
    0
  }
}

///|
/// Σ_χ χ(p) over all chars mod 7 (should equal zeta_cyclo_coeff_prime).
pub fn sum_chars_at(chars : Array[Array[Cx]], a : Int32) -> Cx {
  let mut acc = Cx(0.0, 0.0)
  for v in chars {
    let mut m = a % 7
    if m < 0 {
      m = m + 7
    }
    acc = acc.add(v[m])
  }
  acc
}
