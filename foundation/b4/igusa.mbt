///|
/// igusa.mbt — 57. 伊古薩模空間與伊古薩疊 (Igusa moduli spaces & stacks)
///
/// Igusa's classical picture: the j-line A₁ = A¹ is the coarse moduli of
/// elliptic curves; the STACK structure records automorphisms:
///   |Aut| = 2 (generic j), 4 (j = 1728), 6 (j = 0).
/// Weierstrass models (A, B) with j = 1728·4A³/(4A³+27B²) are acted on by
/// u-scaling (A, B) ↦ (u⁴A, u⁶B); orbits = geometric classes; stabilizers =
/// automorphism groups. The Igusa/Newton stratification of the mod-p fiber:
/// ordinary (a_p ≢ 0) vs supersingular (a_p ≡ 0) — with the classical count
/// of supersingular j-invariants over F_p-bar:
///   #SS = ⌊p/12⌋ + ε,  ε = 0, 1, 1, 2 for p ≡ 1, 5, 7, 11 (mod 12),
/// all lying in F_{p²} (Deuring) — verified by enumeration over F_{p²}.
///
/// Theorem engine:
///   T57a (j 分類): 給定 j₀ ∉ {0, 1728}：{(A,B) : j = j₀} = 2 個 u-軌道
///       （兩條 F_p-扭），軌道長各 (p−1)/2
///   T57b (疊結構): 穩定子 |Aut| = 2, 4, 6（generic/1728/0，p ≡ 1 mod 4/3）
///   T57c (Igusa 分層): #SS(j ∈ F_{p²}) = ⌊p/12⌋ + ε_p（p = 5, 7, 11, 13）
///   T57d (Deuring): SS j-不變量全落於 F_{p²}：枚舉 F_{p²} 與公式吻合

///|
/// j-invariant of y² = x³ + A x + B over F_p: 1728·4A³/(4A³+27B²).
pub fn j_invariant(a : Int64, b : Int64, p : Int32) -> Int32 {
  let pm = p.to_int64()
  let a3 = (a % pm + pm) % pm
  let b2 = (b % pm + pm) % pm
  let num = 4L * a3 * a3 * a3 % pm
  let den = (4L * a3 * a3 * a3 + 27L * b2 * b2) % pm
  if den == 0L {
    return -1 // infinity (disc = 0)
  }
  let inv = mod_inverse(den, pm)
  (1728L * num % pm * inv % pm).to_int()
}

///|
/// Inverse: explicit model with j-invariant exactly j₀ (for j₀ ≢ 1728):
/// A = −3j/(j−1728), B = −2j/(j−1728) over F_p. For j₀ = 1728: (A,B) = (−1, 0).
pub fn model_from_j(j0 : Int32, p : Int32) -> (Int64, Int64) {
  let pm = p.to_int64()
  let j = (j0.to_int64() % pm + pm) % pm
  let j1728 = (1728L % pm + pm) % pm
  if j == j1728 {
    return (-1L, 0L)
  }
  if j == 0L {
    return (0L, 1L) // y² = x³ + 1 has j = 0
  }
  let den = ((j - j1728) % pm + pm) % pm
  let inv = mod_inverse(den, pm)
  let a = ((pm - 3L) * j % pm * inv % pm + pm) % pm
  let b = ((pm - 2L) * j % pm * inv % pm + pm) % pm
  (a, b)
}

///|
/// Count (A, B) ∈ F_p² with j(A,B) = j₀ (and disc ≠ 0).
pub fn fiber_count(j0 : Int32, p : Int32) -> Int32 {
  let mut count = 0
  let mut a = 0
  while a < p {
    let mut b = 0
    while b < p {
      if j_invariant(a.to_int64(), b.to_int64(), p) == j0 {
        count = count + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  count
}

///|
/// Stabilizer size of (A, B) under u-scaling: #{u ∈ F_p^× : u⁴A = A, u⁶B = B}.
pub fn stabilizer_size(a : Int64, b : Int64, p : Int32) -> Int32 {
  let pm = p.to_int64()
  let mut count = 0
  let mut u = 1
  while u < p {
    let uu = u.to_int64()
    let u4 = uu * uu * uu * uu % pm
    let u6 = u4 * uu * uu % pm
    let a0 = (a % pm + pm) % pm
    let b0 = (b % pm + pm) % pm
    if u4 * a0 % pm == a0 && u6 * b0 % pm == b0 {
      count = count + 1
    }
    u = u + 1
  }
  count
}

///|
/// T57a: generic j₀: fiber = 2 twists × (p−1)/2 orbit points = p−1 pairs.
pub fn fiber_generic_check(p : Int32, j0 : Int32) -> Bool {
  let fc = fiber_count(j0, p)
  let stab = stabilizer_size(model_from_j(j0, p).0, model_from_j(j0, p).1, p)
  // orbit of one model = (p−1)/stab; two F_p-twists for generic j:
  fc == 2 * (p - 1) / stab
}

///|
/// T57b: stabilizer sizes at the three special loci.
pub fn stack_structure_check(p : Int32) -> Bool {
  // generic j: stab = #{u : u⁴ = 1 ∧ u⁶ = 1} = #{±1} = 2
  let (ga, gb) = model_from_j(1, p) // j = 1 generic-ish (p > 13)
  let gen_ok = stabilizer_size(ga, gb, p) == 2
  // j = 1728 model (−1, 0): stab = #{u : u⁴ = 1} = gcd(4, p−1)
  let s1728 = stabilizer_size(-1L, 0L, p)
  let e1728 = if (p - 1) % 4 == 0 { 4 } else { 2 }
  // j = 0 model (0, 1): stab = #{u : u⁶ = 1} = gcd(6, p−1)
  let s0 = stabilizer_size(0L, 1L, p)
  let e0 = if (p - 1) % 6 == 0 {
    6
  } else if (p - 1) % 3 == 0 {
    3
  } else if (p - 1) % 2 == 0 {
    2
  } else {
    1
  }
  gen_ok && s1728 == e1728 && s0 == e0
}

///|
/// Number of supersingular j-invariants over F_{p²}: j ∈ F_{p²} with the
/// curve E_j (explicit model) satisfying a_{p²} ≡ 0 (mod p).
pub fn count_ss_j(p : Int32) -> Int32 {
  let fld = GF::make(p, 2)
  let q = fld.q() // p²
  let mut count = 0
  let mut x = 0
  while x < q {
    // interpret x as j ∈ F_{p²}: build the model A = −3j/(j−1728), B = −2j/(j−1728)
    let jv = x
    let one = 1 % p
    let j1728 = fld.mul(1728 % p, one)
    let den = fld.sub(jv, j1728)
    // model: den ≠ 0: A = −3j/(j−1728), B = −2j/(j−1728); den = 0 (j = 1728):
    // model (−1, 0)
    let a0 = if den != 0 && jv != 0 {
      let inv = fld.inv(den)
      fld.mul(fld.mul(p - 3, jv), inv)
    } else if jv == 0 {
      0 // j = 0: model y² = x³ + 1
    } else {
      p - 1 // j = 1728: model y² = x³ − x
    }
    let b0 = if den != 0 && jv != 0 {
      let inv = fld.inv(den)
      fld.mul(fld.mul(p - 2, jv), inv)
    } else if jv == 0 {
      1 // j = 0: b = 1
    } else {
      0
    }
    // count E(F_{p²}): y² = x³ + a0·x + b0 over GF(p, 2)
    let mut cnt = 1
    let mut xi = 0
    while xi < q {
      let xx = fld.mul(xi, xi)
      let xxx = fld.mul(xx, xi)
      let fx = fld.add(fld.add(xxx, fld.mul(a0, xi)), b0)
      cnt = cnt + 1 + fld.chi(fx)
      xi = xi + 1
    }
    let ap2 = q + 1 - cnt
    if (ap2 % p + p) % p == 0 {
      count = count + 1
    }
    x = x + 1
  }
  count
}

///|
/// T57c: classical formula #SS = ⌊p/12⌋ + ε.
pub fn ss_formula(p : Int32) -> Int32 {
  let eps = if p % 12 == 1 {
    0
  } else if p % 12 == 5 || p % 12 == 7 {
    1
  } else {
    2
  }
  p / 12 + eps
}

///|
/// T57c check: enumeration matches the formula.
pub fn ss_count_check(p : Int32) -> Bool {
  count_ss_j(p) == ss_formula(p)
}
