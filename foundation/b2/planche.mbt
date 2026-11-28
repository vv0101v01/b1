///|
/// 189. Mild functoriality and the Plancherel transform — exact Fourier
/// analysis on G = (Z/2)² with sign characters (all arithmetic in Int64).
/// Plancherel identity, convolution theorem, Fourier inversion; mild
/// functoriality = inflation along the norm map π : (Z/2)² → Z/2 has
/// spectral support in the chars factoring through π, with exact mass
/// scaling; temperedness bound preserved.

///|
/// elements of G = (Z/2)² as 0..3 (bits); character χ_s(g) = (−1)^{s·g}
fn sign_char(s : Int32, g : Int32) -> Int64 {
  let dot = s / 2 * (g / 2) + s % 2 * (g % 2)
  if dot % 2 == 0 {
    1L
  } else {
    -1L
  }
}

///|
/// Fourier transform f̂(s) = Σ_g f(g) χ_s(g)
pub fn ft4(f : Array[Int64]) -> Array[Int64] {
  let out : Array[Int64] = []
  for s in 0..<4 {
    let mut acc = 0L
    for g in 0..<4 {
      acc = acc + f[g] * sign_char(s, g)
    }
    out.push(acc)
  }
  out
}

///|
/// T189a: Plancherel identity on (Z/2)²: |G|·Σ f(g)² = Σ f̂(χ)² (exact)
pub fn plancherel_ok() -> Bool {
  let tests : Array[Array[Int64]] = [
    [1L, 0L, 0L, 0L],
    [1L, 2L, -3L, 1L],
    [2L, 2L, 2L, 2L],
    [0L, 1L, 1L, 0L],
  ]
  let mut ok = true
  for t in 0..<tests.length() {
    let f = tests[t]
    let fh = ft4(f)
    let mut lhs = 0L
    for g in 0..<4 {
      lhs = lhs + f[g] * f[g]
    }
    lhs = lhs * 4L
    let mut rhs = 0L
    for s in 0..<4 {
      rhs = rhs + fh[s] * fh[s]
    }
    if lhs != rhs {
      ok = false
    }
  }
  ok
}

///|
/// convolution (f∗g)(x) = Σ_y f(y)g(x+y) on (Z/2)²
pub fn conv4(f : Array[Int64], g : Array[Int64]) -> Array[Int64] {
  let out : Array[Int64] = []
  for x in 0..<4 {
    let mut acc = 0L
    for y in 0..<4 {
      // x + y bitwise xor on two bits
      let z = (x / 2 + y / 2) % 2 * 2 + (x % 2 + y % 2) % 2
      acc = acc + f[y] * g[z]
    }
    out.push(acc)
  }
  out
}

///|
/// T189b: convolution theorem: (f∗g)̂ = f̂ · ĝ pointwise (exact)
pub fn convolution_theorem_ok() -> Bool {
  let f = [1L, 2L, -3L, 1L]
  let g = [0L, 1L, 1L, 0L]
  let lhs = ft4(conv4(f, g))
  let fh = ft4(f)
  let gh = ft4(g)
  let mut ok = true
  for s in 0..<4 {
    if lhs[s] != fh[s] * gh[s] {
      ok = false
    }
  }
  ok
}

///|
/// Fourier inversion: f = (1/|G|) Σ f̂(χ)χ (exact)
pub fn inversion_ok() -> Bool {
  let f = [1L, 2L, -3L, 1L]
  let fh = ft4(f)
  let mut ok = true
  for g in 0..<4 {
    let mut acc = 0L
    for s in 0..<4 {
      acc = acc + fh[s] * sign_char(s, g)
    }
    if acc / 4L != f[g] {
      ok = false
    }
  }
  ok
}

///|
/// T189c: mild functoriality — inflation h = f ∘ π with π(a,b) = a+b:
/// spectral support of h lies in {χ₀₀, χ₁₁} (the chars factoring through
/// π); mass scaling: Σ h² = 2·Σ f²; Plancherel stays exact for h.
pub fn mild_functorial_ok() -> Bool {
  // f lives on B = Z/2; h = f ∘ π on G = (Z/2)² (π: 0↦0, 1↦1, 2↦1, 3↦0)
  let fB = [3L, -1L]
  let h = [fB[0], fB[1], fB[1], fB[0]]
  let hh = ft4(h)
  // support containment: hh[01] = hh[10] = 0 (chars not factoring through π)
  let support_ok = hh[1] == 0L && hh[2] == 0L
  // mass scaling: Σ_G h² = |G/B| · Σ_B f² = 2·Σ_B f²
  let mut mass_b = 0L
  let mut mass_h = 0L
  for g in 0..<2 {
    mass_b = mass_b + fB[g] * fB[g]
  }
  for g in 0..<4 {
    mass_h = mass_h + h[g] * h[g]
  }
  let mass_ok = mass_h == 2L * mass_b
  // Plancherel for h
  let lhs = mass_h * 4L
  let mut rhs = 0L
  for s in 0..<4 {
    rhs = rhs + hh[s] * hh[s]
  }
  // temperedness bound: |ĥ(χ)| ≤ Σ|h|
  let mut absh = 0L
  for g in 0..<4 {
    if h[g] < 0L {
      absh = absh - h[g]
    } else {
      absh = absh + h[g]
    }
  }
  let mut temp_ok = true
  for s in 0..<4 {
    let v = if hh[s] < 0L { -hh[s] } else { hh[s] }
    if v > absh {
      temp_ok = false
    }
  }
  support_ok && mass_ok && lhs == rhs && temp_ok
}

///|
/// 189: Plancherel + mild functoriality package
pub fn plancherel_all_ok() -> Bool {
  plancherel_ok() &&
  convolution_theorem_ok() &&
  inversion_ok() &&
  mild_functorial_ok()
}
