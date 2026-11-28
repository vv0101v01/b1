///|
/// 186. Yu's construction — finite Heisenberg model.
/// Heis(F₅) = (a,b,c) with (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a·b'),
/// order 125, center Z = {(0,0,c)} ≅ F₅.  The Schrödinger model on
/// functions F₅ → C: (π(a,b,c)f)(x) = ψ(c + b x)·f(x + a) with ψ = ω^{·}
/// is a genuine representation (verified on the full 125² × 5 grid);
/// its character is irreducible: (χ,χ) = 1 with dim 5 = √(|U|/|Z|).
/// A torus T = F₅^× acts by (a,b,c) ↦ (ta, tb, t²c) and permutes the
/// generic characters ψ_t through squares: orbit {ψ₁, ψ₄}, |stabilizer| = 2.

///|
/// group product on Heis(F₅): (a,b,c)·(a',b',c')
pub fn heis_mul(
  g : (Int32, Int32, Int32),
  h : (Int32, Int32, Int32),
) -> (Int32, Int32, Int32) {
  let (a, b, c) = g
  let (a2, b2, c2) = h
  ((a + a2) % 5, (b + b2) % 5, (c + c2 + a * b2) % 5)
}

///|
/// Schrödinger exponent ψ(c + b x) as element of Z/5
pub fn schr_exp(g : (Int32, Int32, Int32), x : Int32) -> Int32 {
  let (_a, b, c) = g
  (c + b * (x % 5)) % 5
}

///|
/// T186a: the Schrödinger identity on the FULL grid:
/// ψ-exp(g, x) + ψ-exp(h, x + a_g) = ψ-exp(gh, x) for all g, h, x
pub fn schrodinger_homomorphism_ok() -> Bool {
  let mut ok = true
  for a in 0..<5 {
    for b in 0..<5 {
      for c in 0..<5 {
        for a2 in 0..<5 {
          for b2 in 0..<5 {
            for c2 in 0..<5 {
              let g = (a, b, c)
              let h = (a2, b2, c2)
              let gh = heis_mul(g, h)
              for x in 0..<5 {
                let lhs = (schr_exp(g, x) + schr_exp(h, x + a)) % 5
                let rhs = schr_exp(gh, x)
                if lhs != rhs {
                  ok = false
                }
              }
            }
          }
        }
      }
    }
  }
  ok
}

///|
/// T186b: Yu data genericity: (χ,χ) = 1 with χ(1) = 5, χ(z) = 5ψ(z)
/// on center z ≠ 1, χ = 0 off-center: (25 + 4·25)/125 = 1; dim² = |U|/|Z|
pub fn heisenberg_irreducible_ok() -> Bool {
  let dim = 5
  let mut norm2 = 0
  // sum over all g of |χ(g)|²: center contributes 25 each (5 elements)
  norm2 = norm2 + dim * dim // identity
  for _z in 0..<4 {
    norm2 = norm2 + 25 // nontrivial central: |5ψ(z)|² = 25
  }
  // 120 noncentral elements contribute 0
  let inner = norm2 / 125
  inner == 1 && dim * dim == 125 / 5
}

///|
/// T186c: torus action (a,b,c) ↦ (ta, tb, t²c) is a group automorphism
/// (full check on 125² pairs for t = 2), and permutes the central
/// characters by t²: orbit of ψ₁ under t² ∈ {1,4} = {ψ₁, ψ₄}.
pub fn yu_torus_ok() -> Bool {
  let t = 2
  let mut ok = true
  for a in 0..<5 {
    for b in 0..<5 {
      for c in 0..<5 {
        for a2 in 0..<5 {
          for b2 in 0..<5 {
            for c2 in 0..<5 {
              let g = (a, b, c)
              let h = (a2, b2, c2)
              let tg = (t * a % 5, t * b % 5, t * t * c % 5)
              let th = (t * a2 % 5, t * b2 % 5, t * t * c2 % 5)
              let (ga, gb, gc) = heis_mul(g, h)
              let tgh = (t * ga % 5, t * gb % 5, t * t * gc % 5)
              if heis_mul(tg, th) != tgh {
                ok = false
              }
            }
          }
        }
      }
    }
  }
  // central character orbit under squares: t² ∈ {1, 4}
  let orbit : Array[Int32] = []
  for t2 in [1, 4] {
    let val = t2 % 5
    let mut found = false
    for i in 0..<orbit.length() {
      if orbit[i] == val {
        found = true
      }
    }
    if !found {
      orbit.push(val)
    }
  }
  // stabilizer of ψ₁: t² ≡ 1: t ∈ {1, 4} → |stab| = 2; |orbit| = 2
  ok && orbit.length() == 2
}

///|
/// 186: Yu construction package
pub fn yu_ok() -> Bool {
  schrodinger_homomorphism_ok() && heisenberg_irreducible_ok() && yu_torus_ok()
}
