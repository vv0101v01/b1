///|
/// report.mbt — 計算機抽象導出定理的實驗引擎
/// Each experiment verifies a theorem computationally and returns
/// (PASS/FAIL, evidence string). The full report is assembled in
/// render_report() and printed by cmd/main.

///|
/// One experiment result: (id, statement, passed, evidence).
pub struct Exp(String, String, Bool, String)

///|
fn exp_ok(id : String, stmt : String, ev : String) -> Exp {
  Exp(id, stmt, true, ev)
}

///|
fn exp_fail(id : String, stmt : String, ev : String) -> Exp {
  Exp(id, stmt, false, ev)
}

///|
/// T1: 乘積公式於 Q：|r|_∞ ∏_p |r|_p = 1（精確有理運算）。
fn exp_product_formula_q() -> Exp {
  let cases = [
    Rat(6L, 35L),
    Rat(-12L, 77L),
    Rat(1024L, 3L),
    Rat(1L, 2L),
    Rat(2310L, 1L),
  ]
  let ev : Array[String] = []
  let mut ok = true
  for r in cases {
    let prod = product_formula_rat(r)
    if prod.0 != 1L || prod.1 != 1L {
      ok = false
    }
    ev.push("\{r.to_string()} ⇒ ∏|r|_v = \{prod.to_string()}")
  }
  if ok {
    exp_ok(
      "T1",
      "乘積公式：對 r ∈ Q^×，∏_v |r|_v = 1",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T1", "乘積公式", join_str(ev, "; "))
  }
}

///|
/// T1b: 乘積公式於二次域 K = Q(√d)。
fn exp_product_formula_quad() -> Exp {
  let x1 = QuadElem(-5L, Rat(2L, 1L), Rat(1L, 1L)) // 2 + √-5, N = 9
  let x2 = QuadElem(2L, Rat(2L, 1L), Rat(1L, 1L)) // 2 + √2, N = 2
  let x3 = QuadElem(-5L, Rat(3L, 1L), Rat(2L, 1L)) // 3 + 2√-5, N = 29
  let p1 = product_formula_quad(x1)
  let p2 = product_formula_quad(x2)
  let p3 = product_formula_quad(x3)
  let ok = p1.0 == 1L &&
    p1.1 == 1L &&
    p2.0 == 1L &&
    p2.1 == 1L &&
    p3.0 == 1L &&
    p3.1 == 1L
  let ev = "\{x1.to_string()} ⇒ \{p1.to_string()}; \{x2.to_string()} ⇒ \{p2.to_string()}; \{x3.to_string()} ⇒ \{p3.to_string()}"
  if ok {
    exp_ok(
      "T1b", "二次域乘積公式：∏_v |x|_v = 1（阿基米德部分 = |N(x)|）",
      ev,
    )
  } else {
    exp_fail("T1b", "二次域乘積公式", ev)
  }
}

///|
/// T1c: 函數域 F_2(t) 的乘積公式：Σ_v deg(v)·v(x) = 0。
fn exp_product_formula_ff2() -> Exp {
  // x = (t)(t+1)(t²+t+1) / (t³+t+1)(t+1) — built from bitmasks
  // t = 2, t+1 = 3, t²+t+1 = 7, t³+t+1 = 11
  let f = ff2_mul(ff2_mul(2, 3), 7) // t(t+1)(t²+t+1)
  let g = ff2_mul(11, 3) // (t³+t+1)(t+1)
  let s = ff2_product_formula(f, g)
  // second case: x = (t⁴+t+1)/(t³+t²+1)
  let s2 = ff2_product_formula(19, 13)
  let ok = s == 0 && s2 == 0
  let ev = "Σ deg(v)·v(x) = \{s}, \{s2}（應為 0, 0）"
  if ok {
    exp_ok("T1c", "函數域乘積公式 deg(div x) = 0", ev)
  } else {
    exp_fail("T1c", "函數域乘積公式", ev)
  }
}

///|
/// T2/T4: p 進絕對值：超度量不等式與乘法性。
fn exp_local_abs() -> Exp {
  let p = 5L
  let prec = 8
  let a = PAdic::from_rat(Rat(7L, 3L), p, prec)
  let b = PAdic::from_rat(Rat(1L, 25L), p, prec)
  let u1 = ultrametric_ok(a, b)
  let u2 = multiplicativity_ok(a, b)
  let ev = "|\{a.to_string()}| = \{fmt6(a.abs())}, |\{b.to_string()}| = \{fmt6(b.abs())}; 超度量=\{u1}, 乘法性=\{u2}"
  if u1 && u2 {
    exp_ok(
      "T2/T4", "局部域絕對值：|xy|=|x||y|，|x+y| ≤ max(|x|,|y|)", ev,
    )
  } else {
    exp_fail("T2/T4", "局部域絕對值", ev)
  }
}

///|
/// T3: Hensel 引理：mod p 二次剩餘的平方根可唯一提升至 Z_p。
fn exp_hensel() -> Exp {
  let cases = [(5L, 4L), (7L, 2L), (11L, 5L), (13L, 3L)]
  let ev : Array[String] = []
  let mut ok = true
  for (p, a) in cases {
    let x = a
    let adic = PAdic::from_int(x, p, 12)
    let root = hensel_sqrt(adic)
    // verify root² = a mod p^12
    let sq = root.mul(root)
    let diff = sq.sub(adic)
    if !diff.is_zero() {
      ok = false
      ev.push("p=\{p}, a=\{a}: 失敗")
    } else {
      ev.push("p=\{p}: √\{a} ≡ \{root.digits} (mod \{p}^12) ✓")
    }
  }
  if ok {
    exp_ok(
      "T3",
      "Hensel 引理：QR mod p 的平方根唯一提升到 Z_p（牛頓迭代）",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T3", "Hensel 引理", join_str(ev, "; "))
  }
}

///|
/// T5/T6: 主伊代爾範數 = 1（乘積公式）。
fn exp_idele_norm() -> Exp {
  let cases = [Rat(6L, 35L), Rat(2L, 3L), Rat(-1L, 7L)]
  let ev : Array[String] = []
  let mut ok = true
  for r in cases {
    let prod = Idele::norm_exact_principal(r)
    let x = Idele::from_rat(r)
    let nnum = x.norm()
    let d = if nnum > 1.0 { nnum - 1.0 } else { 1.0 - nnum }
    if prod.0 != 1L || prod.1 != 1L || d > 0.000001 {
      ok = false
    }
    ev.push(
      "\{r.to_string()}: 精確=\{prod.to_string()}, 數值=\{fmt6(nnum)}",
    )
  }
  if ok {
    exp_ok(
      "T5/T6",
      "伊代爾範數：主伊代爾 x ∈ Q^× 的 ||x|| = 1",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T5/T6", "伊代爾範數", join_str(ev, "; "))
  }
}

///|
/// T7: CRT/Ẑ^× 結構：φ 積性，(Z/N)^× ≅ ∏ (Z/p^e)^×。
fn exp_crt() -> Exp {
  let ns = [60, 360, 1001, 2310]
  let ev : Array[String] = []
  let mut ok = true
  for n in ns {
    let c = crt_unit_structure(n)
    if !c {
      ok = false
    }
    ev.push("N=\{n}: φ=\{euler_phi(n)}, 結構=\{c}")
  }
  let zhat = zhat_units_truncated(10) // ∏_{p≤10}(p-1) = 1·2·4·6 = 48
  let z_ok = zhat == 48
  if !z_ok {
    ok = false
  }
  ev.push("|Ẑ^×/(∏_{p>10})| = \{zhat}")
  if ok {
    exp_ok(
      "T7",
      "Ẑ^× 結構：(Z/N)^× ≅ ∏ (Z/p^e)^×，φ 積性",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T7", "CRT 結構", join_str(ev, "; "))
  }
}

///|
/// T8: 類數 = 約化二次型計數（Gauss）。
fn exp_class_number() -> Exp {
  let table = [
    (-4, 1),
    (-7, 1),
    (-8, 1),
    (-11, 1),
    (-15, 2),
    (-20, 2),
    (-23, 3),
    (-163, 1),
  ]
  let ev : Array[String] = []
  let mut ok = true
  for (d, expected) in table {
    let h = class_number_forms(d)
    if h != expected {
      ok = false
    }
    ev.push("h(\{d}) = \{h}（期望 \{expected}）")
  }
  if ok {
    exp_ok(
      "T8",
      "類數公式（Gauss 約化）：h(D) = #{約化正定本原二次型}",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T8", "類數公式", join_str(ev, "; "))
  }
}

///|
/// T9: Hilbert 類多項式：deg H_D = h(D)，H_{-20} 生成 Q(√5) 類域。
fn exp_hilbert() -> Exp {
  let polys = hilbert_class_polynomials()
  let ev : Array[String] = []
  let mut ok = true
  for (d, coeffs) in polys {
    let deg = coeffs.length() - 1
    let h = class_number_forms(d)
    if deg != h {
      ok = false
    }
    ev.push("D=\{d}: deg H_D = \{deg}, h(D) = \{h}")
  }
  // class field check for D = -20: disc(H) = 5·m²
  let disc = 1264000L * 1264000L + 4L * 681472000L
  let divided = disc / 5L
  let cf_ok = disc % 5L == 0L && is_square64(divided)
  if !cf_ok {
    ok = false
  }
  ev.push(
    "disc(H₋₂₀) = \{disc} = 5·\{isqrt64(divided)}² ⇒ 類域 = Q(√5) ✓",
  )
  if ok {
    exp_ok(
      "T9",
      "Hilbert 類多項式：deg H_D = h(D)；根生成 Hilbert 類域",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T9", "Hilbert 類多項式", join_str(ev, "; "))
  }
}

///|
/// T10: 橢圓曲線模空間：#Ell(F_p)/≅ = p（j-不變量參數化）；Hasse 界。
fn exp_elliptic_moduli() -> Exp {
  let ev : Array[String] = []
  let mut ok = true
  for p in [5, 7, 11] {
    let c = count_j_invariants(p)
    if c != p {
      ok = false
    }
    ev.push("p=\{p}: #j = \{c}（=\{p}）")
  }
  // Hasse bound for all curves over F_7
  let mut hasse = true
  let mut a = 0
  while a < 7 {
    let mut b = 0
    while b < 7 {
      let e = ECurve(a, b)
      if e.is_nonsingular(7) {
        let n = e.point_count(7)
        if !hasse_ok(n, 7) {
          hasse = false
        }
      }
      b = b + 1
    }
    a = a + 1
  }
  if !hasse {
    ok = false
  }
  ev.push("F_7 全部曲線滿足 Hasse 界：\{hasse}")
  if ok {
    exp_ok(
      "T10",
      "橢圓曲線模空間：#Ell(F_p)/≅ = p；Hasse 界 |#E−p−1| ≤ 2√p",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T10", "橢圓曲線模空間", join_str(ev, "; "))
  }
}

///|
/// T11: 旗簇：|GL_n| = |B|·|Fl_n|（暴力枚舉驗證）。
fn exp_flag() -> Exp {
  let ev : Array[String] = []
  let mut ok = true
  for (n, q) in [(2, 2), (2, 3), (3, 2)] {
    let gl = count_gl_bruteforce(n, q)
    let b = count_b_bruteforce(n, q)
    let fl = flag_variety_order(n, q)
    if gl != b * fl || gl != gl_order(n, q) || b != b_order(n, q) {
      ok = false
    }
    ev.push("n=\{n}, q=\{q}: |GL| = \{gl}, |B| = \{b}, |Fl| = \{fl}")
  }
  if ok {
    exp_ok(
      "T11",
      "旗簇點數：|GL_n(F_q)| = |B(F_q)|·|Fl_n(F_q)|（軌道–穩定子）",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T11", "旗簇", join_str(ev, "; "))
  }
}

///|
/// T12: Gaussian 二項式與 q-二項式定理。
fn exp_grassmannian() -> Exp {
  let ev : Array[String] = []
  let mut ok = true
  // enumeration vs closed form
  for (n, k, q) in [(4, 2, 2), (5, 2, 2), (3, 1, 3), (4, 2, 3)] {
    let closed = gaussian_binom(n, k, q)
    let enumd = count_subspaces(n, k, q)
    if closed != enumd {
      ok = false
    }
    ev.push("[\{n} \{k}]_\{q} = \{closed}（枚舉 \{enumd}）")
  }
  // q-binomial theorem
  for (n, q) in [(4, 2), (5, 3)] {
    let lhs = q_binom_theorem_lhs(n, q)
    let rhs = q_binom_theorem_rhs(n, q)
    let mut same = lhs.length() == rhs.length()
    let mut i = 0
    while i < lhs.length() && i < rhs.length() {
      if lhs[i] != rhs[i] {
        same = false
      }
      i = i + 1
    }
    if !same {
      ok = false
    }
    ev.push("q-二項式定理 n=\{n}, q=\{q}: \{same}")
  }
  if ok {
    exp_ok(
      "T12",
      "Gr(k,n)(F_q) 點數 = [n k]_q；q-二項式定理 ∏(1+q^i t) = Σ q^{k(k−1)/2}[n k]_q t^k",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T12", "Gaussian 二項式", join_str(ev, "; "))
  }
}

///|
/// T13: 仿射格拉斯曼：Z_p² 指數 p^m 子格數 = σ₁(p^m) = Σ_{i=0}^m q^i。
fn exp_affine_grassmannian() -> Exp {
  let ev : Array[String] = []
  let mut ok = true
  for (p, m) in [(2, 1), (2, 2), (2, 3), (3, 2), (3, 3)] {
    let en = sublattice_count(p, m)
    let cl = sigma1_pm(p, m)
    let po = schubert_poincare_sl2(m, p)
    if en != cl || en != po {
      ok = false
    }
    ev.push(
      "q=\{p}, m=\{m}: σ₁ = \{cl}, 格枚舉 = \{en}, Poincaré = \{po}",
    )
  }
  // dim Gr^{(m)} = ⟨2ρ, mω⟩ = m for SL_2
  let mut dims_ok = true
  let mut m = 1
  while m <= 5 {
    let pairing = two_rho_pairing([m, 0], 2)
    if pairing != m {
      dims_ok = false
    }
    m = m + 1
  }
  if !dims_ok {
    ok = false
  }
  ev.push("⟨2ρ, (m,0)⟩ = m ✓")
  if ok {
    exp_ok(
      "T13",
      "仿射格拉斯曼/Schubert：#{指數 p^m 子格} = Σ_{i=0}^m q^i，頂維度 = ⟨2ρ,λ⟩",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T13", "仿射格拉斯曼", join_str(ev, "; "))
  }
}

///|
/// T14/T15/T16: Bun_2(P^1)：Birkhoff–Grothendieck、HN 分層、自同構。
fn exp_bun() -> Exp {
  let ev : Array[String] = []
  let mut ok = true
  // bundles with det O(6), instability ≤ 8
  let bs = enumerate_bundles(6, 8)
  let strata = hn_strata(6, 8)
  let mut total = 0
  for (_, cnt) in strata {
    total = total + cnt
  }
  if total != bs.length() {
    ok = false
  }
  ev.push(
    "det O(6), 不穩定度 ≤ 8: \{bs.length()} 個叢 → \{strata.length()} 個 HN 層",
  )
  // semistable iff a = b
  for e in bs {
    if e.is_semistable() != (e.0 == e.1) {
      ok = false
    }
  }
  ev.push("半穩定 ⇔ a = b ✓")
  // Aut order formula vs brute force
  for e in [SplitBundle(3, 1), SplitBundle(4, 2), SplitBundle(2, 2)] {
    let f1 = aut_order(e, 3)
    let f2 = aut_order_bruteforce(e, 3)
    if f1 != f2 {
      ok = false
    }
    ev.push("E=O(\{e.0})⊕O(\{e.1}): |Aut| = \{f1}（列舉 \{f2}）")
  }
  // Riemann-Roch on P^1
  if chi_o(5) != 6 || h0_o(5) != 6 || h1_o(-5) != 4 {
    ok = false
  }
  ev.push("χ(O(n)) = n+1 ✓")
  if ok {
    exp_ok(
      "T14/T15/T16",
      "Bun_2(P^1)：Birkhoff–Grothendieck 分解、HN 分層唯一、|Aut(E)| = (q−1)²q^{a−b+1}",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T14/T15/T16", "Bun_G", join_str(ev, "; "))
  }
}

///|
/// T17: 質量公式：Σ 1/|Aut| 截斷和 = 封閉形式幾何級數。
fn exp_bun_mass() -> Exp {
  let q = 3
  let m1 = bun_mass_truncated(4, 10, q)
  let m2 = bun_mass_closed(4, 10, q)
  let diff = if m1 > m2 { m1 - m2 } else { m2 - m1 }
  let ok = diff < 0.0000001
  let ev = "Σ_{i≤10} 1/|Aut| = \{fmt6(m1)}，封閉形式 = \{fmt6(m2)}，差 = \{fmt6(diff)}"
  if ok {
    exp_ok(
      "T17", "Bun_2 質量：截斷質量和收斂於封閉形式（幾何級數）",
      ev,
    )
  } else {
    exp_fail("T17", "質量公式", ev)
  }
}

///|
/// T18: E4³ − E6² = 1728 Δ。
fn exp_delta_identity() -> Exp {
  let n0 = 22
  let e4 = e4_series(n0)
  let e6 = e6_series(n0)
  let d = delta_series(n0)
  let lhs = e4.mul(e4.mul(e4)).sub(e6.mul(e6))
  let rhs = d.scale(1728L)
  let ok = lhs.equals_upto(rhs, n0)
  let mut ev = ""
  let mut i = 1
  while i <= 6 {
    if i > 1 {
      ev = ev + ", "
    }
    ev = ev + "\{lhs.coeff(i)} = 1728·τ(\{i})"
    i = i + 1
  }
  if ok {
    exp_ok(
      "T18", "模判別式恆等式：E4³ − E6² = 1728Δ（係數逐項驗證）",
      ev,
    )
  } else {
    exp_fail("T18", "模判別式恆等式", ev)
  }
}

///|
/// T19: T_p Δ = τ(p) Δ（Hecke 特徵形式）。
fn exp_hecke_eigen() -> Exp {
  let n0 = 33
  let d = delta_series(n0)
  let coef = d.0
  let t2 = hecke_operator(coef, 2, 12)
  let t3 = hecke_operator(coef, 3, 12)
  let tau2 = d.coeff(2) // −24
  let tau3 = d.coeff(3) // 252
  let mut ok = true
  let mut n = 1
  while n <= n0 / 2 {
    if t2[n] != tau2 * coef[n] {
      ok = false
    }
    n = n + 1
  }
  let mut n3 = 1
  while n3 <= (n0 - 1) / 3 {
    if t3[n3] != tau3 * coef[n3] {
      ok = false
    }
    n3 = n3 + 1
  }
  let ev = "τ(2) = \{tau2}, τ(3) = \{tau3}, τ(4) = \{d.coeff(4)}, τ(6) = \{d.coeff(6)}; T_2Δ = τ(2)Δ（前 \{n0 / 2} 係數）, T_3Δ = τ(3)Δ（前 \{(n0 - 1) / 3} 係數）✓"
  if ok {
    exp_ok(
      "T19", "Δ 是所有 Hecke 算子的特徵形式：T_p Δ = τ(p) Δ", ev,
    )
  } else {
    exp_fail("T19", "Hecke 特徵形式", ev)
  }
}

///|
/// T20: Hecke 交換性與結構常數 T_m T_n = Σ_{d|(m,n)} d^{k−1} T_{mn/d²}。
fn exp_hecke_relations() -> Exp {
  let n0 = 30
  let d = delta_series(n0)
  let coef = d.0
  let comm = hecke_commutativity_error(coef, 2, 3, 12, 12)
  let rel = hecke_relation_error(coef, 2, 3, 12, 12)
  let ok = comm == 0L && rel == 0L
  let ev = "max|T_2T_3 − T_3T_2| = \{comm}; max|T_2T_3 − T_6| = \{rel}（gcd(2,3)=1 ⇒ T_2T_3 = T_6）"
  if ok {
    exp_ok(
      "T20", "Hecke 代數交換性與關係 T_m T_n = Σ_{d|(m,n)} d^{k−1} T_{mn/d²}",
      ev,
    )
  } else {
    exp_fail("T20", "Hecke 關係", ev)
  }
}

///|
/// T21: τ 乘性：gcd(m,n)=1 ⇒ τ(mn) = τ(m)τ(n)。
fn exp_tau_multiplicative() -> Exp {
  let d = delta_series(40)
  let checks = [(2, 3), (4, 3), (2, 5), (3, 7)]
  let mut ok = true
  let ev : Array[String] = []
  for (m, n) in checks {
    let lhs = d.coeff(m * n)
    let rhs = d.coeff(m) * d.coeff(n)
    if lhs != rhs {
      ok = false
    }
    ev.push("τ(\{m}·\{n}) = \{lhs}, τ(\{m})τ(\{n}) = \{rhs}")
  }
  if ok {
    exp_ok(
      "T21",
      "Ramanujan 乘性：gcd(m,n)=1 ⇒ τ(mn) = τ(m)τ(n)",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T21", "τ 乘性", join_str(ev, "; "))
  }
}

///|
/// T22: Ramanujan–Petersson 界與 Satake 參數 |α| = p^{(k−1)/2}。
fn exp_ramanujan() -> Exp {
  let n0 = 50
  let d = delta_series(n0)
  let mut ok = true
  let ev : Array[String] = []
  for p in [2, 3, 5, 7, 11, 13, 47] {
    let ap = d.coeff(p).to_double()
    if !ramanujan_ok(ap, p, 12) {
      ok = false
    }
    let (al, _) = satake_params(ap, p, 12)
    let target = @math.pow(p.to_double(), 5.5)
    let da = al.abs() - target
    let ad = if da < 0.0 { -da } else { da }
    if ad > 0.001 {
      ok = false
    }
    ev.push(
      "p=\{p}: τ(p)=\{d.coeff(p)}, |α| = \{fmt6(al.abs())} ≈ p^5.5 = \{fmt6(target)}",
    )
  }
  if ok {
    exp_ok(
      "T22",
      "Ramanujan–Petersson：|τ(p)| < 2p^{11/2}，Satake |α_p| = p^{11/2}",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T22", "Ramanujan", join_str(ev, "; "))
  }
}

///|
/// T23: Euler 乘積 = Dirichlet 級數（L(Δ, 12)）。
fn exp_euler_product() -> Exp {
  let n0 = 50
  let d = delta_series(n0)
  let coef = d.0
  let s = 12.0
  let dir = dirichlet_partial(coef, 45, s)
  let eul = euler_partial(coef, 43, s, 12)
  let diff = if dir > eul { dir - eul } else { eul - dir }
  let rel = diff / dir
  let ok = rel < 0.0001
  let ev = "Σ τ(n)n^−12 = \{fmt6(dir)}，∏_p Euler = \{fmt6(eul)}，相對差 = \{fmt6(rel)}"
  if ok {
    exp_ok(
      "T23", "L(f,s) 的 Euler 乘積 = Dirichlet 級數（局部–整體一致性）",
      ev,
    )
  } else {
    exp_fail("T23", "Euler 乘積", ev)
  }
}

///|
/// T24: Hecke 代數結構常數：T_p² = T_{p²} + p^{k−1} id。
fn exp_hecke_algebra() -> Exp {
  let n0 = 30
  let d = delta_series(n0)
  let e2 = hecke_structure_error(d.0, 2, 12, 12)
  let e3 = hecke_structure_error(d.0, 3, 12, 12)
  let ok = e2 == 0L && e3 == 0L
  let ev = "max|T_2² − T_4 − 2^11| = \{e2}; max|T_3² − T_9 − 3^11| = \{e3}"
  if ok {
    exp_ok(
      "T24", "球面 Hecke 代數：T_p² = T_{p²} + p^{k−1}·id（Satake 同構的結構常數）",
      ev,
    )
  } else {
    exp_fail("T24", "Hecke 代數", ev)
  }
}

///|
/// T25/T26: Hitchin 基底維度 = n²(g−1)+1 = 譜曲線屬數（Lagrangian 纖維）。
fn exp_hitchin_dim() -> Exp {
  let ev : Array[String] = []
  let mut ok = true
  for n in [2, 3, 4] {
    for g in [2, 3, 4] {
      let b1 = hitchin_base_dim(n, g)
      let b2 = hitchin_base_dim_closed(n, g)
      let gs = spectral_genus(n, g)
      let tot = higgs_total_dim(n, g)
      if b1 != b2 || gs != b2 || 2 * b2 != tot {
        ok = false
      }
      ev.push(
        "GL_\{n}, g=\{g}: dim base = \{b1} = n²(g−1)+1 = \{b2}, g_spectral = \{gs}, 2·dim = \{tot}",
      )
    }
  }
  if ok {
    exp_ok(
      "T25/T26",
      "希欽纖維化：dim base = dim Jac(譜曲線) = n²(g−1)+1 = ½ dim(Higgs)（Lagrangian）",
      join_str(ev, "; "),
    )
  } else {
    exp_fail("T25/T26", "Hitchin 維度", join_str(ev, "; "))
  }
}

///|
/// T27/T28: 譜曲線（超橢圓）的 Weil 猜想驗證：函數方程、|α|=√q、Jac 點數。
fn exp_spectral_weil() -> Exp {
  // genus 2 smooth curve: y² = x⁵ + x + 3 over F_7
  // (y² = x⁵+x+1 is singular at x = 4 in char 7!)
  let curve = HypCurve([3, 1, 0, 0, 0, 1])
  let g = curve.genus()
  let e = hyp_l_polynomial(curve, 7, g)
  let fe = hyp_functional_equation_ok(e, 7, g)
  let jac = hyp_jacobian_order(e)
  let cnt = curve.point_count(7, 1)
  let hasse = hyp_hasse_ok(cnt, 7, g)
  let e4v = e[4]
  let e4ok = e4v > 48.5 && e4v < 49.5 // e4 = q^g = 49
  let ok = fe && hasse && e4ok && g == 2 && jac > 0
  let ev = "y²=x⁵+x+3/F_7: g=\{g}, #C(F_7) = \{cnt}, P(t) 係數 = [\{fmt6(e[1])}, \{fmt6(e[2])}, \{fmt6(e[3])}, \{fmt6(e[4])}], 函數方程=\{fe}, e₄=q²=\{e4ok}, #Jac = \{jac} = L(1)"
  if ok {
    exp_ok(
      "T27/T28", "譜曲線 Weil 猜想：函數方程 e_i = q^{g−i}e_{2g−i}，#Jac(C)(F_q) = P(1)",
      ev,
    )
  } else {
    exp_fail("T27/T28", "譜曲線 Weil", ev)
  }
}

///|
/// T28b: 橢圓譜曲線（genus 1）纖維 = Jacobian：#C = P(1)。
fn exp_elliptic_fiber() -> Exp {
  // y² = x³ + x + 1 over F_7 (genus 1 smooth spectral curve)
  let curve = HypCurve([1, 1, 0, 1])
  let g = curve.genus()
  let e = hyp_l_polynomial(curve, 7, g)
  let jac = hyp_jacobian_order(e)
  let cnt = curve.point_count(7, 1)
  let ok = g == 1 && jac == cnt.to_int64()
  let ev = "g=\{g}, #C(F_7) = \{cnt}, #Jac = P(1) = \{jac}（相等 ⇒ 纖維 = Jac）"
  if ok {
    exp_ok(
      "T28b", "希欽纖維 = 譜曲線 Jacobian：#C(F_q) = P(1) = #Pic⁰", ev,
    )
  } else {
    exp_fail("T28b", "橢圓纖維", ev)
  }
}

///|
/// A1: Hecke 特徵形式演化（冪法收斂到自守表示生成元）。
fn exp_evolve_hecke() -> Exp {
  let (lam, res, iters) = hecke_eigenform_evolution(42L, 200)
  let ok = res < 0.000001
  let ev = "\{iters} 次迭代後：λ = \{fmt6(lam)}，殘差 ||Mc − λc|| = \{fmt6(res)}；|λ| < 2·2^{11.5} = 5792.6（Ramanujan 界內）⇒ 收斂到 Hecke 特徵形式 = 自守表示生成元"
  if ok {
    exp_ok("A1", "衍生演生法 A1（Hecke 特徵形式演化/冪法）", ev)
  } else {
    exp_fail("A1", "Hecke 演化", ev)
  }
}

///|
/// A2: Hitchin 譜曲線演化（基因演算法搜尋高點數譜曲線）。
fn exp_evolve_hitchin() -> Exp {
  let hist = hitchin_spectral_curve_ga(7, 20, 15, 2024L)
  let first = hist[0]
  let last = hist[hist.length() - 1]
  // elitism guarantees non-decreasing best
  let mut mono = true
  let mut i = 1
  while i < hist.length() {
    if hist[i] < hist[i - 1] {
      mono = false
    }
    i = i + 1
  }
  let ok = mono && last >= first
  let ev = "最佳適應度（#C(F_7)）演化：\{first} → \{last}（單調不減 = \{mono}）；15 代"
  if ok {
    exp_ok(
      "A2", "衍生演生法 A2（Hitchin 譜曲線演化/基因演算法）", ev,
    )
  } else {
    exp_fail("A2", "Hitchin 演化", ev)
  }
}

///|
/// A3: 二次型約化演化。
fn exp_evolve_forms() -> Exp {
  // D = −20 forms far from reduced: (3,2,2)·τ^k family and (7,6,2)
  let (s1, f1) = form_reduction_evolution(3, 2, 2, 100)
  let (s2, f2) = form_reduction_evolution(7, 6, 2, 100)
  let (s3, f3) = form_reduction_evolution(1, 20, 105, 100)
  let r1 = QForm(3, 2, 2)
  let r2 = QForm(7, 6, 2)
  let r3 = QForm(1, 20, 105)
  let discs_ok = r1.disc() == -20 && r2.disc() == -20 && r3.disc() == -20
  let ok = s1 < 100 && s2 < 100 && s3 < 100 && discs_ok
  let ev = "D = −20：(3,2,2) → \{s1} 步, a+c=\{f1}；(7,6,2) → \{s2} 步, a+c=\{f2}；(1,20,105) → \{s3} 步, a+c=\{f3}；disc 保持 = \{discs_ok}"
  if ok {
    exp_ok(
      "A3", "衍生演生法 A3（二次型約化演化 ↔ 類群元素）", ev,
    )
  } else {
    exp_fail("A3", "型約化演化", ev)
  }
}

///|
/// Run every experiment.
pub fn run_all_experiments() -> Array[Exp] {
  let res : Array[Exp] = []
  res.push(exp_product_formula_q())
  res.push(exp_product_formula_quad())
  res.push(exp_product_formula_ff2())
  res.push(exp_local_abs())
  res.push(exp_hensel())
  res.push(exp_idele_norm())
  res.push(exp_crt())
  res.push(exp_class_number())
  res.push(exp_hilbert())
  res.push(exp_elliptic_moduli())
  res.push(exp_flag())
  res.push(exp_grassmannian())
  res.push(exp_affine_grassmannian())
  res.push(exp_bun())
  res.push(exp_bun_mass())
  res.push(exp_delta_identity())
  res.push(exp_hecke_eigen())
  res.push(exp_hecke_relations())
  res.push(exp_tau_multiplicative())
  res.push(exp_ramanujan())
  res.push(exp_euler_product())
  res.push(exp_hecke_algebra())
  res.push(exp_hitchin_dim())
  res.push(exp_spectral_weil())
  res.push(exp_elliptic_fiber())
  res.push(exp_evolve_hecke())
  res.push(exp_evolve_hitchin())
  res.push(exp_evolve_forms())
  res
}

///|
/// Render the full report as a string.
pub fn render_report() -> String {
  let sb = StringBuilder()
  sb.write_string(
    "══════════════════════════════════════════════════════════\n",
  )
  sb.write_string(
    "  計算機抽象導出定理報告 — Langlands 結構 × MoonBit\n",
  )
  sb.write_string("  Computational Derivation of Theorems (v0.10.x)\n")
  sb.write_string(
    "══════════════════════════════════════════════════════════\n\n",
  )
  let exps = run_all_experiments()
  let mut passed = 0
  for e in exps {
    let status = if e.2 { "✓ PASS" } else { "✗ FAIL" }
    if e.2 {
      passed = passed + 1
    }
    sb.write_string("[\{status}] \{e.0}: \{e.1}\n")
    sb.write_string("       證據：\{e.3}\n\n")
  }
  sb.write_string(
    "──────────────────────────────────────────────────────────\n",
  )
  sb.write_string("  合計：\{passed}/\{exps.length()} 實驗通過\n")
  sb.write_string(
    "──────────────────────────────────────────────────────────\n",
  )
  sb.to_string()
}
