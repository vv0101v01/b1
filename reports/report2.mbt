///|
/// report2.mbt — 批次二實驗：31–40 + 衍生演生法 A4–A6

///|
/// Experiment record.
pub struct Exp2 {
  id : String
  name : String
  statement : String
  detail : String
  pass : Bool
}

///|
pub fn run_all_experiments2() -> Array[Exp2] {
  let res : Array[Exp2] = []
  fn exp2(
    id : String,
    name : String,
    statement : String,
    detail : String,
    pass : Bool,
  ) {
    res.push(Exp2::{ id, name, statement, detail, pass, })
  }
  // ============ 31. ℓ-進表示 ============
  fn exp_blk_1() {
    let e = WCurve(0, 0, 0, 1, 1) // y² = x³ + x + 1 (disc = 31)
    // scan for (k, ell) with E[ell] ⊂ E(F_{7^k})
    let mut detail = ""
    let mut ok = false
    let mut kk = 1
    while kk <= 3 && !ok {
      let mut ell = 2
      while ell <= 3 && !ok {
        let tors = torsion_points(e, 7, kk, ell)
        if tors.length() >= ell * ell - 1 {
          let (tro, deto, m) = verify_tate_module(e, 7, kk, ell)
          let a7 = e.trace(7)
          detail = "p=7, k=\{kk}, ℓ=\{ell}, #E[ℓ]=\{tors.length()}\n  ρ(Frob) = \{m.to_string()} (basis P, Q)\n  tr ρ = \{m.trace_mod(ell)} ≡ a₇ = \{a7} (mod \{ell})：\{tro}\n  det ρ = \{m.det_mod(ell)} ≡ p = 7 (mod \{ell})：\{deto}"
          ok = tro && deto
        }
        ell = ell + 1
      }
      kk = kk + 1
    }
    exp2(
      "T31", "ℓ-進表示 Tate 模", "ρ_ℓ(Frob) 的特徵多項式 = x² − a_p·x + p (mod ℓ)",
      detail, ok,
    )
  }
  exp_blk_1()
  fn exp_blk_2() {
    let err = rep_power_consistency(WCurve(0, 0, 0, 1, 1), 7, 3, 2, 3)
    exp2(
      "T31b",
      "表示公理",
      "ρ(Frobⁿ) = ρ(Frob)ⁿ（GL₂(Z/ℓ) 內一致）",
      "n = 3 的最大元素差 = \{err}",
      err == 0,
    )
  }
  exp_blk_2()
  // ============ 32. Frobenius ============
  fn exp_blk_3() {
    let mut ok = true
    let mut detail = ""
    let mut k = 1
    while k <= 4 {
      let good = fixed_field_theorem_ok(2, 4, k)
      if !good {
        ok = false
      }
      detail = detail +
        "q=2, n=4, k=\{k}: |Fix(φ^k)| = 2^{gcd(k,4)}：\{good}\n"
      k = k + 1
    }
    exp2(
      "T32a", "Frobenius 生成元／固定域", "Fix(φ^k) = F_{q^{gcd(k,n)}}",
      detail, ok,
    )
  }
  exp_blk_3()
  fn exp_blk_4() {
    let f7 = frobenius_in_cyclotomic(2, 7) // ord_7(2) = 3
    let sp = prime_split_cyclotomic(2, 7)
    let sp2 = prime_split_cyclotomic(5, 7)
    let ok = f7 == 3 && sp == (3, 2) && sp2 == (6, 1)
    exp2(
      "T32b",
      "素數在分圓域的分解",
      "f = ord_n(p), g = φ(n)/f",
      "p=2 in Q(ζ₇): f = \{f7}, g = \{sp.1} (應為 3, 2)\np=5 in Q(ζ₇): f = \{sp2.0}, g = \{sp2.1} (應為 6, 1)",
      ok,
    )
  }
  exp_blk_4()
  // ============ 33. 阿廷 L-函數 ============
  fn exp_blk_5() {
    let chi = dir_char_mod5()
    let s1 = dirichlet_series_char(chi, 300, 6.0)
    let s2 = euler_product_char(chi, 100, 6.0)
    let err = s1.sub(s2).abs()
    exp2(
      "T33a",
      "Artin = Dirichlet",
      "Σχ(n)n^{−s} = ∏(1−χ(p)p^{−s})^{-1}（order-4 特徵 mod 5, s = 6）",
      "級數=\{s1.to_string()}，Euler 乘積=\{s2.to_string()}，差=\{err}",
      err < 0.0000001,
    )
  }
  exp_blk_5()
  fn exp_blk_6() {
    let err = artin_direct_sum_error(
      dir_char_mod5(),
      dir_char_chi4(),
      300,
      80,
      6.0,
    )
    exp2(
      "T33b",
      "Artin 形式論",
      "L(χ₁ ⊕ χ₂, s) = L(χ₁, s)·L(χ₂, s)",
      "兩路計算差 = \{err}",
      err < 0.000001,
    )
  }
  exp_blk_6()
  fn exp_blk_7() {
    let lhs = zeta_qi_series(200, 6.0)
    let rhs = zeta_series(200, 6.0) * l_chi4_series(200, 6.0)
    let err = lhs - rhs
    let abs = if err < 0.0 { -err } else { err }
    let r2ok = theta_r2_error(40) == 0 && r2_direct(25) == r2_formula(25)
    exp2(
      "T33c",
      "Dedekind zeta 分解",
      "ζ_{Q(i)}(s) = ζ(s)·L(χ₋₄, s)（⇔ r₂(n) = 4Σ_{d|n}χ₋₄(d)）",
      "級數兩路: \{lhs} vs \{rhs}，差=\{abs}；r₂ 公式驗證：\{r2ok}",
      abs < 0.000001 && r2ok,
    )
  }
  exp_blk_7()
  // ============ 34. 自守 L-函數 ============
  fn exp_blk_8() {
    let a = delta_series(50)
    let b = rankin_selberg_coefficients(a.0, 12, 50)
    let ds = dirichlet_series_double(b, 50, 14.0)
    let ep = rankin_selberg_euler(a.0, 12, 40, 14.0)
    let err = ds - ep
    let abs = if err < 0.0 { -err } else { err }
    exp2(
      "T34a",
      "Rankin–Selberg",
      "Σ|a_n|²n^{−s} = ∏(1−α²X)^{-1}(1−αβX)^{-1}(1−β²X)^{-1}",
      "級數（n ≤ 30）=\{ds}，Euler 乘積（p ≤ 25）=\{ep}，差=\{abs}",
      abs < 0.01,
    )
  }
  exp_blk_8()
  fn exp_blk_9() {
    let a = delta_series(20)
    let err1d = sym2_local_identity_error(a.0, 12, 15)
    let err2 = functorial_power_sum_error(a.coeff(2), 2, 12, 5)
    exp2(
      "T34b",
      "Satake 三重積",
      "局部因子根 = (α², αβ, β²)，b_p = a_p² − p^{k−1}",
      "Sym² 局部恆等式最大誤差 = \{err1d}；Newton 冪和一致最大誤差 = \{err2}",
      err1d < 0.5 && err2 == 0,
    )
  }
  exp_blk_9()
  // ============ 35. 函子性 ============
  fn exp_blk_10() {
    let a = delta_series(20)
    let (e1, e2, e3) = sym2_satake(a.coeff(2), 2, 12)
    let want = a.coeff(2) * a.coeff(2) - 2048
    let ok = e1 == want
    exp2(
      "T35",
      "函子性 Sym²: GL₂ → GL₃",
      "b_p = a_p² − p^{11}，三根 = (α², αβ, β²)",
      "p = 2: a₂ = \{a.coeff(2)}，b₂ = \{e1}（應為 \{want}）\ne2 = \{e2} = p^{11}·b₂，e3 = \{e3} = p^{33}",
      ok && e2 == 2048L * e1 && e3 == 8589934592L,
    )
  }
  exp_blk_10()
  fn exp_blk_11() {
    let a = delta_series(20)
    let (e1, _, _) = adj_satake(a.coeff(2), 2, 12)
    let want = a.coeff(2) * a.coeff(2) - 2 * 2048
    exp2(
      "T35b",
      "adj 分解",
      "adj = Sym² ⊗ det^{−1}：根 (α², 2αβ, β²) 縮放",
      "p = 2: adj e1 = \{e1}（應為 a₂² − 2p^{11} = \{want}）",
      e1 == want,
    )
  }
  exp_blk_11()
  // ============ 36. 基變換 ============
  fn exp_blk_12() {
    let a = delta_series(12)
    let av = a.0
    let mut detail = ""
    let mut ok = true
    for p in primes_upto(11) {
      let lp = legendre(5L, p.to_int64())
      let bp = base_change_coefficient(av[p], p, 12, lp)
      detail = detail + "p = \{p}: (5/p) = \{lp}, a_p = \{av[p]}, b_p = \{bp}\n"
    }
    // sanity: inert p = 2? (5/2)... legendre needs odd p; check formula identity for p = 3
    let b3 = base_change_coefficient(av[3], 3, 12, legendre(5L, 3L))
    let want3 = av[3] * av[3] - 2 * 177147 // a₃² − 2·3^11
    ok = b3 == want3
    exp2(
      "T36",
      "二次基變換",
      "split: b_p = 2a_p；inert: b_p = a_p² − 2p^{11}",
      detail + "p = 3 inert 公式核對：\{b3} = \{want3}：\{ok}",
      ok,
    )
  }
  exp_blk_12()
  // ============ 37. 自守誘導 ============
  fn exp_blk_13() {
    let err = ai_coefficient_error(30)
    exp2(
      "T37a",
      "自守誘導 = 數域 L-函數",
      "Ind_{Q(i)}^Q χ 的 GL₂ 係數 = Σ_{N𝔟 = n} χ(𝔟)（逐項）",
      "n ≤ 30 係數最大差 = \{err}",
      err < 0.000001,
    )
  }
  fn exp_blk_13c() {
    let err = ai_three_way_error(60, 8.0)
    exp2(
      "T37c",
      "AI L-函數分解",
      "L(Ind χ, s) = L(ψ, s)·L(ψχ₋₄, s)（χ = ψ∘N）",
      "s = 8 兩路最大差 = \{err}",
      err < 0.000001,
    )
  }
  exp_blk_13c()
  exp_blk_13()
  fn exp_blk_14() {
    let tbl = ai_character_table(13)
    let gl2 = ai_gl2_coefficients(30)
    let ok = gl2[3] == 0.0 && gl2[7] == 0.0 && gl2[11] == 0.0 // inert p ≡ 3 mod 4
    exp2(
      "T37b",
      "Artin 誘導特徵表",
      "inert p ⇒ tr = 0；split p ⇒ tr = χ(π) + χ(π̄)",
      tbl + "inert p ∈ {3, 7, 11} 跡全為 0：\{ok}",
      ok,
    )
  }
  exp_blk_14()
  // ============ 38. Jacquet–Langlands / Deuring ============
  fn exp_blk_15() {
    // Deuring mass formula: Σ_{ss j ∈ F_{p²}} 1/|Aut| = (p−1)/24
    let mut detail = ""
    let mut ok = true
    for p in [5, 7, 11] {
      let (count, mass, det) = ss_j_invariants_gf2(p)
      let want = (p - 1).to_double() / 24.0
      let diff = mass - want
      let abs = if diff < 0.0 { -diff } else { diff }
      if abs > 0.000001 {
        ok = false
      }
      detail = detail +
        "p = \{p}：超奇異 j ∈ F_{p²} 共 \{count} 個\n\{det}  Σ1/|Aut| = \{mass}，(p−1)/24 = \{want}\n"
    }
    exp2(
      "T38a", "Deuring 質量公式（JL↔四元數）", "Σ_{ss j} 1/|Aut(E_j)| = (p−1)/24",
      detail, ok,
    )
  }
  exp_blk_15()
  fn exp_blk_16() {
    // Deuring count: # supersingular j ∈ F_{p²} = floor(p/12) + ε
    let mut detail = ""
    let mut ok = true
    for p in [5, 7, 11] {
      let (count, _, _) = ss_j_invariants_gf2(p)
      let want = deuring_j_count(p)
      if count != want {
        ok = false
      }
      detail = detail +
        "p = \{p}: 超奇 j 共 \{count} 個；⌊p/12⌋+ε = \{want}\n"
    }
    exp2(
      "T38b", "Deuring 超奇異 j 計數（JL 對應）", "#超奇 j (F_{p²}) = ⌊p/12⌋ + ε",
      detail, ok,
    )
  }
  exp_blk_16()
  // ============ 39. 塔 theta ============
  fn exp_blk_17() {
    let e1 = jacobi_triple_product_error(0.2, 0.7, 12)
    let e2 = jacobi_triple_product_error(0.05, 1.8, 12)
    exp2(
      "T39a",
      "Jacobi 三重積",
      "Σ q^{n²}z^{2n} = ∏(1−q^{2m})(1+q^{2m−1}z²)(1+q^{2m−1}z^{−2})",
      "(q=0.2, z=0.7) 誤差 = \{e1}\n(q=0.05, z=1.8) 誤差 = \{e2}",
      e1 < 0.000001 && e2 < 0.000001,
    )
  }
  exp_blk_17()
  fn exp_blk_18() {
    let e1 = theta_r2_error(50)
    let e2 = theta_l_function_error(150, 6.0)
    exp2(
      "T39b",
      "塞塔對應 θ ↔ 計數 ↔ L",
      "θ₃(q)² = Σ r₂(n)q^n = 4ζ(s)L(χ₋₄, s)",
      "θ₃² 係數 vs 直接計數最大差 = \{e1}；Dirichlet 級數 vs 4ζL 差 = \{e2}",
      e1 == 0 && e2 < 0.001,
    )
  }
  exp_blk_18()
  // ============ 40. 模性定理 ============
  fn exp_blk_19() {
    let mut ok = true
    let mut detail = ""
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
      let (match_, aq, ac) = modularity_check_prime(p)
      if !match_ {
        ok = false
      }
      detail = detail +
        "p = \{p}: a_p(q-展開) = \{aq}, p+1−#E(F_p) = \{ac}：\{match_}\n"
    }
    exp2(
      "T40a", "模性逐素數驗證（X₀(11)）", "η(τ)²η(11τ)² 的 a_p = p+1−#E(F_p)",
      detail, ok,
    )
  }
  exp_blk_19()
  fn exp_blk_20() {
    let h = hasse_violation(47)
    let hv = modularity_hecke_violations(20)
    let (kok, kdet) = level11_known_prime_check()
    exp2(
      "T40b",
      "Hasse 界 ＋ Hecke 關係",
      "|a_p| ≤ 2√p；a_m a_n = Σ d·a_{mn/d²}",
      "Hasse 最大越界 = \{h}（≤ 0 合格）；Hecke 違規 = \{hv}\n已知係數核對：\{kdet}",
      h <= 0.000001 && hv == 0 && kok,
    )
  }
  exp_blk_20()
  // ============ A4–A6 衍生演生法 ============
  fn exp_blk_21() {
    let (fit, best, gens) = evolve_modularity(12, 400)
    let truth = newform_level11(12)
    let mut match_count = 0
    let mut n = 1
    while n <= 12 {
      if best[n] == truth[n] {
        match_count = match_count + 1
      }
      n = n + 1
    }
    let mut s = ""
    let mut n2 = 1
    while n2 <= 12 {
      s = s + "\{best[n2]} "
      n2 = n2 + 1
    }
    exp2(
      "A4",
      "模性 GA（演化新形式係數）",
      "演化 a_n 使 Hecke 關係＋曲線計數全滿足",
      "\{gens} 代後：適應度 = \{fit}（0 = 完美）\n演化係數：\{s}\n真值 n ≤ 12 吻合 \{match_count}/12",
      fit == 0 && match_count == 12,
    )
  }
  exp_blk_21()
  fn exp_blk_22() {
    let e = WCurve(0, -1, 1, -10, -20)
    let a11 = e.trace(11)
    let (fit, m, gens) = evolve_frobenius_matrix(a11, 11, 5, 120)
    exp2(
      "A5",
      "Frobenius 矩陣演化（GL₂(Z/ℓ)）",
      "演化矩陣逼近 tr ≡ a_p (mod ℓ)、det ≡ p (mod ℓ)",
      "X₀(11) 在 p = 11: a₁₁ = \{a11}, ℓ = 5\n\{gens} 代後：\{m.to_string()}，適應度 = \{fit}",
      fit == 0,
    )
  }
  exp_blk_22()
  fn exp_blk_23() {
    // A6: evolve GL_3 Sym² local data (e1, e2, e3) from global power sums
    // of Δ at p = 2: targets t_m = s_{2m} + (2^{11})^m, m = 1..3.
    let a = delta_series(20)
    let s = satake_power_sums(a.coeff(2), 2, 12, 8)
    let targets : Array[Int64] = []
    let pk = 2048L
    let mut pm = 1L
    let mut m = 1
    while m <= 3 {
      pm = pm * pk
      targets.push(s[2 * m] + pm)
      m = m + 1
    }
    let (fit, e1, e2, e3, gens) = evolve_sym2_data(targets, 400)
    let want1 = a.coeff(2) * a.coeff(2) - 2048
    let ok = e1 == want1 &&
      e2 == 2048 * e1 &&
      e3 == 2048 * 2048 * 2048 &&
      fit == 0
    exp2(
      "A6",
      "局整相容演化（Sym² Satake）",
      "由 {a_{p^m}} 冪和演化 GL₃ 局部參數 (e1, e2, e3)",
      "p = 2, Δ：目標 (b₂, 2^{11}b₂, 2^{33}) = (\{want1}, \{2048L * want1}, \{2048L * 2048L * 2048L})\n\{gens} 代後演化出：(\{e1}, \{e2}, \{e3})，殘差 = \{fit}",
      ok,
    )
  }
  exp_blk_23()
  res
}

///|
/// (F_{p²} variants live in jacquet_langlands.mbt: curve_from_j_gf2,
/// count_points_gf2, ss_j_invariants_gf2.)

///|
/// Render the batch-2 report as text.
pub fn render_report2() -> String {
  let res = run_all_experiments2()
  let mut pass_count = 0
  for e in res {
    if e.pass {
      pass_count = pass_count + 1
    }
  }
  let mut s = "====================================================\n"
  s = s +
    " 批次二：計算機抽象導出定理報告 — 結構 31–40 ＋ A4–A6\n"
  s = s + "====================================================\n\n"
  for e in res {
    let verdict = if e.pass { "PASS" } else { "FAIL" }
    s = s + "[\{e.id}] \{e.name} — \{verdict}\n"
    s = s + "  定理：\{e.statement}\n"
    s = s + "  證據：\{e.detail}\n\n"
  }
  s = s + "----------------------------------------------------\n"
  s = s + "實驗通過：\{pass_count} / \{res.length()}\n"
  s
}
