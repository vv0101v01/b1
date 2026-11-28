///|
/// Batch 5 experiment report: T181–T190 + A13–A15.

///|
fn fmt_a13() -> String {
  let (ix, iy, ix2, ixy, iy2) = evolve_noncomm_diagram()
  "  演化弦圖 f: x ↦ " +
  b_sh_arr_i32(ix) +
  ", y ↦ " +
  b_sh_arr_i32(iy) +
  "，f(x²)=" +
  b_sh_arr_i32(ix2) +
  "，f(xy)=" +
  b_sh_arr_i32(ixy) +
  "，f(y²)=" +
  b_sh_arr_i32(iy2) +
  "，fitness = " +
  a13_fitness(ix, iy, ix2, ixy, iy2).to_string() +
  "\n"
}

///|
fn fmt_a15() -> String {
  let lam = evolve_wavefront()
  "  演化頻率序列 λ = " +
  b_sh_arr_i32(lam) +
  "，WF = {−1, +1}，fitness = " +
  a15_fitness(lam).to_string() +
  "\n"
}

///|
pub fn report5() -> String {
  let mut s = "批次五實驗報告 (181–190)\n"
  s = s + "========================\n\n"

  // ---------- T181 ----------
  let k = markov_precision()
  s = s +
    "── T181 弦圖高斯馬可夫 ⇒ 八元數公理 ────────────\n"
  s = s +
    fmt_b("高斯馬可夫消沒：K 於非邊 (0,3) 為 0", markov_vanishes(k))
  s = s +
    fmt_b(
      "二次型黏合：xᵀKx = q_{C1} + q_{C2} − q_S（81 樣本）",
      markov_gluing_ok(k),
    )
  s = s +
    fmt_b(
      "伴隨恆等式：K·adj(K) = det(K)·I（精確整數）",
      adj_identity_ok(k),
    )
  s = s +
    fmt_b("弦圖交換律：(F⊗G)(H⊗K) = (FH)⊗(GK)", interchange_ok())
  s = s +
    fmt_b(
      "Cayley–Dickson 八元數交替律（基底全檢）",
      octonion_alternative_ok(),
    )
  s = s +
    fmt_b(
      "範數乘法 |xy|² = |x|²|y|²（基底組合）",
      octonion_norm_mult_ok(),
    )
  s = s +
    fmt_b(
      "蘊含鏈：4 維馬可夫 + 交換律 ⇒ 8 維八元數公理",
      markov_implies_octonion_ok(),
    )

  // ---------- T182 ----------
  s = s +
    "\n── T182 非交換弦圖與完美樹譜序列 ────────────\n"
  s = s +
    fmt_b(
      "非交換弦圖交換律（字代換恆等式）",
      nc_interchange_ok(),
    )
  s = s +
    fmt_b(
      "完美樹譜頁面：χ(E⁰) = χ(E^∞) = 1（深度 3）",
      tree_spectral_pages_ok(3),
    )
  s = s +
    fmt_b(
      "過濾對長正合序列 0→1→2→1→0 全正合（F₇ 秩計算）",
      tree_les_exact_ok(),
    )

  // ---------- T183 ----------
  s = s +
    "\n── T183 解空間不動點與樹弦齊次同調 ────────────\n"
  s = s +
    fmt_b(
      "2×2 冪等子解空間：#{E²=E} = 14 = 1+1+q(q+1)",
      idempotent_count_ok(),
    )
  s = s +
    fmt_b(
      "Burnside：轉置作用軌道數 = (Fix(id)+Fix(τ))/2（顯式軌道）",
      burnside_idempotents_ok(),
    )
  s = s +
    fmt_b(
      "樹弦同調：弦封閉恰一圈 b = (1,1)",
      tree_string_homology_ok(),
    )
  s = s +
    fmt_b(
      "對合不變量：H₁^G = 1（Maschke 平均，char F₇ ∤ 2）",
      involution_invariants_ok(),
    )

  // ---------- T184 ----------
  s = s +
    "\n── T184 深分歧超尖點表示 ────────────────────\n"
  s = s +
    fmt_b(
      "導子分佈 (Z/25)^*：c = (0,1,2) → (1,3,16)；深 = 16",
      deep_conductor_ok(),
    )
  s = s +
    fmt_b(
      "Galois 非不變 → 超尖點軌道 10 = (q²−q)/2（q = 5）",
      supercuspidal_orbits_ok(),
    )
  s = s +
    fmt_b(
      "不可約判準：ψ ≠ ψ^q ⟺ 誘導不可約（24 全檢）",
      supercuspidal_irred_ok(),
    )
  s = s +
    fmt_b(
      "深 ⟺ 於 U¹ 非平凡（χ_m(6) ≠ 1 ⟺ 5 ∤ m）",
      deep_via_unit_ok(),
    )

  // ---------- T185 ----------
  s = s +
    "\n── T185 表示的深度 ────────────────────────\n"
  s = s +
    fmt_b(
      "過濾階數 (100, 25, 5, 1)＋導子分佈 (1,3,16,80)",
      depth_filtration_ok(),
    )
  s = s +
    fmt_b(
      "深度次可加：depth(χψ) ≤ max（100×100 全檢）",
      depth_subadditive_ok(),
    )
  s = s +
    fmt_b(
      "分歧點 ∈ (1/e)Z（e = 1）；正則表示最大深度 2",
      depth_breakpoints_ok(),
    )
  s = s + fmt_b("過濾乘法 U^a·U^b = U^{min(a,b)}", filtration_mult_ok())

  // ---------- T186 ----------
  s = s +
    "\n── T186 俞氏構造 ──────────────────────────\n"
  s = s +
    fmt_b(
      "薛丁格同態：ψ-exp 交叉恆等式（125²×5 全格點）",
      schrodinger_homomorphism_ok(),
    )
  s = s +
    fmt_b(
      "Stone–von Neumann：(χ,χ) = 1、dim² = |U|/|Z| = 25",
      heisenberg_irreducible_ok(),
    )
  s = s +
    fmt_b(
      "環面作用自同構＋中心特徵軌道 {ψ₁,ψ₄}、|stab| = 2",
      yu_torus_ok(),
    )

  // ---------- T187 ----------
  s = s +
    "\n── T187 卡萊塔局部朗蘭茲構造 ──────────────────\n"
  s = s +
    fmt_b(
      "雙演算法字元恆等式：誘導和 = Chebyshev 遞推（全旋轉）",
      char_identity_ok(),
    )
  s = s +
    fmt_b(
      "不可約判準：(Ind,Ind) = 1 ⟺ χ ≠ χ^s（m ∉ {0,3}）",
      dihedral_irred_ok(),
    )
  s = s +
    fmt_b(
      "正則半單匹配：軌道 {1,5},{2,4} ↔ 2 個二維參數",
      regular_matching_ok(),
    )
  s = s +
    fmt_b(
      "轉移因子 Δ = 1：匹配穩定（指數運算恆等式）",
      transfer_factor_ok(),
    )

  // ---------- T188 ----------
  s = s +
    "\n── T188 半單與非半單朗蘭茲參數 ──────────────────\n"
  s = s +
    fmt_b(
      "N² = 0 分類：625 窮舉 = 25（1 零 + 24 秩一）",
      nilpotent_class_ok(),
    )
  s = s +
    fmt_b(
      "Weil–Deligne 關係 FN = qNF（q = 5 整數矩陣）",
      weil_deligne_ok(),
    )
  s = s +
    fmt_b(
      "單值檢測器：[F,N] = 0 ⟺ N = 0（similitude F）",
      monodromy_detector_ok(),
    )
  s = s +
    fmt_b(
      "Springer 玩具：E₁₂ 軌道 24 = 全秩一冪零 ⇔ S₂ 二不可約",
      springer_classes_ok(),
    )
  s = s +
    fmt_b(
      "半單化保 (tr, det)（特徵多項式不變）",
      semisimplification_ok(),
    )

  // ---------- T189 ----------
  s = s +
    "\n── T189 溫和函子性與普朗歇爾轉 ──────────────────\n"
  s = s +
    fmt_b(
      "普朗歇爾恆等式 |G|Σf² = Σf̂²（4 組測試精確）",
      plancherel_ok(),
    )
  s = s +
    fmt_b(
      "卷積定理：(f∗g)̂ = f̂·ĝ（逐點）",
      convolution_theorem_ok(),
    )
  s = s +
    fmt_b("Fourier 反演：f = (1/|G|)Σf̂χ（精確）", inversion_ok())
  s = s +
    fmt_b(
      "溫和函子性：膨脹譜支撐 ⊂ π-因子化特徵＋質量 ×2＋緩增界",
      mild_functorial_ok(),
    )

  // ---------- T190 ----------
  s = s +
    "\n── T190 波前集 ────────────────────────────\n"
  s = s +
    fmt_b(
      "範例：{n²}→{+1}、{(−1)ⁿn²}→{±1}、有界→∅",
      wf_examples_ok(),
    )
  s = s +
    fmt_b(
      "和規則：WF(u+v) ⊆ WF(u)∪WF(v)（顯式集合）",
      wf_union_ok(),
    )
  s = s +
    fmt_b(
      "積規則：supp(u·v) ⊆ supp(u)+supp(v)（Minkowski）",
      wf_product_ok(),
    )
  s = s +
    fmt_b(
      "圖規則：WF(e^iφ) = graph(φ′)；δ₀ 全方向",
      wf_graph_rule_ok(),
    )

  // ---------- A13 ----------
  s = s +
    "\n── A13 非交換弦圖演化 ─────────────────────\n"
  s = s + fmt_a13()
  s = s +
    fmt_b(
      "演化收斂至同態弦圖（代換一致 = 交換律解）",
      a13_converges_ok(),
    )

  // ---------- A14 ----------
  s = s +
    "\n── A14 深超尖點表示演化 ─────────────────────\n"
  let m14 = evolve_deep_rep()
  s = s +
    "  演化表示基因 m = " +
    m14.to_string() +
    "（cond25 = 2 深、ψ^5 ≠ ψ 非 Galois 不變），fitness = 0\n"
  s = s + fmt_b("演化收斂至深超尖點資料", a14_converges_ok())

  // ---------- A15 ----------
  s = s +
    "\n── A15 波前集演化 ────────────────────────\n"
  s = s + fmt_a15()
  s = s +
    fmt_b(
      "演化收斂至 WF = {−1, +1}（雙向無界頻譜）",
      a15_converges_ok(),
    )

  s = s + "\n"
  s
}
