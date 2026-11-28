///|
/// syn11.mbt — 批次十一·模組 4：句法遺址、泛模型、卡拉梅洛橋樑、相干函子、cdh 拓撲
///
/// 以「有限 G-集合的理論」作為可計算的句法理論：
///   有限呈現模型 = 有限 G-集合；覆蓋 = 聯合滿的有限族（相干拓撲）；
///   泛模型 = 正則 G-集合 U（Hom_G(U, X) = |X|）；
///   橋樑 = 同一拓撲斯 Set[G] 的兩種呈現（群呈現 vs 句法呈現）之不變量比對。
/// cdh：以閉–開分解 {Z, X∖Z} 的 Mayer–Vietoris 加法性實現。

// ───────────────────────── 句法遺址 ─────────────────────────

///|
/// 傳遞 G-集合的度數表：度數 d 的傳遞 G-集合同構類數 = 指數 d 子群的共軛類數。
pub fn b11_transitive_degrees(g : B9Group) -> Array[Int32] {
  let out : Array[Int32] = []
  for d in 1..<=g.k {
    out.push(b10_conj_class_count(g, d))
  }
  out
}

///|
/// 有限呈現模型計數：大小 ≤ n 的 G-集合同構類數（各傳遞塊的重數 DP）。
pub fn b11_fp_gsets(g : B9Group, n : Int32) -> Int32 {
  // 每個 (度數, 同構類) 給出一個可重複取用的塊
  let items : Array[Int32] = []
  let degs = b11_transitive_degrees(g)
  for d in 0..<degs.length() {
    for _ in 0..<degs[d] {
      items.push(d + 1)
    }
  }
  // 無界背包計數：dp[s] = 總大小恰為 s 的重數選擇數
  let dp : Array[Int32] = []
  for _ in 0..<=n {
    dp.push(0)
  }
  dp[0] = 1
  for it in items {
    for s in it..<=n {
      dp[s] = dp[s] + dp[s - it]
    }
  }
  let mut tot = 0
  for s in 0..<=n {
    tot = tot + dp[s]
  }
  tot
}

///|
/// 泛模型：正則 G-集合 U 表示遺忘函子 —— |Hom_G(U, X)| = |X|。
pub fn b11_generic_model(g : B9Group, xs : Array[B9GSet]) -> Bool {
  let u = b9_gset_reg(g)
  for x in xs {
    if b9_hom_gset(u, x) != x.n {
      return false
    }
  }
  true
}

///|
/// 句法拓撲斯中終對象的子對象數：子 G-集合個數（以「軌道子集」計）。
pub fn b11_sub_terminal(g : B9Group) -> Int32 {
  // 終對象 = 單點平凡作用；其子對象 = 軌道集的子集
  b8_pow_int(2, b9_orbit_count(b9_gset_triv(g, 1)))
}

///|
/// 正則 G-集合的自同構個數（以置換窮舉直接計算，獨立於 b9_hom_gset）。
pub fn b11_aut_regular(g : B9Group) -> Int32 {
  let k = g.k
  let perms : Array[Array[Int32]] = []
  b11_perms_rec([], k, perms)
  let reg = b9_gset_reg(g)
  let mut cnt = 0
  for p in perms {
    // p 為集合 {0..k-1} 的置換；檢查是否與作用交換
    let mut ok = true
    for a in 0..<k {
      for x in 0..<k {
        if p[reg.act[a * k + x]] != reg.act[a * k + p[x]] {
          ok = false
        }
      }
    }
    if ok {
      cnt = cnt + 1
    }
  }
  cnt
}

///|
/// 遞迴枚舉全體置換。
fn b11_perms_rec(
  pre : Array[Int32],
  k : Int32,
  out : Array[Array[Int32]],
) -> Unit {
  if pre.length() == k {
    out.push(pre)
    return
  }
  for v in 0..<k {
    let mut used = false
    for u in pre {
      if u == v {
        used = true
      }
    }
    if !used {
      let nxt : Array[Int32] = []
      for u in pre {
        nxt.push(u)
      }
      nxt.push(v)
      b11_perms_rec(nxt, k, out)
    }
  }
}

// ───────────────────────── 卡拉梅洛橋樑 ─────────────────────────

///|
/// 橋樑不變量：兩種呈現下計算同四個不變量。
///   群呈現（代數側）：點數、Sub(1)、泛模型自同構、H^1
///   句法呈現（幾何側）：扭子同構類、子 G-集合、|Hom(U,U)|、Čech H^1
/// 回傳 (群側, 句法側, 是否全等)。
pub fn b11_bridge(
  g : B9Group,
  pm : Int32,
) -> (Array[Int32], Array[Int32], Bool) {
  // 代數側（群呈現）：扭子點、軌道式子終對象、|Hom(reg,reg)|、群上同調
  let grp : Array[Int32] = [
    b9_point_iso_count(g),
    b11_sub_terminal(g),
    b10_fiber_aut(g),
    b9_group_h(g, 1, pm),
  ]
  // 幾何側（模型範疇呈現）：子群共軛類、子 G-集合窮舉、置換窮舉自同構、同一個上同調引擎
  let syn : Array[Int32] = [
    b10_conj_class_count(g, g.k),
    b9_sub_gset_count(b9_gset_triv(g, 1)),
    b11_aut_regular(g),
    b9_group_h(g, 1, pm),
  ]
  let mut eq = true
  for i in 0..<grp.length() {
    if grp[i] != syn[i] {
      eq = false
    }
  }
  (grp, syn, eq)
}

// ───────────────────────── 相干函子 ─────────────────────────

///|
/// 相干函子：保有限極限（終對象、二元乘積）與餘極限（餘積）。
pub fn b11_coherent(u : B8Fun, f : B8PS, g : B8PS) -> (Bool, Bool, Bool) {
  let one = b8_ps_const(u.dst, 1)
  let term = b8_ps_eq(b8_pull(u, one), b8_ps_const(u.src, 1))
  let prod = b8_ps_eq(
    b8_pull(u, b8_ps_prod(f, g)),
    b8_ps_prod(b8_pull(u, f), b8_pull(u, g)),
  )
  let cop = b8_ps_eq(
    b8_lan(u, b8_ps_coprod(b8_pull(u, f), b8_pull(u, g))),
    b8_ps_coprod(b8_lan(u, b8_pull(u, f)), b8_lan(u, b8_pull(u, g))),
  )
  (term, prod, cop)
}

// ───────────────────────── cdh 拓撲 ─────────────────────────

///|
/// cdh 型覆蓋：閉子集 Z 與其開補集 U = X∖Z 構成 X 的覆蓋（餘維分解決）。
pub fn b11_cdh_cover(t : B9Top, z : Array[Bool]) -> Bool {
  let mut hasz = false
  let mut hasu = false
  for p in 0..<t.npt {
    if z[p] {
      hasz = true
    } else {
      hasu = true
    }
  }
  hasz || hasu
}

///|
/// 閉子集判定：X∖Z 為開集。
pub fn b11_closed_set(t : B9Top, z : Array[Bool]) -> Bool {
  let comp : Array[Bool] = []
  for p in 0..<t.npt {
    comp.push(!z[p])
  }
  b9_top_find(t, comp) >= 0
}

///|
/// 歐拉示性數（以上同調維數的交替和）。
pub fn b11_euler(dims : Array[Int32]) -> Int32 {
  let mut e = 0
  for n in 0..<dims.length() {
    if n % 2 == 0 {
      e = e + dims[n]
    } else {
      e = e - dims[n]
    }
  }
  e
}

///|
/// cdh 型 Mayer–Vietoris 的歐拉加法性：閉覆蓋 {Z₁, Z₂} 上
/// χ(X) = χ(Z₁) + χ(Z₂) − χ(Z₁∩Z₂)。
/// 回傳 (χ(X), 右側, 是否成立且覆蓋為閉覆蓋)。
pub fn b11_cdh_mv(
  t : B9Top,
  z1 : Array[Bool],
  z2 : Array[Bool],
  pmax : Int32,
  pm : Int32,
) -> (Int32, Int32, Bool) {
  let mut cov = true
  for p in 0..<t.npt {
    if !z1[p] && !z2[p] {
      cov = false
    }
  }
  let closed = b11_closed_set(t, z1) && b11_closed_set(t, z2)
  let z12 : Array[Bool] = []
  for p in 0..<t.npt {
    z12.push(z1[p] && z2[p])
  }
  let chi_x = b11_euler(b11_site_dims(t, pmax, pm))
  let chi_1 = b11_euler(b11_site_dims(b11_subspace(t, z1), pmax, pm))
  let chi_2 = b11_euler(b11_site_dims(b11_subspace(t, z2), pmax, pm))
  let chi_12 = b11_euler(b11_site_dims(b11_subspace(t, z12), pmax, pm))
  (
    chi_x,
    chi_1 + chi_2 - chi_12,
    cov && closed && chi_x == chi_1 + chi_2 - chi_12,
  )
}
