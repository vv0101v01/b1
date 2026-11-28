///|
/// classify9.mbt — 批次九·模組 10：分類拓撲斯（G-扭子的分類拓撲斯）
///
/// 理論：有限群 G 的扭子（free + transitive 的 G-集合，非空）的分類拓撲斯
/// 是 Set[G] = PSh(BG) = G-Set。萬有扭子 U = G（左正則作用），
/// 且 U 表示遺忘函子：Hom_{Set[G]}(U, X) ≅ |X|。
/// 點：幾何態射 Set → Set[G] 的同構類 = 扭子的同構類 = 1（對有限群），
/// 而其自同構群 = Aut_{Set[G]}(U) = G（故 π₁(Set[G]) = G）。
/// 子對象分類子：G 有限群時 Ω = 兩點平凡集，且 |Sub(X)| = 2^{|X/G|}。
///
/// 全部以整數／布林值精確核對；無浮點。

// ───────────────────────── 萬有扭子 ─────────────────────────

///|
/// 萬有扭子：左正則作用 U = G。
pub fn b9_univ_torsor(g : B9Group) -> B9GSet {
  b9_gset_reg(g)
}

///|
/// 扭子框架：回傳 (自由度, 傳遞性)，即 (所有穩定子 = 1, 軌道數 = 1)。
pub fn b9_torsor_frame(s : B9GSet) -> (Bool, Bool) {
  let mut free = true
  for x in 0..<s.n {
    if b9_stab_size(s, x) != 1 {
      free = false
    }
  }
  (free, b9_orbit_count(s) == 1)
}

///|
/// 表示性：|Hom_{Set[G]}(U, X)| 應等於 |X|（元素數）。
pub fn b9_represent(s : B9GSet) -> (Int32, Int32) {
  (b9_hom_gset(b9_univ_torsor(s.grp), s), s.n)
}

// ───────────────────────── 子對象分類子 ─────────────────────────

///|
/// 子 G-集合的個數（枚舉所有子集並檢查 G-穩定性）。
pub fn b9_sub_gset_count(s : B9GSet) -> Int32 {
  if s.n > 12 {
    return -1
  }
  let mut cnt = 0
  for mask in 0..<b8_pow_int(2, s.n) {
    let mut ok = true
    for gi in 0..<s.grp.k {
      for x in 0..<s.n {
        let bx = (mask >> x) & 1
        let by = (mask >> s.act[gi * s.n + x]) & 1
        if bx != by {
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
/// 分類子：回傳 (|Sub(X)|, 2^軌道數) 供比對；Ω 自身為兩點平凡集。
pub fn b9_classifier(s : B9GSet) -> (Int32, Int32) {
  (b9_sub_gset_count(s), b8_pow_int(2, b9_orbit_count(s)))
}

///|
/// Ω 的大小與 |Nat(1, Ω)|：對有限群皆為 2。
pub fn b9_omega_gset(g : B9Group) -> (Int32, Int32) {
  let one = b9_gset_triv(g, 1)
  let omega = b9_gset_triv(g, 2)
  (b9_sub_gset_count(one), b9_hom_gset(one, omega))
}

// ───────────────────────── 點與分類性質 ─────────────────────────

///|
/// 扭子**作用**的個數（在 |G| 點集上）＝ (|G| − 1)!（結構性）。
pub fn b9_torsor_action_count(g : B9Group) -> Int32 {
  b9_torsor_count(g)
}

///|
/// 點的個數（同構類）：兩扭子模型間有 |G| > 0 個同構 ⟹ 恰一個同構類。
pub fn b9_point_iso_count(g : B9Group) -> Int32 {
  let m = b9_hom_gset(b9_univ_torsor(g), b9_univ_torsor2(g))
  if g.k > 0 && m == g.k {
    1
  } else {
    0
  }
}

///|
/// 兩個扭子之間的同構數：任意兩扭子 T, T' 有 |G| 個同構（扭子範疇為單點群胚）。
pub fn b9_torsor_iso_count(g : B9Group) -> Int32 {
  b9_hom_gset(b9_univ_torsor(g), b9_univ_torsor(g))
}

///|
/// 第二個扭子模型：右正則作用 x ↦ x·a⁻¹（與左正則同構但不相同）。
pub fn b9_univ_torsor2(g : B9Group) -> B9GSet {
  let act : Array[Int32] = []
  for a in 0..<g.k {
    let mut inv = 0
    for h in 0..<g.k {
      if g.mul[a * g.k + h] == 0 {
        inv = h
      }
    }
    for x in 0..<g.k {
      act.push(g.mul[x * g.k + inv])
    }
  }
  { grp: g, n: g.k, act, }
}

///|
/// 分類性質：對每個 G-集合 X，扭子 T 上的「X-值點」 = Hom_{Set[G]}(T, X)。
/// 扭子範疇等價於單點類別 ⟹ 其上的 X-值點數與 T 無關。
pub fn b9_classify_check(g : B9Group, x : B9GSet) -> (Int32, Int32) {
  (b9_hom_gset(b9_univ_torsor(g), x), b9_hom_gset(b9_univ_torsor2(g), x))
}

///|
/// 萬有扭子的自同構群大小 = |G|（= π₁(Set[G])）。
pub fn b9_aut_univ(g : B9Group) -> Int32 {
  b9_torsor_aut(g)
}
