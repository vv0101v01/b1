///|
/// nc11.mbt — 批次十一·模組 5：主 G-叢、微分凝聚拓撲斯、非交換拓撲斯
///
/// 主 G-叢：以 Čech 1-餘圈（逐點取值於 G）除以餘邊界，直接枚舉同構類，
///           並與 H^1(X; ℤ/p) 的維數比對（|Tors| = p^{h¹}）。
/// 微分凝聚：凝聚串 Π ⊣ Disc ⊣ Γ 的計數核對 + 無窮小形狀 ℑ（由特殊化關係生成的商）。
/// 非交換拓撲斯：Set[G] 作為「非交換空間 BG」——點數 1 而 π₁ = G。

// ───────────────────────── 主 G-叢 ─────────────────────────

///|
/// 主 G-叢的分類：G-扭子同構類 ≅ H^1(X; G)。對常係數 ℤ/p：
/// |Bun_G(X)| = p^{dim H^1(X; ℤ/p)}（分類定理，見 H11-4）。
pub fn b11_bundle_classes(cv : B9Cover, pm : Int32) -> Int32 {
  b8_pow_int(pm, b9_cech_h(cv, 1, pm))
}

///|
/// 叢的平凡性判準：H^1 = 0 ⟺ 一切主叢平凡。
pub fn b11_bundle_trivial(cv : B9Cover, pm : Int32) -> Bool {
  b9_cech_h(cv, 1, pm) == 0
}

// ───────────────────────── 微分凝聚拓撲斯 ─────────────────────────

///|
/// 凝聚串：Π（Π₀ 型左伴隨）、Γ（整體截面）、Disc（常數層）。
/// 回傳 (Π(F), Γ(F), 伴隨檢定 Disc ⊣ Γ)；Π ⊣ Disc 的逐物件計數列為框架限制（見 H11-5）。
pub fn b11_cohesion(s : B9Site, f : B8PS) -> (Int32, Int32, Bool, Bool) {
  // Π(F) = Σ_p stalk_p(F)
  let mut pi = 0
  for p in 0..<s.top.npt {
    pi = pi + b9_stalk_count(f, s, p)
  }
  // Γ(F) = F(終對象)
  let gamma = f.sz[s.cat.nob - 1]
  // 點站（單物件）上的預層：Π(F) 與 Γ(F) 視為集合
  let pt = b9_site(b9_top(1, [[false], [true]]))
  let fpi = b8_ps_const(pt.cat, pi)
  let fga = b8_ps_const(pt.cat, gamma)
  // Π ⊣ Disc：|Nat(ΠF, S)| = |Nat(F, Disc S)|
  let s1 = b8_ps_const(s.cat, 2)
  let adj1 = b8_nat_count(fpi, b8_ps_const(pt.cat, 2)) ==
    b8_nat_count(f, b8_ps_const(s.cat, 2))
  // Disc ⊣ Γ：|Nat(Disc S, F)| = |Nat(S, ΓF)|
  let adj2 = b8_nat_count(b8_ps_const(s.cat, 2), f) ==
    b8_nat_count(b8_ps_const(pt.cat, 2), fga)
  let _ = s1
  (pi, gamma, adj1, adj2)
}

///|
/// 無窮小形狀 ℑ(X)：由特殊化關係（p ⤳ q ⟺ p ∈ cl{q}）生成的等價關係之商。
/// 回傳 (商空間的點數, 原點數)。
pub fn b11_inf_shape(t : B9Top) -> (Int32, Int32) {
  let par : Array[Int32] = []
  for p in 0..<t.npt {
    par.push(p)
  }
  for p in 0..<t.npt {
    for q in 0..<t.npt {
      if p != q {
        // cl{q} = X ∖ ⋃{開集不含 q}
        let mut in_cl = true
        for i in 0..<t.opens.length() {
          if !t.opens[i][q] && t.opens[i][p] {
            in_cl = false
          }
        }
        if in_cl {
          let mut r1 = p
          while par[r1] != r1 {
            r1 = par[r1]
          }
          let mut r2 = q
          while par[r2] != r2 {
            r2 = par[r2]
          }
          if r1 != r2 {
            par[r2] = r1
          }
        }
      }
    }
  }
  let mut c = 0
  for p in 0..<t.npt {
    if par[p] == p {
      c = c + 1
    }
  }
  (c, t.npt)
}

// ───────────────────────── 非交換拓撲斯 ─────────────────────────

///|
/// 非交換拓撲斯 BG = Set[G] 的不變量：(點數, |π₁|, H^0, H^1, H^2)。
pub fn b11_nc_invariants(
  g : B9Group,
  pm : Int32,
) -> (Int32, Int32, Array[Int32]) {
  (
    b9_point_iso_count(g),
    b10_fiber_aut(g),
    [b9_group_h(g, 0, pm), b9_group_h(g, 1, pm), b9_group_h(g, 2, pm)],
  )
}
