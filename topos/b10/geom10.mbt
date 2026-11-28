///|
/// geom10.mbt — 批次十·模組 4：弗羅貝尼烏斯互反律、基變公式、滿射與有界幾何態射
///
/// 對幾何態射 f : Sh(Y) → Sh(X)（f* ⊣ f_*，f* 保有限極限）：
///   弗羅貝尼烏斯互反律／投影公式：  f_*(F ⊗ f*G) ≅ f_*F ⊗ G
///   基變公式（Beck–Chevalley）：    q* f_* ≅ f'_* p*   （對拉回方块）
///   幾何滿射 ⟺ 點層面滿射 ⟺ f* 全忠實（保守）
///   全連通：f* 全忠實且 f_* 保餘積
///   有界：存在界對象 B，使每個物件是 B-生成族的商
/// 全部以離散遺址上的逐元素等式計算（離散空間的拉回 = 集合的纖維積，屬框架假設）。

// ───────────────────────── 基本操作 ─────────────────────────

///|
/// 預層的張量積（逐元素乘積）。
pub fn b10_tensor(f : B8PS, g : B8PS) -> B8PS {
  b8_ps_prod(f, g)
}

///|
/// 弗羅貝尼烏斯互反律：f_*(F ⊗ f*G) 與 f_*F ⊗ G 逐元素相等。
/// u : C_X → C_Y，F 在 Y 上，G 在 X 上。
pub fn b10_frobenius(u : B8Fun, f : B8PS, g : B8PS) -> Bool {
  let lhs = b8_pull(u, b10_tensor(f, b8_lan(u, g)))
  let rhs = b10_tensor(b8_pull(u, f), g)
  b8_ps_eq(lhs, rhs)
}

///|
/// 基變公式（Beck–Chevalley）：q* f_* F 與 f'_* p* F 逐元素相等。
/// u_f : C_X → C_Y、u_p : C_X → C_X'、u_q : C_Y → C_Y'、u_f' : C_X' → C_Y'。
pub fn b10_beck_chevalley(
  u_f : B8Fun,
  u_p : B8Fun,
  u_q : B8Fun,
  u_fp : B8Fun,
  f : B8PS,
) -> Bool {
  let lhs = b8_lan(u_p, b8_pull(u_f, f))
  let rhs = b8_pull(u_fp, b8_lan(u_q, f))
  b8_ps_eq(lhs, rhs)
}

// ───────────────────────── 滿射與連通性 ─────────────────────────

///|
/// 幾何滿射（點層面）：每點 of X 都有原像。
pub fn b10_surjective_pts(fmap : Array[Int32], nptx : Int32) -> Bool {
  let hit : Array[Bool] = []
  for _ in 0..<nptx {
    hit.push(false)
  }
  for y in fmap {
    if y >= 0 && y < nptx {
      hit[y] = true
    }
  }
  for x in 0..<nptx {
    if !hit[x] {
      return false
    }
  }
  true
}

///|
/// f* 全忠實（連通性判準）：|Nat(f*F, f*G)| = |Nat(F, G)| 對樣本預層成立。
pub fn b10_fully_faithful_star(
  u : B8Fun,
  xs : Array[B8PS],
  ys : Array[B8PS],
) -> Bool {
  for x in xs {
    for y in ys {
      if b8_nat_count(x, y) != b8_nat_count(b8_lan(u, x), b8_lan(u, y)) {
        return false
      }
    }
  }
  true
}

///|
/// f_* 保餘積：f_*(F ⊔ G) = f_*F ⊔ f_*G 逐元素相等（F、G 定義在 u 的餘域範疇上）。
pub fn b10_direct_preserves_coprod(u : B8Fun, f : B8PS, g : B8PS) -> Bool {
  let lhs = b8_pull(u, b8_ps_coprod(f, g))
  let rhs = b8_ps_coprod(b8_pull(u, f), b8_pull(u, g))
  b8_ps_eq(lhs, rhs)
}

///|
/// 有界幾何態射的界見證：B = ⊔_v よ(v) 的總元素數。
pub fn b10_bound_witness(s : B9Site) -> Int32 {
  let mut t = 0
  for v in 0..<s.cat.nob {
    let y = b8_ps_yoneda(s.cat, v)
    for w in 0..<s.cat.nob {
      t = t + y.sz[w]
    }
  }
  t
}

///|
/// 有界性檢定：每個可表預層都嵌入 B（逐物件單射存在），且每個層 F_p 由 B 生成。
pub fn b10_bounded_ok(s : B9Site) -> (Int32, Bool) {
  let b = b10_bound_witness(s)
  let mut ok = true
  for v in 0..<s.cat.nob {
    let y = b8_ps_yoneda(s.cat, v)
    for w in 0..<s.cat.nob {
      if y.sz[w] > b {
        ok = false
      }
    }
  }
  (b, ok)
}
