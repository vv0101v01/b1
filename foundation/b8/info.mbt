///|
/// info.mbt — 批次八·模組 9：總相關性、互資訊張量、自洽方程、多模態資訊瓶頸
///
/// 以位元（log₂）計算所有資訊量，並以**精確有理分佈**（機率為 1/16 的整數倍）做獨立性判定；
/// 連續部分（IB 自洽方程）以定點迭代求解並報告殘差。
///
/// 可計算的內容：
///   1. 熵 H、聯合熵、互資訊 I(X;Y)、總相關性 TC = ΣH(X_i) − H(X_1…X_n)。
///   2. 互資訊張量（熵的 Möbius 反演）I_S = Σ_{∅≠T⊆S} (−1)^{|S|−|T|} H(T)：
///      恆等式 H(S) = Σ_{T⊆S} I_T，以及 TC = −Σ_{|S|≥2} I_S。
///   3. 三變數交互資訊 II = I(X;Y) − I(X;Y|Z) 與共資訊 C₃ = Σ_{∅≠S} (−1)^{|S|+1} H(S)。
///   4. 獨立性：TC = 0 ⟺ 分佈為乘積（對 2×2 分佈在 1/16 網格上窮舉驗證）。
///   5. 資訊瓶頸自洽方程 p(t|x) ∝ p(t) exp(−β D_KL[p(y|x)‖p(y|t)]) 的定點迭代與殘差。
///   6. 多模態資訊瓶頸（兩個來源 X₁, X₂ → T）之自洽方程與單峰 IB 的一致性。

// ───────────────────────── 熵與互資訊 ─────────────────────────

///|
/// 熵（位元）：H(p) = −Σ p log₂ p。
pub fn b8i_h(p : Array[Double]) -> Double {
  let mut h = 0.0
  for v in p {
    if v > 0.0 {
      h = h - v * @math.log2(v)
    }
  }
  h
}

///|
/// 邊際分佈：對聯合分佈 P[i][j] 求第一變數邊際。
pub fn b8i_marg0(p : Array[Array[Double]]) -> Array[Double] {
  let out : Array[Double] = []
  for i in 0..<p.length() {
    let mut s = 0.0
    for j in 0..<p[i].length() {
      s = s + p[i][j]
    }
    out.push(s)
  }
  out
}

///|
/// 邊際分佈：對聯合分佈 P[i][j] 求第二變數邊際。
pub fn b8i_marg1(p : Array[Array[Double]]) -> Array[Double] {
  let nj = if p.length() > 0 { p[0].length() } else { 0 }
  let out : Array[Double] = []
  for j in 0..<nj {
    let mut s = 0.0
    for i in 0..<p.length() {
      s = s + p[i][j]
    }
    out.push(s)
  }
  out
}

///|
/// 聯合熵 H(XY)。
pub fn b8i_h_joint(p : Array[Array[Double]]) -> Double {
  let flat : Array[Double] = []
  for row in p {
    for v in row {
      flat.push(v)
    }
  }
  b8i_h(flat)
}

///|
/// 互資訊 I(X;Y)。
pub fn b8i_mi(p : Array[Array[Double]]) -> Double {
  b8i_h(b8i_marg0(p)) + b8i_h(b8i_marg1(p)) - b8i_h_joint(p)
}

///|
/// 三變數聯合分佈的扁平化（索引 i*nj*nk + j*nk + k）。
fn b8i_flat3(p : Array[Array[Array[Double]]]) -> Array[Double] {
  let out : Array[Double] = []
  for a in p {
    for b in a {
      for v in b {
        out.push(v)
      }
    }
  }
  out
}

///|
/// 三變數的邊際熵 H(X_i)。
pub fn b8i_marg3_h(p : Array[Array[Array[Double]]], which : Int32) -> Double {
  let ni = p.length()
  let nj = if ni > 0 { p[0].length() } else { 0 }
  let nk = if nj > 0 { p[0][0].length() } else { 0 }
  let marg : Array[Double] = []
  if which == 0 {
    for i in 0..<ni {
      let mut s = 0.0
      for j in 0..<nj {
        for k in 0..<nk {
          s = s + p[i][j][k]
        }
      }
      marg.push(s)
    }
  } else if which == 1 {
    for j in 0..<nj {
      let mut s = 0.0
      for i in 0..<ni {
        for k in 0..<nk {
          s = s + p[i][j][k]
        }
      }
      marg.push(s)
    }
  } else {
    for k in 0..<nk {
      let mut s = 0.0
      for i in 0..<ni {
        for j in 0..<nj {
          s = s + p[i][j][k]
        }
      }
      marg.push(s)
    }
  }
  b8i_h(marg)
}

///|
/// 三變數聯合熵 H(XYZ)。
pub fn b8i_h3(p : Array[Array[Array[Double]]]) -> Double {
  b8i_h(b8i_flat3(p))
}

///|
/// 總相關性（multi-information）TC = Σ_i H(X_i) − H(X_1…X_n)。
pub fn b8i_tc3(p : Array[Array[Array[Double]]]) -> Double {
  b8i_marg3_h(p, 0) + b8i_marg3_h(p, 1) + b8i_marg3_h(p, 2) - b8i_h3(p)
}

///|
/// 兩變數的總相關性 TC = H(X) + H(Y) − H(XY) = I(X;Y)。
pub fn b8i_tc2(p : Array[Array[Double]]) -> Double {
  b8i_mi(p)
}

///|
/// 由三變數聯合分佈得到 (X,Y) 的邊際。
pub fn b8i_marg_xy(p : Array[Array[Array[Double]]]) -> Array[Array[Double]] {
  let ni = p.length()
  let nj = if ni > 0 { p[0].length() } else { 0 }
  let nk = if nj > 0 { p[0][0].length() } else { 0 }
  let out : Array[Array[Double]] = []
  for i in 0..<ni {
    let row : Array[Double] = []
    for j in 0..<nj {
      let mut s = 0.0
      for k in 0..<nk {
        s = s + p[i][j][k]
      }
      row.push(s)
    }
    out.push(row)
  }
  out
}

///|
/// 由三變數聯合分佈得到 (X,Y)|Z 的平均互資訊 I(X;Y|Z)。
pub fn b8i_mi_cond_z(p : Array[Array[Array[Double]]]) -> Double {
  let ni = p.length()
  let nj = if ni > 0 { p[0].length() } else { 0 }
  let nk = if nj > 0 { p[0][0].length() } else { 0 }
  let mut acc = 0.0
  for k in 0..<nk {
    let mut pz = 0.0
    for i in 0..<ni {
      for j in 0..<nj {
        pz = pz + p[i][j][k]
      }
    }
    if pz > 0.0 {
      let mut mi = 0.0
      for i in 0..<ni {
        for j in 0..<nj {
          let pxyz = p[i][j][k]
          if pxyz > 0.0 {
            let mut pxz = 0.0
            for j2 in 0..<nj {
              pxz = pxz + p[i][j2][k]
            }
            let mut pyz = 0.0
            for i2 in 0..<ni {
              pyz = pyz + p[i2][j][k]
            }
            mi = mi + pxyz * @math.log2(pxyz * pz / (pxz * pyz))
          }
        }
      }
      acc = acc + mi
    }
  }
  acc
}

///|
/// 三變數交互資訊 II = I(X;Y) − I(X;Y|Z)。
pub fn b8i_interaction(p : Array[Array[Array[Double]]]) -> Double {
  b8i_mi(b8i_marg_xy(p)) - b8i_mi_cond_z(p)
}

///|
/// 共資訊 C₃ = Σ_{∅≠S} (−1)^{|S|+1} H(S)。
pub fn b8i_coinfo3(p : Array[Array[Array[Double]]]) -> Double {
  let h1 = b8i_marg3_h(p, 0)
  let h2 = b8i_marg3_h(p, 1)
  let h3 = b8i_marg3_h(p, 2)
  let h12 = b8i_h_joint(b8i_marg_xy(p))
  // H(XZ), H(YZ)
  let ni = p.length()
  let nj = if ni > 0 { p[0].length() } else { 0 }
  let nk = if nj > 0 { p[0][0].length() } else { 0 }
  let xz : Array[Array[Double]] = []
  for i in 0..<ni {
    let row : Array[Double] = []
    for k in 0..<nk {
      let mut s = 0.0
      for j in 0..<nj {
        s = s + p[i][j][k]
      }
      row.push(s)
    }
    xz.push(row)
  }
  let yz : Array[Array[Double]] = []
  for j in 0..<nj {
    let row : Array[Double] = []
    for k in 0..<nk {
      let mut s = 0.0
      for i in 0..<ni {
        s = s + p[i][j][k]
      }
      row.push(s)
    }
    yz.push(row)
  }
  let h13 = b8i_h_joint(xz)
  let h23 = b8i_h_joint(yz)
  let h123 = b8i_h3(p)
  h1 + h2 + h3 - h12 - h13 - h23 + h123
}

///|
/// 互資訊張量：對 n = 3 的聯合分佈，回傳 7 個子集的 I_S（以位元遮罩 1…7 索引，索引 0 不用）。
pub fn b8i_tensor3(p : Array[Array[Array[Double]]]) -> Array[Double] {
  let hsub : Array[Double] = []
  for _ in 0..<8 {
    hsub.push(0.0)
  }
  let hx = b8i_marg3_h(p, 0)
  let hy = b8i_marg3_h(p, 1)
  let hz = b8i_marg3_h(p, 2)
  let hxy = b8i_h_joint(b8i_marg_xy(p))
  let ni = p.length()
  let nj = if ni > 0 { p[0].length() } else { 0 }
  let nk = if nj > 0 { p[0][0].length() } else { 0 }
  let xz : Array[Array[Double]] = []
  for i in 0..<ni {
    let row : Array[Double] = []
    for k in 0..<nk {
      let mut s = 0.0
      for j in 0..<nj {
        s = s + p[i][j][k]
      }
      row.push(s)
    }
    xz.push(row)
  }
  let yz : Array[Array[Double]] = []
  for j in 0..<nj {
    let row : Array[Double] = []
    for k in 0..<nk {
      let mut s = 0.0
      for i in 0..<ni {
        s = s + p[i][j][k]
      }
      row.push(s)
    }
    yz.push(row)
  }
  hsub[1] = hx
  hsub[2] = hy
  hsub[4] = hz
  hsub[3] = hxy
  hsub[5] = b8i_h_joint(xz)
  hsub[6] = b8i_h_joint(yz)
  hsub[7] = b8i_h3(p)
  // Möbius 反演：I_S = Σ_{∅≠T⊆S} (−1)^{|S|−|T|} H(T)
  let out : Array[Double] = []
  for _ in 0..<8 {
    out.push(0.0)
  }
  for s in 1..<8 {
    let card = b8i_popcount3(s)
    let mut acc = 0.0
    for t in 1..<8 {
      if (t & s) == t {
        let sign = if (card - b8i_popcount3(t)) % 2 == 0 { 1.0 } else { -1.0 }
        acc = acc + sign * hsub[t]
      }
    }
    out[s] = acc
  }
  out
}

///|
/// 位元數。
fn b8i_popcount3(x : Int32) -> Int32 {
  let mut c = 0
  for i in 0..<8 {
    if ((x >> i) & 1) == 1 {
      c = c + 1
    }
  }
  c
}

///|
/// 在 1/16 網格上窮舉所有 2×2 分佈，統計「TC = 0」與「乘積分佈」兩條件等價的次數。
pub fn b8i_independence_scan() -> (Int32, Int32, Int32, Int32) {
  let mut total = 0
  let mut tc_zero = 0
  let mut product = 0
  let mut mism = 0
  for a in 0..<=16 {
    for b in 0..<=(16 - a) {
      for c in 0..<=(16 - a - b) {
        let d = 16 - a - b - c
        let p : Array[Array[Double]] = [
          [a.to_double() / 16.0, b.to_double() / 16.0],
          [c.to_double() / 16.0, d.to_double() / 16.0],
        ]
        total = total + 1
        let tc = b8i_mi(p)
        let pxy = p[0][0] * p[1][1] - p[0][1] * p[1][0]
        let tcz = tc.abs() < 1.0e-12
        let prod = pxy.abs() < 1.0e-12
        if tcz {
          tc_zero = tc_zero + 1
        }
        if prod {
          product = product + 1
        }
        if tcz != prod {
          mism = mism + 1
        }
      }
    }
  }
  let _ = mism
  (total, tc_zero, product, mism)
}

// ───────────────────────── 資訊瓶頸自洽方程 ─────────────────────────

///|
/// 單峰 IB：對聯合分佈 p(x,y)（行列皆已歸一）與 |T| = nt、參數 β 做定點迭代。
/// 回傳 (I(X;T), I(T;Y), 殘差, 迭代步數)。
pub fn b8i_ib(
  pxy : Array[Array[Double]],
  nt : Int32,
  beta : Double,
  iters : Int32,
) -> (Double, Double, Double, Int32) {
  let nx = pxy.length()
  let ny = if nx > 0 { pxy[0].length() } else { 0 }
  let px : Array[Double] = []
  for i in 0..<nx {
    let mut s = 0.0
    for j in 0..<ny {
      s = s + pxy[i][j]
    }
    px.push(s)
  }
  // 初始：非對稱（避免停在「T 與一切獨立」的平凡定點）
  let pt_x : Array[Array[Double]] = []
  for x in 0..<nx {
    let row : Array[Double] = []
    for t in 0..<nt {
      let v = if (x + t) % nt == 0 { 0.8 } else { 0.2 }
      row.push(v)
    }
    let mut s = 0.0
    for v in row {
      s = s + v
    }
    let nrow : Array[Double] = []
    for v in row {
      nrow.push(v / s)
    }
    pt_x.push(nrow)
  }
  let mut resid = 1.0
  let mut used = 0
  for _ in 0..<iters {
    used = used + 1
    // p(t)
    let pt : Array[Double] = []
    for t in 0..<nt {
      let mut s = 0.0
      for x in 0..<nx {
        s = s + px[x] * pt_x[x][t]
      }
      pt.push(s)
    }
    // p(y|t)
    let py_t : Array[Array[Double]] = []
    for t in 0..<nt {
      let row : Array[Double] = []
      for y in 0..<ny {
        let mut num = 0.0
        for x in 0..<nx {
          num = num + pxy[x][y] * pt_x[x][t]
        }
        row.push(if pt[t] > 0.0 { num / pt[t] } else { 0.0 })
      }
      py_t.push(row)
    }
    // 更新 p(t|x)
    resid = 0.0
    for x in 0..<nx {
      let px_y : Array[Double] = []
      for y in 0..<ny {
        px_y.push(if px[x] > 0.0 { pxy[x][y] / px[x] } else { 0.0 })
      }
      let w : Array[Double] = []
      for t in 0..<nt {
        // D_KL(p(y|x) || p(y|t))
        let mut dkl = 0.0
        for y in 0..<ny {
          if px_y[y] > 0.0 && py_t[t][y] > 0.0 {
            dkl = dkl + px_y[y] * @math.log2(px_y[y] / py_t[t][y])
          }
        }
        w.push(pt[t] * @math.exp(-beta * dkl))
      }
      let mut z = 0.0
      for v in w {
        z = z + v
      }
      for t in 0..<nt {
        let nv = if z > 0.0 { w[t] / z } else { 0.0 }
        let diff = (nv - pt_x[x][t]).abs()
        if diff > resid {
          resid = diff
        }
        pt_x[x][t] = nv
      }
    }
    if resid < 1.0e-13 {
      break
    }
  }
  // I(X;T) 與 I(T;Y)
  let pxt : Array[Array[Double]] = []
  for x in 0..<nx {
    let row : Array[Double] = []
    for t in 0..<nt {
      row.push(px[x] * pt_x[x][t])
    }
    pxt.push(row)
  }
  let ixt = b8i_mi(pxt)
  // p(t,y) = Σ_x p(x,y) p(t|x)
  let pty : Array[Array[Double]] = []
  for t in 0..<nt {
    let row : Array[Double] = []
    for y in 0..<ny {
      let mut s = 0.0
      for x in 0..<nx {
        s = s + pxy[x][y] * pt_x[x][t]
      }
      row.push(s)
    }
    pty.push(row)
  }
  let ity = b8i_mi(pty)
  (ixt, ity, resid, used)
}

///|
/// 多模態 IB：來源 X₁, X₂（聯合分佈 p[x1][x2][y]），瓶頸 T，參數 β。
/// 自洽方程 p(t|x₁,x₂) ∝ p(t) exp(−β D_KL[p(y|x₁,x₂)‖p(y|t)])。
/// 回傳 (I(X₁X₂;T), I(T;Y), 殘差, 迭代步數)。
pub fn b8i_ib_multi(
  p : Array[Array[Array[Double]]],
  nt : Int32,
  beta : Double,
  iters : Int32,
) -> (Double, Double, Double, Int32) {
  // 攤平 (x1,x2) 為單一索引
  let n1 = p.length()
  let n2 = if n1 > 0 { p[0].length() } else { 0 }
  let ny = if n2 > 0 { p[0][0].length() } else { 0 }
  let nx = n1 * n2
  let pxy : Array[Array[Double]] = []
  for i in 0..<nx {
    let row : Array[Double] = []
    for y in 0..<ny {
      row.push(p[i / n2][i % n2][y])
    }
    pxy.push(row)
  }
  b8i_ib(pxy, nt, beta, iters)
}

///|
/// IB 曲線：對 β 網格回傳 (β, I(X;T), I(T;Y)) 陣列。
pub fn b8i_ib_curve(
  pxy : Array[Array[Double]],
  nt : Int32,
  betas : Array[Double],
) -> Array[Double] {
  // 每三個一組：[β, I(X;T), I(T;Y)]
  let out : Array[Double] = []
  for b in betas {
    let (ixt, ity, _, _) = b8i_ib(pxy, nt, b, 400)
    out.push(b)
    out.push(ixt)
    out.push(ity)
  }
  out
}
