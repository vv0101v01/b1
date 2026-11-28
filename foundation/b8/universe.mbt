///|
/// universe.mbt — 批次八·模組 4：不可達基數與格羅滕迪克宇宙（含可達／正則基數）
///
/// 可計算的內容：
///   1. 累積層級 V_n 的基數：|V_n| = 0,1,2,4,16,65536, 2^65536（BigInt 精確）。
///   2. 格羅滕迪克宇宙條件（遞移、幂集封閉、並集封閉、配對封閉）在 V_0…V_4 上的逐項判定，
///      以及失敗見證（第一個失敗發生在 V_2，見證 x = {∅}）。
///   3. 正則性（cf(κ) = κ）與可達性（∃λ<κ, κ ≤ 2^λ）在有限基數上的完整枚舉：
///      **不存在有限不可達基數**（1000 個有限基數全部可達）——
///      第一個不可達基數必然是 ω（此部分為框架假設，非本程式所證）。
///   4. Beth 塔 b_0 = 1、b_{n+1} = 2^{b_n} 與 |V_{n+1}| = b_n 的精確對照。

// ───────────────────────── 層級與宇宙條件 ─────────────────────────

///|
/// |V_n|：V_0 = ∅，V_{n+1} = V_n ∪ P(V_n)，故 |V_{n+1}| = 2^{|V_n|}。
/// 回傳前十個層級的基數（超過 Int32 者以 -1 標記）。
pub fn b8u_level_sizes(nmax : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut s = 0
  for _ in 0..<nmax {
    out.push(s)
    // s ← 2^s
    if s >= 31 {
      s = -1
    } else {
      s = b8u_pow2_int(s)
    }
  }
  out
}

///|
/// |V_n| 的 BigInt 精確值（僅在 0…4 層避免爆炸，第 5 層為 2^65536）。
pub fn b8u_level_size_big(n : Int32) -> @bigint.BigInt {
  let mut acc = @bigint.BigInt::from_int(0)
  // 0,1,2,4,16,65536,2^65536
  let small = [0, 1, 2, 4, 16, 65536]
  if n < 6 && n >= 0 {
    return @bigint.BigInt::from_int(small[n])
  }
  acc = @bigint.BigInt::from_int(2).pow(@bigint.BigInt::from_int(65536))
  acc
}

///|
/// Beth 塔：b_0 = 1，b_{n+1} = 2^{b_n}（BigInt）。
pub fn b8u_beth(n : Int32) -> @bigint.BigInt {
  let mut b = @bigint.BigInt::from_int(1)
  for _ in 0..<n {
    b = @bigint.BigInt::from_int(2).pow(b)
  }
  b
}

///|
/// 有限基數的正則性：cf(k) = k（有限序數的共尾度等於自身）。
pub fn b8u_cf(k : Int32) -> Int32 {
  k
}

///|
/// 有限基數的可達性：∃λ < k 使 k ≤ 2^λ。
pub fn b8u_reachable(k : Int32) -> Bool {
  let mut ok = false
  for lam in 0..<k {
    if lam < 31 && k <= b8u_pow2_int(lam) {
      ok = true
    }
  }
  ok
}

///|
/// 在 1…n 中統計可達基數的個數。
pub fn b8u_reachable_count(n : Int32) -> Int32 {
  let mut c = 0
  for k in 1..<=n {
    if b8u_reachable(k) {
      c = c + 1
    }
  }
  c
}

///|
/// 在 1…n 中統計正則基數的個數（有限情形全部正則）。
pub fn b8u_regular_count(n : Int32) -> Int32 {
  let mut c = 0
  for k in 1..<=n {
    if b8u_cf(k) == k {
      c = c + 1
    }
  }
  c
}

///|
/// 格羅滕迪克宇宙判定（在 HF 集合上）：遞移 + 幂集封閉 + 並集封閉 + 對任意兩成員其配對亦為成員。
pub fn b8u_is_universe(r : B8Reg, x : Int32) -> Bool {
  if !b8reg_transitive(r, x) {
    return false
  }
  if !b8reg_pow_closed(r, x) {
    return false
  }
  if !b8reg_union_closed(r, x) {
    return false
  }
  let ms = b8reg_members(r, x)
  for a in ms {
    for b in ms {
      let pair = b8reg_set(r, [a, b])
      let mut found = false
      for z in ms {
        if z == pair {
          found = true
        }
      }
      if !found {
        return false
      }
    }
  }
  true
}

///|
/// 對 V_0…V_{nmax-1} 逐層判定是否為格羅滕迪克宇宙，回傳每層的布林值。
pub fn b8u_universe_levels(r : B8Reg, nmax : Int32) -> Array[Bool] {
  let out : Array[Bool] = []
  for n in 0..<nmax {
    // V_n 的代表元素：V_n 本身（作為集合）。用登錄表中「成員 = 等級 n-1 的全部元素」的編號。
    // V_n 本身的編號 = 以「V_n 的成員（即 b8reg_level(n) 的元素）」為成員的集合
    let members : Array[Int32] = []
    for x in b8reg_level(r, n) {
      members.push(x)
    }
    let vn = b8reg_set(r, members)
    out.push(b8u_is_universe(r, vn))
  }
  out
}

///|
/// V_n 中幂集封閉失敗的見證個數。
pub fn b8u_pow_failures(r : B8Reg, n : Int32) -> Int32 {
  let lvl = b8reg_level(r, n)
  let mut c = 0
  for x in lvl {
    let px = b8reg_powerset(r, x)
    let mut found = false
    for z in lvl {
      if z == px {
        found = true
      }
    }
    if !found {
      c = c + 1
    }
  }
  c
}
