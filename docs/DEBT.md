# 除錯、去重、減債（批次十五收尾）

> 全部數字由 `cmd/tools` 產生，可重跑：
> `moon run cmd/tools --target native -- stats|audit|dups|deps --check`
> 快照：`docs/reports/DEBT_report.txt`。

## 一、把 Python 全部換成 MoonBit（零 Python 倉庫）

原本兩支腳本都靠「跑 `moon check`、用正則解析它的**人類可讀診斷文字**、再改檔案」：

| 舊 | 新 | 為何非換不可 |
|---|---|---|
| `tools/regen_deps.py`（235 行） | `cmd/tools/{deps,scan}.mbt` | 把編譯器輸出當 API，訊息一改就壞；且要 subprocess |
| `tools/qualify_test_uses.py`（110 行） | `cmd/tools/qualify.mbt` | 同上，且「改寫後重跑 check 驗證、失敗就還原」的迴圈極慢 |

新的 `cmd/tools` 是純 MoonBit 可執行程式，**自己做詞法分析**（`scan.mbt`：行註解、字串、
字串插值 `\{…}`、字元字面量、test 區塊），因此不需要 subprocess，也不需要外部程式。
`fs`／`args` 來自 `moonbitlang/x` 與 `moonbitlang/core/env`（`moon.mod` 已宣告）。

子命令：`deps`、`qualify`（都可加 `--check`）、`audit`、`dups`、`stats`、`why <套件>`。

兩個設計約束（讓它比舊腳本更可靠）：

1. **層級即契約**：`pkg_rank()` 明列 core(0) → common(1) → b1…b8(2–9) → b9…b15(10–15)
   → b12(16) → axioms(17) → reports(18) → cmd/main(19)。只允許「高 rank 指向低 rank」，
   所以 import 圖**不可能出現環**。舊腳本偶爾會寫出 `b3 → b6` 這種假弧，直接讓整個
   模組無法求解；現在這類弧在生成階段就被丟棄。
2. **語義比較**：`--check` 比的是「alias＋名稱」集合與「路徑＋別名」集合，不是文字。
   因此 `moon fmt` 想怎麼斷行都不會造成假漂移（舊腳本一定會和 fmt 打架）。

CI 現在會跑 `deps --check` 與 `qualify --check`，管路一旦漂移就紅燈。

## 二、清死碼（29 個函式）

`cmd/tools audit` 的定義是「宣告後**全倉零引用**」（入口 `main` 除外）。清除後重掃，
會暴露「只被死者引用」的第二層，共三輪收斂：

| 輪 | 刪除 |
|---|---|
| 1（15 個） | `b14_bool4`、`b14_cx_add`、`b14_cx_hom_total`、`b14_cx_shift`、`b14_f2_ker_dim`、`b14_i_star`、`b14_interior`、`b14_is_spectral`、`b14_j_upper`、`b14_m_circle_opens`、`b14_m_diamond`、`b14_m_disc_opens`、`b14_m_v`、`b14_strat_dual`、`b9_incl` |
| 2（5 個） | `b14_cx_dual`、`b14_cx_pad`、`b14_f2_diag`、`b14_m_disc`、`b9_top_poset` |
| 3（1 個） | `b14_chain_rev` |

另外刪掉我自己在批次十五留下的 `b15` 探針檔與 `b14_cx_shift` 的殘留引用
（`reports/report14.mbt` 的說明文字改成不指名函式）。

現況：**死碼 0**。

## 三、去重（4 份副本 → 1 份）

`cmd/tools dups` 把函式體正規化成 token 串（數值保留原文、字串保留內容、識別字原樣），
長度 ≥ 120 才比。首輪抓到 5 組，其中 3 組是**假陽性**（常數或字串不同），修好正規化後剩 2 組；
真重複只有一組 —— 陣列逐元素相等：

```
common/shared.mbt      : b_sh_arr_eq     (泛型 [T : Eq])
core/godel.mbt         : go_arr_eq       (Int32 版)
foundation/b12/kpm.mbt : b12_sigma_same  (Int32 版)
topos/b15/g13.mbt      : b15_arr_eq_i32  (Int32 版)
```

處理：把 `core.go_arr_eq` 升為泛型 `pub fn[T : Eq]`，其餘三處改成一行委派：

```moonbit
pub fn b_sh_arr_eq(a, b) { @core.go_arr_eq(a, b) }
```

`core` 是最底層，泛型實作放在那裡才能被所有套件共用。現況：**逐字重複 0 組**。

## 四、除錯

1. **`moon.pkg` 全數重算**：改用上述層級契約後，`zz_deps.mbt` 與 `moon.pkg` 由靜態分析
   決定，`deps --check` 回報 0 漂移；`moon check --deny-warn` 乾淨。
2. **`moonbitlang/x@0.5.9` 成為唯一外部依賴**（只用 `fs` 與 `env`），`.mooncakes/` 已加入
   `.gitignore`。
3. 詞法器修掉的三類地雷（每一類都曾讓分析結果錯得不明顯）：
   - 空白被當成 token（`fn` 後面接到的不是函式名而是 `Sym(' ')`）；
   - 字串插值 `"\{fmt6(x)}"` 裡的 `fmt6` 完全看不到，導致被判定為死碼；
   - 數字被正規化成同一個 token，讓「常數不同」的函式誤判為重複。
4. `pub fn[T : Eq] f` 這種**泛型宣告**一開始沒被解析（`[` 卡在 `fn` 與名字之間），
   導致 `b_sh_arr_eq` 之類的函式在別的套件眼裡「不存在」。

## 五、驗收

| 檢查 | 結果 |
|---|---|
| `moon fmt --check` | 通過 |
| `moon check --deny-warn` | 0 error、0 warning |
| `moon test` | **236 / 236** |
| `moon run cmd/main` | 298 行 `[PASS]`、0 行 `[FAIL]` |
| `deps --check` / `qualify --check` | 0 漂移 |
| `audit` | 死碼 0 |
| `dups` | 重複 0 |
