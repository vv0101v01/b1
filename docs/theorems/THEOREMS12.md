# 批次十二：CZFM 不可達層級、哥德爾殘餘、馬洛／KPM 與全域公理

> 對應程式：`foundation/b12/czfm.mbt`、`foundation/b12/godel2.mbt`、`foundation/b12/kpm.mbt`、
> `foundation/b12/lang12.mbt`、`axioms/axioms.mbt`、`core/godel.mbt`、
> `reports/report12.mbt`、`reports/batch12_wbtest.mbt`。
> 報告輸出：`moon run cmd/main` 的第十二段（`PASS = 30，FAIL = 0`）。

## 本批次的態度：公理不被「宣稱」，只被「找不到反例」

使用者要求「新增全域公理：邏輯鏈拓撲斯、馬洛、朗蘭茲自洽約束完備且圖靈-約旦完備及萬有約束可達，
受哥德爾第一及第二定理約束，**永恆無法被找到的那塊正是系統具備自洽、圖靈及萬有的證明**」。

這正是本批次實作的骨架，但把它**降為可計算**：

1. 每條全域公理都給出**有限模型上的可反駁檢核**（`b12_lct_holds`、`b12_lc_complete`、
   `b12_three_completeness`）。找不到反例 ⇒ `[PASS]`；找到反例 ⇒ `[FAIL]`，報告立刻變紅。
2. 「永恆無法被找到的那塊」被**顯式標記**，不是藏起來：
   `b12_axiom_audit()` 回傳 `(相容, 已檢核 2, 永不可得 1)`；
   `b12_residual_gap()` 給出殘餘描述；`b12_g2_all_depths(n)` 對所有深度回傳 `false`
   （Con(A) 在 N 步以內搜不到證明）；`b12_mahlo_gap()` 指出有限層級不含馬洛基數。
3. 因此報告裡會同時出現兩種句子：「此公理在此模型上成立」與「此處永遠得不到」。
   後者不是失敗，而是**誠實性條款**——它本身就是「系統具備自洽 + 圖靈-約旦 + 萬有可達」的
   哥德爾式代價。

## 全域公理（`axioms/axioms.mbt`）

| 代號 | 名稱 | 狀態 | 可計算檢核 |
|---|---|---|---|
| GA-1 | 邏輯鏈拓撲斯（LCT） | 有限模型已檢核 | `b12_lct_holds(sizes, bound)`：鏈長有限、每層黏合深度 ≤ 界 |
| GA-2 | 馬洛公理（Mahlo） | **永不可得（哥德爾殘餘）** | `b12_mahlo_finite(κ)` 對所有有限 κ 回傳 `false`；反思強度序 `b12_reflect_rank`／`b12_reflect_monotone` 可計算 |
| GA-3 | 朗蘭茲自洽約束完備（LC） | 有限模型已檢核 | `b12_lc_complete(galois, automorphic)`：兩側標籤逐一配對，無未配對元素 |

三公理聯合自洽：`b12_joint_completeness` 在同一個有限模型上同時檢核 GA-1／GA-2 的可計算殘餘／GA-3，
回傳 `(三完備, [三個真值], 殘餘已標記)`。

## 定理（T411–T429）

| 編號 | 內容 | 程式 |
|---|---|---|
| T411 | CZFM 不可達層級：V_α 塔的基數／共尾度／正則性；**有限層級無不可達基數**（誠實見證） | `b12_czfm_levels`、`b12_inaccessible` |
| T412 | 存在性／反思雙重視角：由下往上的新增量與由上往下的反射比描述**同一個塔**（不變量殘差 = 0、反射比恆 ≥ 2） | `b12_bottom_up`、`b12_top_down`、`b12_dual_ok` |
| T413 | 等一致性轉譯網路：4 系統的轉譯以置換矩陣顯式給出；非雙射的「偽轉譯」被拒；網路連通 | `b12_is_perm_matrix`、`b12_translation_map`、`b12_network_complete` |
| T414 | 顯式表示：3 循環 σ = [1,2,0] 的逆 σ⁻¹ = [2,0,1]，σ∘σ⁻¹ = id | `b12_inv_perm` |
| T415 | 哥德爾編碼：⌜S0=S0⌝ = 20212500，反解回 [2,1,5,2,1]，重編碼得同一數 | `go_godel_of_names`、`go_ungodel` |
| T416 | (T-IN) 內定理性：單步證明檢查器接受真公理、拒絕冒名式子 ⇒ 證明可判定 | `b12_proof_check`、`b12_is_axiom` |
| T417 | (L-IN) 內可證性：深度 d 的截斷內 φ 有證明、¬φ 無證明 ⇒ □ 可列舉但截斷外不可得 | `b12_provable`、`b12_derive_candidates` |
| T418 | 函數提取矛盾：對角化在有限域上**不**產生矛盾項；停機問題仍不可判定、界 = −1 ⇒ 提取普遍可行會導致矛盾 | `b12_extraction_contradiction`、`b12_halting_decidable_by_extraction` |
| T419 | KPM 標記：有限層級無容許序數；標記 (α, kp, mahlo) 良形成要求 kp ≤ mahlo | `b12_admissible`、`b12_kpm_mark` |
| T420 | 弱馬洛記號：ψ(2,5) = 21；6 個記號互不碰撞（單射），碰撞 (1,0)/(0,8) 被偵測 | `b12_weak_mahlo_notation`、`b12_notation_injective` |
| T421 | 多層塌縮函數：ψ_2 每步 +2^level 嚴格遞增（高層不收斂）；ψ_0 為共尾度、恆等（3 個不動點） | `b12_collapse`、`b12_collapse_fixpoints` |
| T422 | n-馬洛／ω-馬洛：強度階梯嚴格遞增；階梯 [0,2,1] 因不單調被拒 | `b12_n_mahlo`、`b12_omega_mahlo` |
| T423 | Σ_n-正確：模型與真實層級前 3 級真值表全等；翻轉一項即失配 ⇒ 可反駁 | `b12_sigma_n_correct`、`b12_sigma_agree` |
| T424 | 列維綱領 Λ：Σ₁ 見證在遞移模型中全保留（絕對）；非遞移模型遺失見證 | `b12_levy_lambda` |
| T425 | Σ₁-可定義無界閉集（CU）：無界 + 極限封閉；閉包算子冪等 | `b12_club_set`、`b12_club_closure` |
| T426 | 朗蘭茲自洽約束：5 個 Satake 標籤兩側配對、對偶和恆為 p+1、互逆雙射；多一項即完備失敗 | `b12_lc_pair`、`b12_lc_complete`、`b12_lc_involution_ok` |
| T427 | 全域公理清單：3 條（已檢核 2、永不可得 1） | `b12_axioms`、`b12_axiom_audit` |
| T428 | 三公理聯合自洽（相容性見證） | `b12_joint_completeness` |
| T429 | 自洽・圖靈-約旦・萬有可達 三完備；殘餘缺口（G1/G2）已標記 | `b12_three_completeness`、`b12_g1_sentence`、`b12_g2_all_depths` |

## 衍生演算法（A65–A75）

| 編號 | 內容 | 程式 |
|---|---|---|
| A65 | 不可達／正則性檢定器（有限層級逐項判定） | `b12_regular_up_to`、`b12_inaccessible` |
| A66 | 哥德爾 β 函數編碼器（CRT；c 以 BigInt 承載，支援任意長度序列） | `go_beta_encode`、`go_beta_big`、`go_beta_val` |
| A67 | 配對／反配對引擎（Cantor） | `go_cantor_pair`、`go_cantor_unpair` |
| A68 | 證明候選生成器（公理 + MP 閉包） | `b12_derive_candidates` |
| A69 | 截斷可證性搜尋器 | `b12_provable` |
| A70 | KPM 標記比較器（字典序） | `b12_kpm_cmp` |
| A71 | 塌縮函數計算器（多層 ψ 迭代） | `b12_collapse` |
| A72 | 馬洛階梯生成器（n-馬洛 → ω-馬洛） | `b12_strength_ladder`、`b12_omega_mahlo` |
| A73 | Σ_n 真值表比對器（逐項 + 級內差異計數） | `b12_sigma_n_correct` |
| A74 | 列維絕對性檢查器（Σ₁ 見證保留） | `b12_levy_lambda` |
| A75 | CU 閉包算子（極限封閉迭代至不動點） | `b12_club_closure` |

## 名詞對照（使用者指定清單）

| 名詞 | 落點 |
|---|---|
| CZFM 不可達層級 | T411、`b12_czfm_levels` |
| 存在性與反思雙重視角 | T412、`b12_bottom_up`／`b12_top_down` |
| 等一致性轉譯網路 | T413、`b12_is_perm_matrix`／`b12_network_complete` |
| 顯式表示 | T413/T414、`b12_translation_map`／`b12_inv_perm` |
| (T-IN) 與 (L-IN) | T416／T417、`b12_proof_check`／`b12_provable` |
| $\mathrm{Ax\text{-}M_{ext}}$（外延性公理模式） | T413 的置換矩陣轉譯（結構保持 ⇒ 外延同一）＋ T415 的編碼互逆 |
| 聯集編碼 | T412／A67：Cantor 配對與 β 編碼把「聯集」壓成單一自然數 |
| 函數提取矛盾 | T418 |
| 弱馬洛記號 | T420、`b12_weak_mahlo_notation` |
| 相對化序數分析 | T419／T422：標記的字典序與強度階梯 |
| KPM 標記 | T419、`b12_kpm_mark`／`b12_kpm_cmp` |
| 多層塌縮函數 | T421、`b12_collapse` |
| n-馬洛、ω-馬洛 | T422 |
| Σ_n-正確 | T423 |
| 列維綱領 Λ | T424 |
| Σ₁-可定義無界閉集 | T425 |

## 誠實性聲明

- 有限模型上「找不到反例」**不等於**定理成立；本批次所有 `[PASS]` 都附帶模型大小與檢核方式。
- GA-2（馬洛）在有限域上**永不可得**，因此標為殘餘而非已證。
- G2 的 Con(A) 在所有有限深度搜尋失敗，這正是「不可由自身證明」的有限投影；
  全域自洽性只能作為公理引入，`b12_residual_gap()` 明文記載此事。
