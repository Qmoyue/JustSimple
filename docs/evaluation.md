# Gleipner 评测

固定样本含 123 个正例和 47 个负例，每个用例计一次。[样本版本 6cad4b0](https://github.com/software-engineering-and-security/Gleipner/tree/6cad4b07cf3a0f54fa2b149f5df9febccd02dcff)

| 指标 | 结果 |
| --- | ---: |
| TP / FP / FN / TN | 98 / 25 / 25 / 10 |
| 未决负例 | 12 |
| 查准率 | 79.67% |
| 召回率 | 79.67% |
| 误报率（已判定负例） | 71.43% |
| 准确率（已判定用例） | 68.35% |

分析截断且未报警的负例单列为未决。内置知识与评测样本同源。
