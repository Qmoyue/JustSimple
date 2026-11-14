# Gleipner 评测

固定样本含 123 个正例和 47 个负例，每个用例计一次，使用默认预算和内置知识。[样本版本 6cad4b0](https://github.com/software-engineering-and-security/Gleipner/tree/6cad4b07cf3a0f54fa2b149f5df9febccd02dcff)

| 指标 | 结果 |
| --- | ---: |
| TP / FP / FN / TN | 98 / 17 / 25 / 13 |
| 未决负例 | 17 |
| 查准率 | 85.22% |
| 召回率 | 79.67% |
| 误报率（已判定负例） | 56.67% |
| 准确率（已判定用例） | 72.55% |

30 类中 17 类完成、13 类截断。截断且未报警的负例列为未决；结果衡量用例级候选报警。
